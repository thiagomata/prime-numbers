#!/usr/bin/env python3

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "src" / "main" / "scala"


def strip_comments(source: str) -> str:
    without_block_comments = re.sub(r"/\*.*?\*/", " ", source, flags=re.DOTALL)
    return "\n".join(re.sub(r"//.*$", "", line) for line in without_block_comments.splitlines())


def scope_root_from_arg(scope: str | None) -> Path:
    if not scope:
        return SOURCE_ROOT
    if re.fullmatch(r"\d+", scope):
        return SOURCE_ROOT / "v1" / f"chapter{scope}"
    return (ROOT / scope).resolve()


def display_path(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def resolve_reference(
    reference: str,
    current_package: str,
    objects_by_simple_name: dict[str, list[str]],
) -> list[str]:
    parts = reference.split(".")
    simple_name = parts[-1]
    candidates = objects_by_simple_name.get(simple_name, [])
    if not candidates:
        return []

    if len(parts) > 1:
        explicit_prefix = ".".join(parts[:-1])
        exact = [candidate for candidate in candidates if candidate == f"{explicit_prefix}.{simple_name}"]
        if exact:
            return exact

    same_package = [candidate for candidate in candidates if candidate == f"{current_package}.{simple_name}"]
    if same_package:
        return same_package

    return candidates if len(candidates) == 1 else []


def main() -> int:
    scope_root = scope_root_from_arg(sys.argv[1] if len(sys.argv) > 1 else None)
    if not scope_root.is_dir():
        print(f"Cycle check scope does not exist: {scope_root}", file=sys.stderr)
        return 2

    files = sorted(scope_root.glob("**/*.scala"))
    declarations: dict[str, dict[str, str | Path]] = {}
    objects_by_simple_name: dict[str, list[str]] = defaultdict(list)
    packages_by_file: dict[Path, str] = {}

    for file_path in files:
        source = strip_comments(file_path.read_text())
        package_match = re.search(r"^\s*package\s+([\w.]+)", source, flags=re.MULTILINE)
        package_name = package_match.group(1) if package_match else ""
        packages_by_file[file_path] = package_name

        for declaration in re.finditer(
            r"^\s*(?:object|class|case\s+class)\s+([A-Z]\w*)\b",
            source,
            flags=re.MULTILINE,
        ):
            simple_name = declaration.group(1)
            qualified_name = ".".join(part for part in [package_name, simple_name] if part)
            declarations[qualified_name] = {
                "file": file_path,
                "simple": simple_name,
                "package": package_name,
            }
            objects_by_simple_name[simple_name].append(qualified_name)

    graph: dict[str, set[str]] = defaultdict(set)

    for file_path in files:
        source = strip_comments(file_path.read_text())
        current_package = packages_by_file[file_path]
        sources = [name for name, data in declarations.items() if data["file"] == file_path]
        if not sources:
            continue

        for reference_match in re.finditer(r"\b((?:[a-z]\w*\.)*[A-Z]\w*)\s*\.", source):
            reference = reference_match.group(1)
            targets = resolve_reference(reference, current_package, objects_by_simple_name)
            for target in targets:
                for source_object in sources:
                    if source_object != target:
                        graph[source_object].add(target)

    visited: dict[str, str] = {}
    stack: list[str] = []
    cycles: set[str] = set()

    def visit(node: str) -> None:
        visited[node] = "visiting"
        stack.append(node)

        for target in sorted(graph[node]):
            if visited.get(target) == "visiting":
                index = stack.index(target)
                cycle = stack[index:] + [target]
                cycles.add(" -> ".join(cycle))
            elif target not in visited:
                visit(target)

        stack.pop()
        visited[node] = "visited"

    for node in sorted(declarations):
        if node not in visited:
            visit(node)

    if not cycles:
        print(f"No object/class reference cycles found in {display_path(scope_root)}.")
        return 0

    print(f"Object/class reference cycles found in {display_path(scope_root)}:")
    for cycle in sorted(cycles):
        print(f"- {cycle}")
    return 1


if __name__ == "__main__":
    sys.exit(main())
