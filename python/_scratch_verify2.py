import os
import tempfile
import math

from sympy import primerange
from sieve_sequence import per_sequence_frontier_chart as p1
from sieve_sequence import frontier_comparison_stages_chart as p2
from sieve_sequence import fixed_lineage_hazard_chart as p3

print("== p2 load_stages CSV fixture ==")
with tempfile.TemporaryDirectory() as td:
    dense = os.path.join(td, "dense.csv")
    sparse = os.path.join(td, "sparse.csv")
    with open(dense, "w") as f:
        f.write("p,G_local,destroyed\n7,100.0,28\n11,100.0,18\n17,50.0,0\n")
    with open(sparse, "w") as f:
        f.write("p,G_local,destroyed\n101,200.0,10\n")
    p2.DENSE_PATH = dense
    p2.SPARSE_PATH = sparse
    stages = p2.load_stages()
    print("stages:", stages)
    print("p keys:", [s[0] for s in stages])
    print("rate17 (zero destroyed):", stages[2][1], "expected 0.0")

print("== p3 load_rows + draw SVG ==")
with tempfile.TemporaryDirectory() as td:
    p3.OUT_DIR = td
    p3.DATA_DIR = td
    rows = "r,excess_hazard,c_eff\n3,0.5,0.25\n5,0.8,0.3\n7,1.2,0.4\n11,1.6,0.45\n13,2.0,0.5\n17,2.5,0.55\n19,3.0,0.6\n23,3.5,0.65\n"
    for Q in (17, 101):
        with open(os.path.join(td, f"fixed-lineage-hazard-Q{Q}.csv"), "w") as f:
            f.write(rows)
    Q_values = [17, 101]
    all_data = p3.load_rows(Q_values)
    print("loaded Q keys:", list(all_data.keys()))
    canvas = p3.draw(all_data, Q_values)
    svg = canvas.render()
    print("svg starts with <svg:", svg.startswith("<svg "))
    print("svg ends with </svg>:", svg.rstrip().endswith("</svg>"))
    print("svg length:", len(svg))