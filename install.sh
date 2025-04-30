if [ ! -f "sbt-stainless.zip" ]; then
  wget https://github.com/epfl-lara/stainless/releases/download/v0.9.8.9/sbt-stainless.zip
fi
rm -rf project
rm -rf stainless
unzip sbt-stainless.zip

VERSION="0.9.8.8"
BASE_URL="https://github.com/epfl-lara/stainless/releases/download/v$VERSION"
TARGET="stainless-dotty-standalone-$VERSION.zip"

# Detect platform
OS="$(uname -s)"
ARCH="$(uname -m)"

# Check if the file already exists
if [ -f "$TARGET" ]; then
   echo "$FILE already exists. Skipping download."
else
   # Determine the correct suffix
  case "$OS" in
      Linux)
          FILE="stainless-dotty-standalone-$VERSION-linux.zip"
          ;;
      Darwin)
          if [[ "$ARCH" == "arm64" ]]; then
              FILE="stainless-dotty-standalone-$VERSION-mac-arm64.zip"
          else
              echo "Unsupported Mac architecture: $ARCH"
              exit 1
          fi
          ;;
      MINGW*|MSYS*|CYGWIN*|Windows_NT)
          FILE="stainless-dotty-standalone-$VERSION-win.zip"
          ;;
      *)
          echo "Unsupported OS: $OS"
          exit 1
          ;;
  esac

  # Download the file
  echo "Downloading $FILE..."
  wget "$BASE_URL/$FILE" -O "$TARGET"
fi

rm -rf stainless-dotty-standalone-0.9.8.8
unzip "${TARGET}" -d stainless-dotty-standalone-0.9.8.8
rm -rf project/lib/stainess-library.jar
cp ./stainless-dotty-standalone-0.9.8.8/lib/stainless-library.jar project/lib/
