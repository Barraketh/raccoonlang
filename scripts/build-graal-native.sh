#!/usr/bin/env bash

set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
MAIN_CLASS="${MAIN_CLASS:-com.raccoonlang.Main}"
OUTPUT_DIR="${OUTPUT_DIR:-$ROOT_DIR/target/graalvm}"
OUTPUT_NAME="${OUTPUT_NAME:-raccoon}"
SBT_BIN="${SBT_BIN:-sbt}"

find_native_image() {
  if command -v native-image >/dev/null 2>&1; then
    command -v native-image
    return 0
  fi

  if [[ -n "${JAVA_HOME:-}" && -x "${JAVA_HOME}/bin/native-image" ]]; then
    printf '%s\n' "${JAVA_HOME}/bin/native-image"
    return 0
  fi

  local candidates=(
    "/Library/Java/JavaVirtualMachines/graalvm-21.jdk/Contents/Home/bin/native-image"
    "/Library/Java/JavaVirtualMachines/graalvm-25.jdk/Contents/Home/bin/native-image"
  )
  local candidate
  for candidate in "${candidates[@]}"; do
    if [[ -x "$candidate" ]]; then
      printf '%s\n' "$candidate"
      return 0
    fi
  done

  return 1
}

ensure_native_image() {
  if find_native_image >/dev/null 2>&1; then
    find_native_image
    return 0
  fi

  if [[ "$(uname -s)" == "Darwin" ]]; then
    echo "native-image not found. Install GraalVM first, for example:" >&2
    echo "  brew install --cask graalvm-jdk@21" >&2
    echo "  sudo xattr -dr com.apple.quarantine /Library/Java/JavaVirtualMachines/graalvm-21.jdk" >&2
  else
    echo "native-image not found. Install GraalVM and ensure native-image is on PATH or JAVA_HOME/bin." >&2
  fi
  return 1
}

NATIVE_IMAGE_BIN="$(ensure_native_image)"
GRAAL_HOME="$(cd "$(dirname "$NATIVE_IMAGE_BIN")/.." && pwd)"

mkdir -p "$OUTPUT_DIR"

echo "Compiling JVM classes and writing GraalVM classpath..."
"$SBT_BIN" -batch -no-colors compile graalvmNativeImageClasspath

CLASSPATH_FILE="$ROOT_DIR/target/graalvm/classpath.txt"
if [[ ! -f "$CLASSPATH_FILE" ]]; then
  echo "Missing classpath file: $CLASSPATH_FILE" >&2
  exit 1
fi

CLASSPATH="$(tr -d '\n' < "$CLASSPATH_FILE")"
OUTPUT_PATH="$OUTPUT_DIR/$OUTPUT_NAME"

echo "Building native image at $OUTPUT_PATH"
JAVA_HOME="$GRAAL_HOME" "$NATIVE_IMAGE_BIN" \
  --no-fallback \
  -o "$OUTPUT_PATH" \
  -cp "$CLASSPATH" \
  "$@" \
  "$MAIN_CLASS"

echo "Built $OUTPUT_PATH"
