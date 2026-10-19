#!/usr/bin/env bash
# Rename this template project from "ProjectTemplate" to a name of your choice.
#
# Usage: ./customize.sh MyProject
#
# The name must be a valid Lean module name: a letter followed by letters,
# digits or underscores (UpperCamelCase is conventional, e.g. `FermatLastTheorem`).

set -euo pipefail

OLD="ProjectTemplate"
NEW="${1:-}"

if [[ -z "$NEW" ]]; then
  echo "Usage: $0 NewProjectName" >&2
  exit 1
fi

if [[ ! "$NEW" =~ ^[A-Za-z][A-Za-z0-9_]*$ ]]; then
  echo "Error: '$NEW' is not a valid Lean module name." >&2
  echo "Use a letter followed by letters, digits or underscores, e.g. MyProject." >&2
  exit 1
fi

cd "$(dirname "$0")"

if [[ ! -f "$OLD.lean" || ! -d "$OLD" ]]; then
  echo "Error: $OLD.lean / $OLD/ not found — has the project already been renamed?" >&2
  exit 1
fi

if [[ -e "$NEW.lean" || -e "$NEW" ]]; then
  echo "Error: $NEW.lean or $NEW/ already exists." >&2
  exit 1
fi

# Use `git mv` when inside a git repository so history follows the files.
move() {
  if git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git mv "$1" "$2"
  else
    mv "$1" "$2"
  fi
}

# Replace every occurrence of the old name in the project's text files.
files=(lakefile.toml lake-manifest.json "$OLD.lean")
while IFS= read -r -d '' f; do files+=("$f"); done < <(find "$OLD" -name '*.lean' -print0)

for f in "${files[@]}"; do
  [[ -f "$f" ]] && sed -i.bak "s/$OLD/$NEW/g" "$f" && rm -f "$f.bak"
done

# Only retitle the README; its instructions refer to the template by name.
[[ -f README.md ]] && sed -i.bak "1s/.*/# $NEW/" README.md && rm -f README.md.bak

move "$OLD.lean" "$NEW.lean"
move "$OLD" "$NEW"

# Build artifacts for the old package name are stale; mathlib's are kept.
rm -rf .lake/build

echo "Renamed $OLD -> $NEW."
echo "Next: run 'lake exe cache get' and 'lake build', then delete customize.sh if you like."
