#!/usr/bin/env sh

set -eu

root_dir=${1:-.}

if ! command -v grep >/dev/null 2>&1; then
  printf '%s\n' 'error: grep is required to run this check' >&2
  exit 2
fi

pattern='(^|[^A-Za-z_])(Axiom|Admitted|admit)([^A-Za-z_]|$)'

matches=$(grep -RInE \
  --include='*.v' \
  --exclude='LibTactics.v' \
  --exclude-dir='.git' \
  --exclude-dir='_build' \
  --exclude='*.vo' \
  --exclude='*.vok' \
  --exclude='*.vos' \
  --exclude='*.glob' \
  --exclude='*.aux' \
  "$pattern" "$root_dir" || true)

if [ -n "$matches" ]; then
  printf '%s\n' 'Found forbidden Axiom/admit usage:' >&2
  printf '%s\n' "$matches" >&2
  exit 1
fi

printf '%s\n' 'No forbidden Axiom/admit usage found.'