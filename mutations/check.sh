#!/bin/sh
# Applies each mutation to ArgosGuard.lean and checks that the result no longer builds.
set -u
cd "$(dirname "$0")/.."
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
status=0
for d in mutations/*.diff; do
  rm -f "$tmp/ArgosGuard.lean"
  if ! patch -s -o "$tmp/ArgosGuard.lean" ArgosGuard.lean "$d"; then
    echo "$d: does not apply"; status=1
  elif lake env lean "$tmp/ArgosGuard.lean" >/dev/null 2>&1; then
    echo "$d: still builds"; status=1
  else
    echo "$d: breaks the build"
  fi
done
exit $status
