#!/bin/sh
# The differential test (README.md): each program in corpus/, and every
# fixture and example, checked by `quarz check --tree` and then by the
# model. A program the model disagrees on fails the run; one outside the
# model's range is counted. QUARZ is the `quarz` binary (default: the
# workspace's debug build).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
quarz=${QUARZ:-$root/target/debug/quarz}
conf=$here/.lake/build/bin/conformance
agree=0 out=0 bad=0
for f in "$here"/corpus/*.qz $(find "$root/crates/quarz-cli/tests/fixtures" "$root/examples" -name '*.qz' | sort); do
  tree=$("$quarz" check --tree "$f" 2>/dev/null) || {
    # The corpus checks, by design.
    case $f in "$here"/corpus/*) bad=$((bad + 1)); echo "${f#$root/}: does not check" ;; esac
    continue
  }
  r=$(printf '%s' "$tree" | "$conf")
  case $r in
    agrees) agree=$((agree + 1)) ;;
    "out of range"*) out=$((out + 1)) ;;
    *) bad=$((bad + 1)); echo "${f#$root/}: $r" ;;
  esac
  # The corpus is in range, by design.
  case $f in "$here"/corpus/*) case $r in "out of range"*) bad=$((bad + 1)); echo "${f#$root/}: $r" ;; esac ;; esac
done
echo "conformance: $agree agree, $out out of range, $bad disagree"
[ "$bad" -eq 0 ]
