#!/usr/bin/env bash
# Compares the checker's verdicts of two quarz binaries.
#
#   tools/check-diff.sh OLD_QUARZ NEW_QUARZ [DIR...]
#
# Runs `quarz check` with each binary over every tracked `.qz` file of
# this repository, and over the cog checkouts given as DIRs, and prints
# the programs whose verdict changed: newly refused, newly accepted, a
# changed message (exit status or diagnostics), or a run that timed out
# or crashed with one binary only, with both outputs. Exits 1 when
# anything changed, 0 otherwise, 2 on an error (a usage error, a DIR in
# which nothing is found, a binary or `timeout` that could not run).
#
# What is checked:
# - a tracked `.qz` file of this repository outside a cog: `quarz check
#   FILE`, from the repository's root;
# - a cog (a directory with a tracked `Cog.toml`, in this repository or
#   in a DIR, the DIR itself included): `quarz check` in its directory
#   (its src/, as its users load it), and, when it has tracked
#   `test/**/*_test.qz` files, its tests with `quarz test --list` there
#   (checked together, as `quarz test` loads them, and not run; the list
#   itself is not compared). A cog's other `.qz` files are not checked.
#   Both run with `--locked --offline`, so that nothing is resolved,
#   fetched or written: a cog whose dependencies are not fetched yet (no
#   Cog.lock, or a dependency missing from the cache) fails the same way
#   with both binaries, which is no difference; run `quarz cog fetch`
#   (or its tests once) there first.
#
# Each run has QUARZ_NO_CACHE=1, QUARZ_THREADS=1 and QUARZ_VERIFY=moves
# (as `cargo test` has), and a timeout of CHECK_DIFF_TIMEOUT seconds
# (default 300). A program refused the same way by both binaries
# (std/prelude.qz alone, say) is not a difference; one that timed out or
# crashed the same way with both was not checked, and is listed apart.
# Runs go in parallel, CHECK_DIFF_JOBS at once (default: the number of
# CPUs); the output is in the order of the programs' paths. A DIR is
# labelled by its name, which must differ from the other DIRs' and from
# this repository's top-level entries.
#
# Needs bash and the GNU tools (find -printf, sed -i, timeout, nproc,
# xargs -0 -r -P), as on Linux.

set -euo pipefail

fail() {
  echo "check-diff: $*" >&2
  exit 2
}

if [ "$#" -lt 2 ]; then
  echo "usage: tools/check-diff.sh OLD_QUARZ NEW_QUARZ [DIR...]" >&2
  exit 2
fi

for tool in git timeout nproc xargs find sed sort cmp mktemp; do
  command -v "$tool" >/dev/null || fail "needs $tool"
done
timeout_s=${CHECK_DIFF_TIMEOUT:-300}
jobs_n=${CHECK_DIFF_JOBS:-$(nproc)}
case "$timeout_s" in '' | *[!0-9]* | 0) fail "CHECK_DIFF_TIMEOUT is not a positive number of seconds: $timeout_s" ;; esac
case "$jobs_n" in '' | *[!0-9]* | 0) fail "CHECK_DIFF_JOBS is not a positive number: $jobs_n" ;; esac

absolute() { # an absolute path for $1, which exists
  if [ -d "$1" ]; then (cd "$1" && pwd -P); else
    printf '%s/%s\n' "$(cd "$(dirname "$1")" && pwd -P)" "$(basename "$1")"
  fi
}

binary() { # the absolute path of the executable $1 (a path, or a command)
  local b=$1
  case "$b" in */*) ;; *) b=$(command -v -- "$b" || true) ;; esac
  if [ -z "$b" ] || [ ! -f "$b" ] || [ ! -x "$b" ]; then
    fail "not an executable: $1"
  fi
  absolute "$b"
}

old=$(binary "$1") || exit 2
new=$(binary "$2") || exit 2
shift 2

repo=$(cd "$(dirname "$0")/.." && pwd -P)
git -C "$repo" rev-parse --is-inside-work-tree >/dev/null 2>&1 || fail "not in a git checkout: $repo"

dirs=()
labels=" "
for d in "$@"; do
  [ -d "$d" ] || fail "not a directory: $d"
  d=$(absolute "$d")
  name=$(basename "$d")
  case "$labels" in *" $name/ "*) fail "two DIRs named $name" ;; esac
  if [ -n "$(git -C "$repo" ls-files -- ":(top,literal)$name" | head -1)" ]; then
    fail "a DIR named like a path of this repository: $name"
  fi
  labels="$labels$name/ "
  dirs+=("$d")
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
# From here on a failing command is an error (2), not a difference (1).
set -E
trap 'exit 2' ERR

export QUARZ_NO_CACHE=1 QUARZ_THREADS=1 QUARZ_VERIFY=moves
export CHECK_DIFF_OLD=$old CHECK_DIFF_NEW=$new CHECK_DIFF_TMP=$tmp
export CHECK_DIFF_TIMEOUT=$timeout_s

# The pattern of sed's s|...|...| that matches $1 literally.
literal() { printf '%s' "$1" | sed 's/[][\\.*^$|]/\\&/g'; }
export -f literal
# The replacement of sed's s|...|...| that is $1 literally.
replacement() { printf '%s' "$1" | sed 's/[\\&|]/\\&/g'; }

# Absolute paths in diagnostics (a dependency's files, which a cog names
# by its absolute path) become paths under the labels: this
# repository's root goes, a DIR becomes its name, and the home directory
# (a dependency fetched into the cache) becomes ~.
{
  printf 's|%s/||g\n' "$(literal "$repo")"
  for d in ${dirs[@]+"${dirs[@]}"}; do
    printf 's|%s/|%s/|g\n' "$(literal "$d")" "$(replacement "$(basename "$d")")"
  done
  if [ -n "${HOME:-}" ]; then printf 's|%s/|~/|g\n' "$(literal "$HOME")"; fi
} >"$tmp/paths.sed"

# The jobs, one per line of $tmp/jobs.tsv: LABEL, KIND (check, cog or
# test), DIRECTORY to run in, TARGET. A path with a tab or a newline in
# it is refused rather than misread.
jobs=$tmp/jobs.tsv
: >"$jobs"
add_job() { # LABEL KIND DIR TARGET
  case "$1$3$4" in
    *$'\t'* | *$'\n'*) fail "a tab or newline in a path: $1" ;;
  esac
  printf '%s\t%s\t%s\t%s\n' "$1" "$2" "$3" "$4" >>"$jobs"
}

# The tracked files of a directory's repository under it, NUL-separated
# (every file under it when it is not in a git repository), into $2.
tracked() { # DIR PATTERN OUT
  if git -C "$1" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    git -C "$1" ls-files -z -- "$2" >"$3"
  else
    (cd "$1" && find . -type f -path "./$2" -printf '%P\0') >"$3"
  fi
}

# Adds the jobs of the cogs under ROOT (labelled PREFIX/path) and writes
# their directories, relative to ROOT, NUL-separated, to OUT.
add_cogs() { # ROOT PREFIX OUT
  local root=$1 prefix=$2 out=$3 toml cog dir label f
  : >"$out"
  tracked "$root" '*Cog.toml' "$tmp/tomls"
  while IFS= read -r -d '' toml; do
    case "$toml" in Cog.toml | */Cog.toml) ;; *) continue ;; esac
    cog=$(dirname "$toml")
    if [ "$cog" = . ]; then
      dir=$root label=${prefix%/}
    else
      dir=$root/$cog label=$prefix$cog
    fi
    add_job "$label/ (cog)" cog "$dir" .
    tracked "$dir" 'test/*.qz' "$tmp/tests"
    while IFS= read -r -d '' f; do
      case "$f" in
        *_test.qz)
          add_job "$label/test/ (tests)" test "$dir" test
          break
          ;;
      esac
    done <"$tmp/tests"
    printf '%s\0' "$cog" >>"$out"
  done <"$tmp/tomls"
}

# This repository: its cogs, then the files outside them.
add_cogs "$repo" "" "$tmp/cogs"
git -C "$repo" ls-files -z -- '*.qz' >"$tmp/files"
while IFS= read -r -d '' f; do
  inside=
  while IFS= read -r -d '' cog; do
    case "$f" in "$cog"/*) inside=1 ;; esac
  done <"$tmp/cogs"
  if [ -z "$inside" ]; then add_job "$f" check "$repo" "$f"; fi
done <"$tmp/files"

# The DIRs, labelled by their own names; one without a cog is an error
# (a typo, or a cog not committed yet).
for d in ${dirs[@]+"${dirs[@]}"}; do
  add_cogs "$d" "$(basename "$d")/" "$tmp/dircogs"
  [ -s "$tmp/dircogs" ] || fail "no tracked Cog.toml in $d"
done

LC_ALL=C sort -t $'\t' -k1,1 -o "$jobs" "$jobs"
total=$(wc -l <"$jobs")

# Runs one job with both binaries: N KIND DIR TARGET. Writes
# $tmp/N.{old,new} (the output) and $tmp/N.{old,new}.rc.
run_job() {
  local n=$1 kind=$2 dir=$3 target=$4 side bin rc out
  for side in old new; do
    if [ "$side" = old ]; then bin=$CHECK_DIFF_OLD; else bin=$CHECK_DIFF_NEW; fi
    out=$CHECK_DIFF_TMP/$n.$side
    rc=0
    if ! cd "$dir" 2>"$out"; then
      rc=126
    else
      case "$kind" in
        check) timeout -k 10 "$CHECK_DIFF_TIMEOUT" "$bin" check "$target" \
          >"$out" 2>&1 </dev/null || rc=$? ;;
        cog) timeout -k 10 "$CHECK_DIFF_TIMEOUT" "$bin" check --locked --offline \
          >"$out" 2>&1 </dev/null || rc=$? ;;
        test) timeout -k 10 "$CHECK_DIFF_TIMEOUT" "$bin" test --list --locked --offline \
          2>"$out" >/dev/null </dev/null || rc=$? ;;
      esac
    fi
    if [ "$rc" = 124 ] || [ "$rc" = 137 ]; then
      if [ -s "$out" ] && [ -n "$(tail -c 1 "$out")" ]; then echo >>"$out"; fi
      echo "(timed out after ${CHECK_DIFF_TIMEOUT}s)" >>"$out"
    fi
    # The directory it ran in goes from absolute paths, then the roots
    # become labels ($tmp/paths.sed).
    sed -i -e "s|$(literal "$dir/")||g" -f "$CHECK_DIFF_TMP/paths.sed" "$out"
    echo "$rc" >"$out.rc"
  done
}
export -f run_job

n=0
while IFS=$'\t' read -r _ kind dir target; do
  n=$((n + 1))
  printf '%s\0%s\0%s\0%s\0' "$n" "$kind" "$dir" "$target"
done <"$jobs" | xargs -0 -r -n 4 -P "$jobs_n" bash -c 'run_job "$@"' run_job

# What an exit status says: 0 accepted, 1 refused, else the run failed.
outcome() {
  case "$1" in
    0) echo accepted ;;
    1) echo refused ;;
    124 | 137) echo "timed out" ;;
    *) echo crashed ;;
  esac
}

refused=0 accepted=0 changed=0 failed=0 unchecked=0 n=0
while IFS=$'\t' read -r label _; do
  n=$((n + 1))
  o=$tmp/$n.old r=$tmp/$n.new
  orc=$(cat "$o.rc") nrc=$(cat "$r.rc")
  for rc in "$orc" "$nrc"; do
    case "$rc" in
      125 | 126 | 127)
        echo "check-diff: $label: could not run (exit $rc):" >&2
        cat "$o" "$r" >&2
        exit 2
        ;;
    esac
  done
  oo=$(outcome "$orc") no=$(outcome "$nrc")
  if [ "$orc" = "$nrc" ] && cmp -s "$o" "$r"; then
    case "$oo" in accepted | refused) continue ;; esac
    verdict="$oo with both (not checked)" unchecked=$((unchecked + 1))
  elif [ "$oo" = accepted ] && [ "$no" = refused ]; then
    verdict="newly refused" refused=$((refused + 1))
  elif [ "$oo" = refused ] && [ "$no" = accepted ]; then
    verdict="newly accepted" accepted=$((accepted + 1))
  elif [ "$oo" = "$no" ]; then
    verdict="changed message" changed=$((changed + 1))
  else
    verdict="$oo, now $no" failed=$((failed + 1))
  fi
  printf '%s: %s\n' "$label" "$verdict"
  printf '  old (exit %s):\n' "$orc"
  sed 's/^/    /' "$o"
  printf '  new (exit %s):\n' "$nrc"
  sed 's/^/    /' "$r"
done <"$jobs"

echo "check-diff: $total checked, $refused newly refused, $accepted newly accepted," \
  "$changed changed message, $failed newly or no longer timed out or crashed," \
  "$unchecked timed out or crashed with both"
if [ $((refused + accepted + changed + failed)) != 0 ]; then exit 1; fi
exit 0
