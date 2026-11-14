#!/usr/bin/env bash
# Differential fuzz of extension conformance: random programs (classes,
# modules, scoped and top-level extensions, abstract methods and methods
# with a body, overloads, methods of another result type) run with two
# quarz binaries, whose answers are compared.
#
#   tools/fuzz-extensions/run.sh OLD_QUARZ NEW_QUARZ [COUNT] [FIRST_SEED]
#
# For each seed and each generator (gen1.py: one extension per
# conformance; gen2.py: a module brought through a second extension;
# gen3.py: the witness record's rarer rules, #536 step 3: generic targets
# under different arguments, an extension's own method below a
# conformance, an own include whose only method of the name has another
# result type, two conformances to one module up a chain; gen4.py: an
# extension's class-side conformance, #669: the witness of a module's
# class method among the extension's own, the target's own, its own
# includes, the extension's includes and a superclass's; gen5.py: an
# abstract class's requirements implemented further up, by an include or
# by the subclass, called by name and through the abstract type), the
# program is run on the interpreter with each binary (QUARZ_NO_CACHE=1,
# QUARZ_THREADS=1, QUARZ_VERIFY=moves, a timeout of 60 seconds) and the
# two outputs (stdout and stderr together) and exit statuses are
# compared. A difference is any difference; the programs that differ are
# kept in OUT (default: a new temporary directory) as SEED.GEN.qz with
# both outputs, and listed. Prints a summary line:
#
#   fuzz-extensions: N programs, D differ, V violations with OLD, W with NEW
#
# (a violation: "internal error", "QIR fact violated", a panic or a
# TypeError in the output: the checker accepted a program that broke a
# guarantee; an assertion of NEW alone, an oracle's say, is a difference
# too). Exits 1 when anything differs, 0 otherwise, 2 on a usage error.
# FUZZ_GENS picks the generators (default: all five). COUNT is the
# number of seeds per generator (default 1000); runs go in
# parallel, FUZZ_JOBS at once (default: the number of CPUs).
#
# To compare a branch with main: build main in a second worktree with its
# own CARGO_TARGET_DIR and pass its target/debug/quarz as OLD_QUARZ.
set -euo pipefail

if [ "$#" -lt 2 ]; then
  echo "usage: tools/fuzz-extensions/run.sh OLD_QUARZ NEW_QUARZ [COUNT] [FIRST_SEED]" >&2
  exit 2
fi
old=$(readlink -f "$1")
new=$(readlink -f "$2")
count=${3:-1000}
first=${4:-1}
here=$(cd "$(dirname "$0")" && pwd)
out=${OUT:-$(mktemp -d)}
jobs_n=${FUZZ_JOBS:-$(nproc)}
[ -x "$old" ] && [ -x "$new" ] || { echo "fuzz-extensions: a binary cannot be run" >&2; exit 2; }
mkdir -p "$out"

one() {
  local gen=$1 seed=$2 old=$3 new=$4 here=$5 out=$6
  local dir
  dir=$(mktemp -d)
  python3 "$here/$gen.py" "$seed" > "$dir/p.qz"
  local oo on so sn
  set +e
  oo=$(cd "$dir" && QUARZ_NO_CACHE=1 QUARZ_THREADS=1 QUARZ_VERIFY=moves timeout 60 "$old" run p.qz 2>&1); so=$?
  on=$(cd "$dir" && QUARZ_NO_CACHE=1 QUARZ_THREADS=1 QUARZ_VERIFY=moves timeout 60 "$new" run p.qz 2>&1); sn=$?
  set -e
  local viol='internal error|QIR fact|panicked|^TypeError'
  local vo=0 vn=0 same=1
  grep -Eq "$viol" <<<"$oo" && vo=1
  grep -Eq "$viol" <<<"$on" && vn=1
  if [ "$oo" != "$on" ] || [ "$so" != "$sn" ]; then
    same=0
    cp "$dir/p.qz" "$out/$seed.$gen.qz"
    printf '%s\n[exit %s]\n' "$oo" "$so" > "$out/$seed.$gen.old"
    printf '%s\n[exit %s]\n' "$on" "$sn" > "$out/$seed.$gen.new"
  fi
  rm -rf "$dir"
  echo "$gen $seed $same $vo $vn"
}
export -f one

export FZ_OLD="$old" FZ_NEW="$new" FZ_HERE="$here" FZ_OUT="$out"
results=$(for gen in ${FUZZ_GENS:-gen1 gen2 gen3 gen4 gen5}; do
  seq "$first" $((first + count - 1)) | sed "s/^/$gen /"
done | xargs -P "$jobs_n" -n 2 bash -c 'one "$1" "$2" "$FZ_OLD" "$FZ_NEW" "$FZ_HERE" "$FZ_OUT"' _)

total=$(wc -l <<<"$results")
differ=$(awk '$3 == 0' <<<"$results" | wc -l)
vold=$(awk '$4 == 1' <<<"$results" | wc -l)
vnew=$(awk '$5 == 1' <<<"$results" | wc -l)
awk '$3 == 0 { print "differs: " $2 "." $1 }' <<<"$results" | sort -n
echo "fuzz-extensions: $total programs, $differ differ, $vold violations with OLD, $vnew with NEW (kept in $out)"
[ "$differ" -eq 0 ]
