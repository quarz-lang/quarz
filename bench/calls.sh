#!/bin/bash
# The table of #984: instructions per operation of each case of
# bench/calls.qz, compiled (-O2) and, with --vm, interpreted, pinned to
# one core: (at N2 - at N1) / (N2 - N1), less the `empty` case's.
# QUARZ: the quarz to build with (default target/release/quarz);
# CPU: the core (default 2).
set -u
here=$(cd "$(dirname "$0")" && pwd)
quarz=${QUARZ:-$here/../target/release/quarz}
cpu=${CPU:-2}
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
QUARZ_AOT_OPT=2 "$quarz" build -o "$out/calls" "$here/calls.qz" > /dev/null || exit 1
count() { # mode case n
  if [ "$1" = vm ]; then set -- "$1" "$2" "$3" "$quarz" run "$here/calls.qz"; else set -- "$1" "$2" "$3" "$out/calls"; fi
  local c=$2 n=$3; shift 3
  QUARZ_THREADS=1 taskset -c "$cpu" perf stat -x, -e cpu_core/instructions/u -o "$out/st" "$@" "$c" "$n" > /dev/null 2>&1
  grep instructions "$out/st" | cut -d, -f1
}
per() { # mode case n1 n2
  local a b
  a=$(count "$1" "$2" "$3"); b=$(count "$1" "$2" "$4")
  echo $(( (b - a) / ($4 - $3) ))
}
modes=compiled
[ "${1:-}" = --vm ] && modes="compiled vm"
for mode in $modes; do
  if [ $mode = vm ]; then n1=20000; n2=220000; else n1=100000; n2=1100000; fi
  base=$(per $mode empty $n1 $n2)
  echo "== $mode (empty loop: $base per iteration)"
  for c in native0 fast0 native1 fast1 native2 owned block_value static_call static_call_kept dynamic_call new keywords keywords_left_out defaults; do
    echo "$c $(( $(per $mode $c $n1 $n2) - base ))"
  done
  # (Per element: no outer loop to take away.)
  for c in each_loop map_loop each_block_value each_yield hash_each hash_each_pair each_line each_char; do
    echo "$c $(per $mode $c $n1 $n2) (per element)"
  done
done
