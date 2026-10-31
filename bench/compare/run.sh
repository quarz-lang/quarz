#!/bin/sh
# Compare Quarz (VM and compiled) with Go, Rust, Crystal, Spinel and
# Ruby on bench/*.qz and their transcriptions here. Prints the best
# wall-clock time of several runs for each program, in milliseconds,
# then how many runs each took: after a first run of t ms,
# clamp(round(20000 / t), 3, 20) in all (RUNS=n makes it n everywhere).
#
#   cargo build --release
#   PATH="$HOME/go-sdk/bin:$PATH" taskset -c 3 bench/compare/run.sh
#
# Go, rustc and ruby must be on the path. Crystal and Spinel are used
# when found: CRYSTAL names the compiler (default `crystal`, with
# CRYSTAL_LINK_FLAGS passed to `--link-flags` if set), SPINEL the
# `spinel` script (default `spinel`). A missing one prints `-`.
# Every program's output is checked against Quarz's first.
set -e
cd "$(dirname "$0")/../.."
out=$(mktemp -d)
counts=$(mktemp)
trap 'rm -rf "$out" "$counts"' EXIT
quarz=./target/release/quarz
crystal=${CRYSTAL:-crystal}
spinel=${SPINEL:-spinel}
have() { command -v "$1" >/dev/null 2>&1; }
programs="startup fib loop collections objects strings dispatch tak"
mkdir -p "$out/bin"
for b in $programs; do
  $quarz build bench/$b.qz -o "$out/bin/aot_$b"
  go build -o "$out/bin/go_$b" bench/compare/go/$b.go
  rustc -O -o "$out/bin/rust_$b" bench/compare/rust/$b.rs
  if have "$crystal"; then
    if [ -n "$CRYSTAL_LINK_FLAGS" ]; then
      "$crystal" build --release --no-debug --link-flags "$CRYSTAL_LINK_FLAGS" \
        -o "$out/bin/crystal_$b" bench/compare/crystal/$b.cr
    else
      "$crystal" build --release --no-debug -o "$out/bin/crystal_$b" bench/compare/crystal/$b.cr
    fi
  fi
  if have "$spinel"; then
    "$spinel" bench/compare/ruby/$b.rb -o "$out/bin/spinel_$b" >/dev/null 2>&1
  fi
done
# Best wall-clock time of a command's runs, in milliseconds, and their
# number (`TIME RUNS`); `- -` when its program was not built.
best() {
  if [ ! -x "$1" ] && ! have "$1"; then
    printf -- "- -"
    return
  fi
  min=
  runs=${RUNS:-}
  i=0
  while [ -z "$runs" ] || [ "$i" -lt "$runs" ]; do
    start=$(date +%s%N)
    "$@" >/dev/null
    end=$(date +%s%N)
    t=$(( (end - start) / 100000 ))
    if [ -z "$min" ] || [ "$t" -lt "$min" ]; then min=$t; fi
    i=$((i + 1))
    if [ -z "$runs" ]; then
      # About 20 s of runs in all, from the first one's time (in 0.1 ms).
      runs=$(( (200000 + t / 2) / (t > 0 ? t : 1) ))
      [ "$runs" -lt 3 ] && runs=3
      [ "$runs" -gt 20 ] && runs=20
    fi
  done
  printf "%d.%d %d" $((min / 10)) $((min % 10)) "$runs"
}
# The same output everywhere (numbers with a decimal point compared as
# numbers to 15 digits: `3.0` and `3.00` agree; integers as written).
norm() {
  awk '{ for (i = 1; i <= NF; i++) {
           if ($i ~ /^-?[0-9]+\.[0-9]+$/) printf "%.15g\n", $i; else print $i } }'
}
check() {
  want=$("$out/bin/aot_$1" $2 | norm)
  for cmd in "$quarz run bench/$1.qz" "$out/bin/go_$1" \
    "$out/bin/rust_$1" "$out/bin/crystal_$1" "$out/bin/spinel_$1" \
    "ruby bench/compare/ruby/$1.rb"; do
    bin=${cmd%% *}
    if [ -x "$bin" ] || have "$bin"; then
      got=$($cmd $2 | norm)
      if [ "$got" != "$want" ]; then
        echo "output of $cmd $2 differs:" >&2
        echo "$got" >&2
        exit 1
      fi
    fi
  done
}
header() {
  printf "%-14s %9s %9s %7s %7s %7s %7s %8s %8s\n" "$1" quarz-vm quarz-aot \
    go rust crystal spinel ruby ruby-yjit
}
# A row of times, and its run counts kept for the second table.
row() {
  name=$1
  b=$2
  arg=$3
  check "$b" "$arg"
  set -- \
    "$(best $quarz run bench/$b.qz $arg)" \
    "$(best "$out/bin/aot_$b" $arg)" \
    "$(best "$out/bin/go_$b" $arg)" \
    "$(best "$out/bin/rust_$b" $arg)" \
    "$(best "$out/bin/crystal_$b" $arg)" \
    "$(best "$out/bin/spinel_$b" $arg)" \
    "$(best ruby bench/compare/ruby/$b.rb $arg)" \
    "$(best ruby --yjit bench/compare/ruby/$b.rb $arg)"
  printf "%-14s %9s %9s %7s %7s %7s %7s %8s %8s\n" "$name" \
    "${1% *}" "${2% *}" "${3% *}" "${4% *}" "${5% *}" "${6% *}" "${7% *}" "${8% *}"
  printf "%-14s %9s %9s %7s %7s %7s %7s %8s %8s\n" "$name" \
    "${1#* }" "${2#* }" "${3#* }" "${4#* }" "${5#* }" "${6#* }" "${7#* }" "${8#* }" >>"$counts"
}
header program
for b in startup fib loop collections objects strings dispatch; do
  row "$b" "$b" ""
done
row "tak(30,20,10)" tak 10
echo "(milliseconds, best of the runs below; process start-up included)"
echo
header runs
cat "$counts"
