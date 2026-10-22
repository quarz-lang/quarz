#!/bin/sh
# Compare Quarz (VM and compiled) with Go, Rust, Crystal, Spinel and
# Ruby on bench/*.qz and their transcriptions here. Prints the best
# wall-clock time of several runs for each program, in milliseconds.
#
#   cargo build --release
#   PATH="$HOME/go-sdk/bin:$PATH" RUNS=10 taskset -c 3 bench/compare/run.sh
#
# Go, rustc and ruby must be on the path. Crystal and Spinel are used
# when found: CRYSTAL names the compiler (default `crystal`, with
# CRYSTAL_LINK_FLAGS passed to `--link-flags` if set), SPINEL the
# `spinel` script (default `spinel`). A missing one prints `-`.
# Every program's output is checked against Quarz's first.
set -e
cd "$(dirname "$0")/../.."
out=$(mktemp -d)
runs=${RUNS:-5}
quarz=./target/release/quarz
crystal=${CRYSTAL:-crystal}
spinel=${SPINEL:-spinel}
have() { command -v "$1" >/dev/null 2>&1; }
programs="fib loop collections objects strings dispatch tak"
mkdir -p "$out/bin"
for b in $programs; do
  $quarz build bench/$b.qz -o "$out/bin/llvm_$b"
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
# Best wall-clock time of `runs` runs of a command, in milliseconds; `-`
# when its program was not built.
best() {
  if [ ! -x "$1" ] && ! have "$1"; then
    printf -- "-"
    return
  fi
  min=
  for _ in $(seq "$runs"); do
    start=$(date +%s%N)
    "$@" >/dev/null
    end=$(date +%s%N)
    t=$(( (end - start) / 100000 ))
    if [ -z "$min" ] || [ "$t" -lt "$min" ]; then min=$t; fi
  done
  printf "%d.%d" $((min / 10)) $((min % 10))
}
# The same output everywhere (numbers compared as numbers: `3.0` and
# `3.00` agree).
norm() {
  awk '{ for (i = 1; i <= NF; i++) {
           if ($i ~ /^-?[0-9]+(\.[0-9]+)?$/) printf "%.10g\n", $i; else print $i } }'
}
check() {
  want=$("$out/bin/llvm_$1" $2 | norm)
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
printf "%-13s %9s %9s %7s %7s %7s %7s %8s %8s\n" program quarz-vm quarz-llvm \
  go rust crystal spinel ruby ruby-yjit
row() {
  name=$1
  b=$2
  arg=$3
  check "$b" "$arg"
  printf "%-13s %9s %9s %7s %7s %7s %7s %8s %8s\n" "$name" \
    "$(best $quarz run bench/$b.qz $arg)" \
    "$(best "$out/bin/llvm_$b" $arg)" \
    "$(best "$out/bin/go_$b" $arg)" \
    "$(best "$out/bin/rust_$b" $arg)" \
    "$(best "$out/bin/crystal_$b" $arg)" \
    "$(best "$out/bin/spinel_$b" $arg)" \
    "$(best ruby bench/compare/ruby/$b.rb $arg)" \
    "$(best ruby --yjit bench/compare/ruby/$b.rb $arg)"
}
for b in fib loop collections objects strings dispatch; do
  row "$b" "$b" ""
done
row "tak(24,16,8)" tak 8
row "tak(27,18,9)" tak 9
echo "(milliseconds; best of $runs runs)"
rm -rf "$out"
