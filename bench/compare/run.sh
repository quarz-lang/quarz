#!/bin/sh
# Compare Quarz (VM and compiled) with Go, Rust and Ruby on bench/*.qz.
# Prints the best wall-clock time of several runs for each program.
#
#   cargo build --release
#   PATH="$HOME/go-sdk/bin:$PATH" bench/compare/run.sh
set -e
cd "$(dirname "$0")/../.."
out=$(mktemp -d)
runs=${RUNS:-5}
quarz=./target/release/quarz
mkdir -p "$out/bin"
for b in fib loop collections objects strings; do
  $quarz build bench/$b.qz -o "$out/bin/quarz_$b"
  go build -o "$out/bin/go_$b" bench/compare/go/$b.go
  rustc -O -o "$out/bin/rust_$b" bench/compare/rust/$b.rs
done
# Best wall-clock time of `runs` runs, in milliseconds.
best() {
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
printf "%-12s %9s %9s %9s %9s %9s %9s\n" "program" "quarz-vm" "quarz-aot" "go" "rust" "ruby" "ruby-yjit"
for b in fib loop collections objects strings; do
  printf "%-12s %9s %9s %9s %9s %9s %9s\n" "$b" \
    "$(best $quarz run bench/$b.qz)" \
    "$(best "$out/bin/quarz_$b")" \
    "$(best "$out/bin/go_$b")" \
    "$(best "$out/bin/rust_$b")" \
    "$(best ruby bench/compare/ruby/$b.rb)" \
    "$(best ruby --yjit bench/compare/ruby/$b.rb)"
done
echo "(milliseconds; best of $runs runs)"
rm -rf "$out"
