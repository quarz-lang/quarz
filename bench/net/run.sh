#!/bin/bash
# Throughput of the line echo servers (echo.qz in the interpreter and
# compiled with each backend, server.go with one thread and with
# several), driven by client.go: round trips per second for each number
# of connections. Run from the repository root after `cargo build
# --release`, with `go` on the path:
#
#   bench/net/run.sh [CONNS...]          # default: 1 16 64 256
#
# SERVER_CPU (default 2) is the one CPU the single-threaded servers are
# pinned to, SERVER_CPUS (default 0-3) the ones the multi-threaded Go
# server may use, CLIENT_CPUS (default 4-15) the client's; DUR (default
# 5s) the measuring time after a second of warm-up.
set -euo pipefail
if [ $# -gt 0 ]; then conns=("$@"); else conns=(1 16 64 256); fi
server_cpu=${SERVER_CPU:-2}
server_cpus=${SERVER_CPUS:-0-3}
client_cpus=${CLIENT_CPUS:-4-15}
dur=${DUR:-5s}
quarz=./target/release/quarz
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

go build -o "$out/client" bench/net/client.go
go build -o "$out/server" bench/net/server.go
$quarz build bench/net/echo.qz -o "$out/echo_llvm" >/dev/null

port=$((20000 + RANDOM % 20000))
# measure NAME CPUS CONNS COMMAND...: start the server pinned to CPUS,
# wait for its port, run the client, stop the server.
measure() {
  local name=$1 cpus=$2 c=$3
  shift 3
  port=$((port + 1))
  taskset -c "$cpus" "$@" "$port" >/dev/null 2>&1 &
  local pid=$!
  for _ in $(seq 100); do
    (exec 3<>"/dev/tcp/127.0.0.1/$port") 2>/dev/null && break
    sleep 0.05
  done
  local r
  r=$(taskset -c "$client_cpus" "$out/client" -port "$port" -c "$c" -d "$dur" | awk '{print $1}')
  kill "$pid" 2>/dev/null || true
  wait "$pid" 2>/dev/null || true
  printf " %10s" "$r"
}

printf "%-6s %10s %10s %10s %10s\n" conns quarz-vm quarz-llvm go-1thread go-multi
for c in "${conns[@]}"; do
  printf "%-6s" "$c"
  measure vm "$server_cpu" "$c" $quarz run bench/net/echo.qz
  measure llvm "$server_cpu" "$c" "$out/echo_llvm"
  measure go1 "$server_cpu" "$c" env GOMAXPROCS=1 "$out/server"
  measure goN "$server_cpus" "$c" "$out/server"
  echo
done
echo "(round trips per second; 64-byte lines)"
