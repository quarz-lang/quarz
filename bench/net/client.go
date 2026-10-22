// Load for the echo servers: -c connections, each sending a line of
// -size bytes and waiting for it to come back, for -d; prints the round
// trips per second.
//
//	go build -o client bench/net/client.go && ./client -port PORT -c 64 -d 5s
package main

import (
	"bufio"
	"bytes"
	"flag"
	"fmt"
	"net"
	"os"
	"sync"
	"sync/atomic"
	"time"
)

func main() {
	port := flag.String("port", "9000", "server port on 127.0.0.1")
	conns := flag.Int("c", 64, "connections")
	dur := flag.Duration("d", 5*time.Second, "duration")
	size := flag.Int("size", 64, "bytes per line, newline included")
	flag.Parse()
	msg := append(bytes.Repeat([]byte("x"), *size-1), '\n')
	var total atomic.Int64
	var stop atomic.Bool
	var wg sync.WaitGroup
	for i := 0; i < *conns; i++ {
		c, err := net.Dial("tcp", "127.0.0.1:"+*port)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		wg.Add(1)
		go func(c net.Conn) {
			defer wg.Done()
			defer c.Close()
			r := bufio.NewReader(c)
			for !stop.Load() {
				if _, err := c.Write(msg); err != nil {
					fmt.Fprintln(os.Stderr, err)
					return
				}
				line, err := r.ReadSlice('\n')
				if err != nil || len(line) != len(msg) {
					fmt.Fprintln(os.Stderr, "bad reply:", err)
					return
				}
				total.Add(1)
			}
		}(c)
	}
	// A second to warm up, then count the round trips made during -d.
	time.Sleep(time.Second)
	before := total.Load()
	t0 := time.Now()
	time.Sleep(*dur)
	after := total.Load()
	elapsed := time.Since(t0).Seconds()
	stop.Store(true)
	wg.Wait()
	fmt.Printf("%.0f round trips/s (%d connections, %d-byte lines)\n",
		float64(after-before)/elapsed, *conns, *size)
}
