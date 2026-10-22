// A line echo server, the same as echo.qz: a goroutine per connection
// writes back each line it reads, one write per line.
//
//	go build -o server bench/net/server.go && ./server PORT
package main

import (
	"bufio"
	"fmt"
	"net"
	"os"
)

func main() {
	ln, err := net.Listen("tcp", "127.0.0.1:"+os.Args[1])
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	for {
		c, err := ln.Accept()
		if err != nil {
			continue
		}
		go func(c net.Conn) {
			defer c.Close()
			r := bufio.NewReader(c)
			for {
				line, err := r.ReadSlice('\n')
				if err != nil {
					return
				}
				if _, err := c.Write(line); err != nil {
					return
				}
			}
		}(c)
	}
}
