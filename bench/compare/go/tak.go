package main

import (
	"fmt"
	"os"
	"strconv"
)

func tak(x, y, z int) int {
	if y >= x {
		return z
	}
	return tak(tak(x-1, y, z), tak(y-1, z, x), tak(z-1, x, y))
}

func main() {
	n, _ := strconv.Atoi(os.Args[1])
	fmt.Println(tak(n*3, n*2, n))
}
