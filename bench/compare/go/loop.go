package main

import "fmt"

func main() {
	i := 0
	sum := 0
	for i < 120000000 {
		sum += i * 2 % 7
		i++
	}
	fmt.Println(sum)
}
