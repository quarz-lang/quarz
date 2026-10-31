package main

import "fmt"

func main() {
	acc := []int{}
	for i := 0; i < 8000000; i++ {
		acc = append(acc, i)
	}
	fmt.Println(len(acc))
	mapped := make([]int, 0, len(acc))
	for _, x := range acc {
		mapped = append(mapped, x*2)
	}
	selected := []int{}
	for _, x := range mapped {
		if x%3 == 0 {
			selected = append(selected, x)
		}
	}
	total := 0
	for _, x := range selected {
		total += x
	}
	fmt.Println(total)
	h := map[int]int{}
	for i := 0; i < 1600000; i++ {
		h[i] = i * 2
	}
	fmt.Println(len(h))
	s := 0
	for x := 1; x <= 8000000; x++ {
		s += x
	}
	fmt.Println(s)
}
