package main

import (
	"fmt"
	"strings"
)

func main() {
	var b strings.Builder
	for i := 0; i < 200000; i++ {
		fmt.Fprintf(&b, "item %d, ", i)
	}
	s := b.String()
	fmt.Println(len(s))
	words := strings.Split(s, ", ")
	// Ruby/Quarz drop the trailing empty piece.
	if len(words) > 0 && words[len(words)-1] == "" {
		words = words[:len(words)-1]
	}
	fmt.Println(len(words))
	upper := make([]string, 0, len(words))
	for _, w := range words {
		upper = append(upper, strings.ToUpper(w))
	}
	n := 0
	for _, w := range upper {
		if strings.HasSuffix(w, "7") {
			n++
		}
	}
	fmt.Println(n)
}
