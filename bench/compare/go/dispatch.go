package main

import (
	"fmt"
	"math"
)

type Shape interface{ Area() float64 }

type Circle struct{ r float64 }
type Rect struct{ w, h float64 }
type Tri struct{ b, h float64 }

func (c *Circle) Area() float64 { return 3.0 * c.r * c.r }
func (r *Rect) Area() float64   { return r.w * r.h }
func (t *Tri) Area() float64    { return 0.5 * t.b * t.h }

func main() {
	var shapes []Shape
	for i := 0; i < 300; i++ {
		f := float64(i)
		shapes = append(shapes, &Circle{f}, &Rect{f, 2.0}, &Tri{f, 3.0})
	}
	total := 0.0
	for k := 0; k < 1000; k++ {
		for _, s := range shapes {
			total += s.Area()
		}
	}
	fmt.Printf("%.1f\n", math.Round(total*10)/10)
}
