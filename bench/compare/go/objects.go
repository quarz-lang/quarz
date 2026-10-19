package main

import "fmt"

type Vec2 struct{ X, Y float64 }

func (a Vec2) Add(b Vec2) Vec2        { return Vec2{a.X + b.X, a.Y + b.Y} }
func (a Vec2) Scale(k float64) Vec2   { return Vec2{a.X * k, a.Y * k} }

type Particle struct{ Pos, Vel Vec2 }

func (p *Particle) Step(dt float64) { p.Pos = p.Pos.Add(p.Vel.Scale(dt)) }

func main() {
	ps := make([]*Particle, 1000)
	for i := range ps {
		ps[i] = &Particle{Vec2{float64(i), 0}, Vec2{1, 0.5}}
	}
	for t := 0; t < 300; t++ {
		for _, p := range ps {
			p.Step(0.01)
		}
	}
	fmt.Printf("%.2f\n", ps[0].Pos.X)
}
