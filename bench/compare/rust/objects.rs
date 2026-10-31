#[derive(Clone, Copy)]
struct Vec2 {
    x: f64,
    y: f64,
}
impl Vec2 {
    fn add(self, o: Vec2) -> Vec2 {
        Vec2 { x: self.x + o.x, y: self.y + o.y }
    }
    fn scale(self, k: f64) -> Vec2 {
        Vec2 { x: self.x * k, y: self.y * k }
    }
}
struct Particle {
    pos: Vec2,
    vel: Vec2,
}
impl Particle {
    fn step(&mut self, dt: f64) {
        self.pos = self.pos.add(self.vel.scale(dt));
    }
}
fn main() {
    let mut ps: Vec<Box<Particle>> = (0..1000)
        .map(|i| Box::new(Particle { pos: Vec2 { x: i as f64, y: 0.0 }, vel: Vec2 { x: 1.0, y: 0.5 } }))
        .collect();
    for _ in 0..15_000 {
        for p in ps.iter_mut() {
            p.step(0.01);
        }
    }
    println!("{:.2}", ps[0].pos.x);
}
