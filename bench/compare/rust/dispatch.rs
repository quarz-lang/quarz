trait Shape {
    fn area(&self) -> f64;
}
struct Circle {
    r: f64,
}
struct Rect {
    w: f64,
    h: f64,
}
struct Tri {
    b: f64,
    h: f64,
}
impl Shape for Circle {
    fn area(&self) -> f64 {
        3.0 * self.r * self.r
    }
}
impl Shape for Rect {
    fn area(&self) -> f64 {
        self.w * self.h
    }
}
impl Shape for Tri {
    fn area(&self) -> f64 {
        0.5 * self.b * self.h
    }
}
fn main() {
    let mut shapes: Vec<Box<dyn Shape>> = Vec::new();
    for i in 0..300 {
        let f = i as f64;
        shapes.push(Box::new(Circle { r: f }));
        shapes.push(Box::new(Rect { w: f, h: 2.0 }));
        shapes.push(Box::new(Tri { b: f, h: 3.0 }));
    }
    let mut total = 0.0;
    for _ in 0..1000 {
        for s in &shapes {
            total += s.area();
        }
    }
    println!("{:.1}", (total * 10.0f64).round() / 10.0);
}
