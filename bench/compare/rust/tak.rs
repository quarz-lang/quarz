fn tak(x: i64, y: i64, z: i64) -> i64 {
    if y >= x {
        return z;
    }
    tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y))
}
fn main() {
    let n: i64 = std::env::args().nth(1).unwrap().parse().unwrap();
    println!("{}", tak(n * 3, n * 2, n));
}
