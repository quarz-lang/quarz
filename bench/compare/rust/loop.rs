fn main() {
    let mut i: i64 = 0;
    let mut sum: i64 = 0;
    while i < 3_000_000 {
        sum += i * 2 % 7;
        i += 1;
    }
    println!("{sum}");
}
