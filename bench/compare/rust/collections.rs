use std::collections::HashMap;
fn main() {
    let mut acc: Vec<i64> = Vec::new();
    for i in 0..8_000_000 {
        acc.push(i);
    }
    println!("{}", acc.len());
    let mapped: Vec<i64> = acc.iter().map(|x| x * 2).collect();
    let selected: Vec<i64> = mapped.into_iter().filter(|x| x % 3 == 0).collect();
    let total: i64 = selected.iter().fold(0, |a, x| a + x);
    println!("{total}");
    let mut h: HashMap<i64, i64> = HashMap::new();
    for i in 0..1_600_000 {
        h.insert(i, i * 2);
    }
    println!("{}", h.len());
    let s: i64 = (1..=8_000_000i64).fold(0, |a, x| a + x);
    println!("{s}");
}
