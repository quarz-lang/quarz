use std::fmt::Write;
fn main() {
    let mut s = String::new();
    for i in 0..1_200_000 {
        write!(s, "item {i}, ").unwrap();
    }
    println!("{}", s.chars().count());
    let mut words: Vec<&str> = s.split(", ").collect();
    while words.last() == Some(&"") {
        words.pop();
    }
    println!("{}", words.len());
    let upper: Vec<String> = words.iter().map(|w| w.to_uppercase()).collect();
    let n = upper.iter().filter(|w| w.ends_with('7')).count();
    println!("{n}");
}
