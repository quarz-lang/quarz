acc = [] of Int64
1_000_000.times { |i| acc << i.to_i64 }
puts acc.size
puts acc.map { |x| x * 2 }.select { |x| x % 3 == 0 }.reduce(0_i64) { |a, x| a + x }
h = {} of Int64 => Int64
200_000.times { |i| h[i.to_i64] = i.to_i64 * 2 }
puts h.size
puts (1_i64..1_000_000_i64).reduce(0_i64) { |a, x| a + x }
