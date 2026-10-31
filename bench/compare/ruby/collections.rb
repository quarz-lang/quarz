acc = []
8_000_000.times { |i| acc = acc.push(i) }
puts acc.size
puts acc.map { |x| x * 2 }.select { |x| x % 3 == 0 }.reduce(0) { |a, x| a + x }
h = {}
1_600_000.times { |i| h[i] = i * 2 }
puts h.size
puts (1..8_000_000).reduce(0) { |a, x| a + x }
