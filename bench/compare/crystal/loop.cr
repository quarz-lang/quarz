i = 0_i64
sum = 0_i64
while i < 3_000_000
  sum += i * 2 % 7
  i += 1
end
puts sum
