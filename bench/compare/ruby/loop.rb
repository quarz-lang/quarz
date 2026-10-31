i = 0
sum = 0
while i < 120_000_000
  sum += i * 2 % 7
  i += 1
end
puts sum
