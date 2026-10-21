def tak(x, y, z)
  return z if y >= x
  tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y))
end
n = ARGV[0].to_i
puts tak(n * 3, n * 2, n)
