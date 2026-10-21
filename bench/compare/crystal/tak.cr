def tak(x : Int64, y : Int64, z : Int64) : Int64
  return z if y >= x
  tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y))
end
n = ARGV[0].to_i64
puts tak(n * 3, n * 2, n)
