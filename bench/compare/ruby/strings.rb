s = +""
1_200_000.times { |i| s << "item #{i}, " }
puts s.size
words = s.split(", ")
puts words.size, words.map(&:upcase).count { |w| w.end_with?("7") }
