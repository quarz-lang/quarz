s = String.build do |b|
  1_200_000.times { |i| b << "item #{i}, " }
end
puts s.size
words = s.split(", ")
words.pop if words.last? == ""
puts words.size
puts words.map(&.upcase).count { |w| w.ends_with?("7") }
