abstract class Shape
  abstract def area : Float64
end
class Circle < Shape
  def initialize(@r : Float64); end
  def area : Float64
    3.0 * @r * @r
  end
end
class Rect < Shape
  def initialize(@w : Float64, @h : Float64); end
  def area : Float64
    @w * @h
  end
end
class Tri < Shape
  def initialize(@b : Float64, @h : Float64); end
  def area : Float64
    0.5 * @b * @h
  end
end
shapes = [] of Shape
300.times do |i|
  shapes << Circle.new(i.to_f)
  shapes << Rect.new(i.to_f, 2.0)
  shapes << Tri.new(i.to_f, 3.0)
end
total = 0.0
50_000.times { shapes.each { |s| total += s.area } }
puts total.round(1)
