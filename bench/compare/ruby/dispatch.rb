class Shape
  def area = 0.0
end
class Circle < Shape
  def initialize(r)
    @r = r
  end
  def area = 3.0 * @r * @r
end
class Rect < Shape
  def initialize(w, h)
    @w = w
    @h = h
  end
  def area = @w * @h
end
class Tri < Shape
  def initialize(b, h)
    @b = b
    @h = h
  end
  def area = 0.5 * @b * @h
end
shapes = []
300.times do |i|
  shapes.push(Circle.new(i.to_f))
  shapes.push(Rect.new(i.to_f, 2.0))
  shapes.push(Tri.new(i.to_f, 3.0))
end
total = 0.0
50_000.times { shapes.each { |s| total += s.area } }
puts total.round(1)
