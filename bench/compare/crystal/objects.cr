struct Vec2
  getter x : Float64
  getter y : Float64
  def initialize(@x : Float64, @y : Float64); end
  def +(o : Vec2) : Vec2
    Vec2.new(x + o.x, y + o.y)
  end
  def scale(k : Float64) : Vec2
    Vec2.new(x * k, y * k)
  end
end
class Particle
  getter pos : Vec2
  def initialize(@pos : Vec2, @vel : Vec2); end
  def step(dt : Float64) : Nil
    @pos = @pos + @vel.scale(dt)
  end
end
ps = Array.new(1000) { |i| Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5)) }
15_000.times { ps.each { |p| p.step(0.01) } }
puts ps[0].pos.x.round(2)
