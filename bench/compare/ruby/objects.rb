Vec2 = Data.define(:x, :y) do
  def +(o) = Vec2.new(x + o.x, y + o.y)
  def scale(k) = Vec2.new(x * k, y * k)
end
class Particle
  attr_reader :pos
  def initialize(pos, vel)
    @pos = pos
    @vel = vel
  end
  def step(dt)
    @pos = @pos + @vel.scale(dt)
  end
end
ps = Array.new(1000) { |i| Particle.new(Vec2.new(i.to_f, 0.0), Vec2.new(1.0, 0.5)) }
300.times { ps.each { |p| p.step(0.01) } }
puts ps[0].pos.x.round(2)
