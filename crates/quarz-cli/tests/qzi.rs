//! A unit's check taken out of one program and read back into another
//! (`quarz_types::unit`, the `.qzi` of docs/05 §2) runs as if checked
//! there.

use quarz_syntax::{parse, SourceFile};
use quarz_types::load::unit_base;
use quarz_types::unit::{apply, extract, Target, UnitDelta};
use quarz_types::{Checked, PRELUDE_SOURCE};

struct Dir(std::path::PathBuf);

impl Dir {
    fn new(name: &str) -> Dir {
        let p = std::env::temp_dir().join(format!("quarz-qzi-{}-{name}", std::process::id()));
        std::fs::create_dir_all(&p).unwrap();
        Dir(p)
    }
    fn write(&self, name: &str, text: &str) {
        std::fs::write(self.0.join(name), text).unwrap();
    }
}

impl Drop for Dir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Load and check `path`: the checked program and its sources (prelude
/// first).
fn check(path: &std::path::Path) -> (Checked, Vec<SourceFile>) {
    let prelude = parse(PRELUDE_SOURCE);
    let (units, diags) = quarz_types::load(path);
    assert!(diags.iter().all(|(_, d)| !d.is_error()));
    let sources: Vec<SourceFile> = units.iter().map(|u| u.source.clone()).collect();
    let to_check: Vec<quarz_types::Unit> = units.into_iter().map(quarz_types::Unit::from).collect();
    let (checked, diags) = quarz_types::check_units(&prelude.program, &to_check);
    let errors: Vec<String> = diags
        .iter()
        .filter(|(_, d)| d.is_error())
        .map(|(_, d)| d.message.clone())
        .collect();
    assert!(errors.is_empty(), "{errors:?}");
    let mut files = vec![SourceFile::new("<prelude>", PRELUDE_SOURCE)];
    files.extend(sources);
    (checked.unwrap(), files)
}

fn run(checked: Checked, files: &[SourceFile]) -> String {
    let (code, out) = quarz_cli::run_capturing(checked, files, Vec::new());
    assert_eq!(code, 0, "{out}");
    out
}

const LIB: &str = r##"
module Shape
  abstract def area -> Float
  def describe -> String = "#{self.class} #{area}"
end
class Sq
  include Shape
  @s: Float
  attr_reader :s
  def initialize(@s: Float); end
  def area -> Float = @s * @s
end
data Pt = (x: Int, y: Int)
enum Res[T]
  variant Ok(v: T)
  variant Err(m: String)
end
class Box[T]
  @v: T
  def initialize(@v: T); end
  def get -> T = @v
  def map[U](&: (T) -> U) -> Box[U] = Box.new(yield(@v))
end
LIMIT = 10
"##;

const MAIN: &str = r##"
require_relative "lib"
class Big < Sq
  def area -> Float = super * 2.0
end
extension Pt
  def +(o: Pt) -> Pt = Pt.new(x + o.x, y + o.y)
end
def total(shapes: Array[Shape]) -> Float = shapes.sum { |s| s.area }
shapes: Array[Shape] = [Sq.new(2.0), Big.new(1.0)]
puts total(shapes), shapes.map(&:describe).join(", ")
p Pt.new(1, 2) + Pt.new(3, 4)
r: Res[Int] = Res::Ok.new(LIMIT)
case r
in Res::Ok(v) then puts v + 1
in Res::Err(m) then puts m
end
b = Box.new(3).map { |x| "#{x}!" }
puts b.get, Sq.new(3.0).s
"##;

#[test]
fn a_unit_read_back_into_another_program_runs_the_same() {
    let d = Dir::new("a");
    d.write("lib.qz", LIB);
    d.write("main.qz", MAIN);
    // Another file before the library shifts every number in the second
    // program.
    d.write(
        "other.qz",
        "class Other\n  def o -> Int = 1\nend\nOTHER = 2\n",
    );
    d.write(
        "shift.qz",
        "require_relative \"other\"\nrequire_relative \"lib\"\n",
    );
    let (whole, files) = check(&d.0.join("main.qz"));
    let expected = run(
        Checked {
            world: whole.world.clone(),
            output: whole.output.clone(),
            units: whole.units.clone(),
        },
        &files,
    );
    let name = |f: u32| -> String {
        whole
            .units
            .iter()
            .find(|u| u.file == f)
            .map(|u| u.name.clone())
            .unwrap_or_default()
    };
    let main = whole.units.last().unwrap().clone();
    let main_base = files[main.file as usize].base;
    let delta = extract(&whole.world, &whole.output, &[], &main, main_base, &name);
    let bytes = delta.encode();

    let (mut shifted, mut files2) = check(&d.0.join("shift.qz"));
    let names: Vec<(String, u32)> = shifted
        .units
        .iter()
        .map(|u| (u.name.clone(), u.file))
        .collect();
    let file = shifted.units.len() as u32 + 1;
    let base = unit_base(50);
    let main_name = main.name.clone();
    let lookup = |k: &str| -> Option<u32> {
        if k == main_name {
            return Some(file);
        }
        names.iter().find(|(n, _)| n == k).map(|(_, f)| *f)
    };
    let delta = UnitDelta::decode(&bytes, main_base, base).unwrap();
    let mut self_news = Vec::new();
    let unit = apply(
        &mut shifted.world,
        &mut shifted.output,
        &mut self_news,
        delta,
        &Target {
            files: &lookup,
            base,
        },
    )
    .expect("read back");
    shifted.units.push(unit);
    files2.push(SourceFile::with_base(main_name, MAIN, base));
    // (The numbers did move.)
    assert_ne!(whole.world.classes.len(), shifted.world.classes.len());
    assert_eq!(run(shifted, &files2), expected);
}
