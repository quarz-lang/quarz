//! `quarz cog`: managing the cogs (packages) of the application around the
//! current directory (see docs/10-cogs.md).

use std::path::PathBuf;
use std::process::ExitCode;

use quarz_cog::{AddRequest, Options};

fn fail(message: impl std::fmt::Display) -> ExitCode {
    eprintln!("quarz: {message}");
    ExitCode::FAILURE
}

fn root() -> Result<PathBuf, ExitCode> {
    let here = std::env::current_dir().map_err(fail)?;
    quarz_cog::find_root(&here)
        .ok_or_else(|| fail("no Cog.toml here or above (`quarz cog init` writes one)"))
}

/// The options every subcommand accepts, taken out of `args`.
fn options(args: &mut Vec<String>) -> Options {
    let mut opts = Options {
        verbose: true,
        ..Default::default()
    };
    args.retain(|a| match a.as_str() {
        "--locked" => {
            opts.locked = true;
            false
        }
        "--offline" => {
            opts.offline = true;
            false
        }
        _ => true,
    });
    opts
}

/// The value of `--name VALUE` in `args`, taken out.
fn take_value(args: &mut Vec<String>, flag: &str) -> Result<Option<String>, ExitCode> {
    let Some(i) = args.iter().position(|a| a == flag) else {
        return Ok(None);
    };
    if i + 1 >= args.len() {
        return Err(fail(format!("{flag} needs a value")));
    }
    let value = args.remove(i + 1);
    args.remove(i);
    Ok(Some(value))
}

pub fn command(args: &[String]) -> ExitCode {
    let mut args = args.to_vec();
    if args.is_empty() {
        return fail("`quarz cog` needs a command: init, add, update, fetch, vendor, tree, outdated or verify");
    }
    let sub = args.remove(0);
    let opts = options(&mut args);
    match run(&sub, args, opts) {
        Ok(code) => code,
        Err(code) => code,
    }
}

fn run(sub: &str, mut args: Vec<String>, opts: Options) -> Result<ExitCode, ExitCode> {
    match sub {
        "init" => {
            let dir = std::env::current_dir().map_err(fail)?;
            let name = quarz_cog::init(&dir).map_err(fail)?;
            println!("wrote Cog.toml for `{name}` (src/main.qz is the application's main file)");
        }
        "add" => {
            let tag = take_value(&mut args, "--tag")?;
            let rev = take_value(&mut args, "--rev")?;
            let key = take_value(&mut args, "--as")?;
            let subdir = take_value(&mut args, "--subdir")?;
            let dev = args.iter().any(|a| a == "--dev");
            args.retain(|a| a != "--dev");
            if tag.is_some() && rev.is_some() {
                return Err(fail("give --tag or --rev, not both"));
            }
            let [url] = args.as_slice() else {
                return Err(fail("usage: quarz cog add URL [--tag vX.Y.Z | --rev COMMIT] [--as KEY] [--subdir DIR] [--dev]"));
            };
            let root = root()?;
            let req = AddRequest {
                url: url.clone(),
                tag,
                rev,
                key,
                subdir,
                dev,
            };
            let (key, what) = quarz_cog::add(&root, &req, &opts).map_err(fail)?;
            let table = if dev {
                "dev-dependencies"
            } else {
                "dependencies"
            };
            println!("added `{key}` to [{table}] ({what})");
        }
        "update" => {
            let root = root()?;
            let opts = Options {
                refresh: true,
                ..opts
            };
            let movement = quarz_cog::open(&root, &opts).map_err(fail)?;
            print!("{}", quarz_cog::tree(&movement));
        }
        "fetch" => {
            let root = root()?;
            let movement = quarz_cog::open(&root, &opts).map_err(fail)?;
            println!("{} cog(s) fetched and verified", movement.cogs.len() - 1);
        }
        "vendor" => {
            let root = root()?;
            let n = quarz_cog::vendor(&root, &opts).map_err(fail)?;
            println!("copied {n} cog(s) into vendor/");
        }
        "tree" => {
            let root = root()?;
            let movement = quarz_cog::open(&root, &opts).map_err(fail)?;
            print!("{}", quarz_cog::tree(&movement));
        }
        "outdated" => {
            let root = root()?;
            let movement = quarz_cog::open(&root, &opts).map_err(fail)?;
            let list = quarz_cog::outdated(&movement).map_err(fail)?;
            if list.is_empty() {
                println!("every cog is at its newest version tag");
            }
            for (name, locked, newest) in list {
                println!("{name}: {locked} locked, {newest} available");
            }
        }
        "verify" => {
            let root = root()?;
            let problems = quarz_cog::verify(&root).map_err(fail)?;
            if problems.is_empty() {
                println!("every cog matches Cog.lock");
            } else {
                for p in &problems {
                    eprintln!("quarz: {p}");
                }
                return Ok(ExitCode::FAILURE);
            }
        }
        other => return Err(fail(format!("unknown cog command `{other}`"))),
    }
    Ok(ExitCode::SUCCESS)
}
