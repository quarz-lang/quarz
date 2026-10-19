//! Time (a point in time with a UTC offset) and the Duration helpers that
//! need the clock.

use std::collections::HashMap;
use std::fmt::Write as _;
use std::rc::Rc;

use chrono::{
    DateTime, Datelike, FixedOffset, Local, LocalResult, Offset, TimeZone, Timelike, Utc,
};

use crate::interp::{Args, EvalResult, Flow, Interp, NativeFn};
use crate::value::*;

use super::{float, int, string};

const NS: i64 = 1_000_000_000;

pub fn register(m: &mut HashMap<&'static str, NativeFn>) {
    m.insert("Time.now", |_, _, _| {
        let now = Local::now();
        Ok(time(
            now.timestamp_nanos_opt().unwrap_or(0),
            now.offset().local_minus_utc(),
            false,
        ))
    });
    m.insert("Time.at", |i, _, a| {
        let ns = match a.arg(0) {
            Value::Int(s) => s
                .checked_mul(NS)
                .ok_or_else(|| i.raise(i.exc.range_error, "time out of range"))?,
            v => (float(i, v, "seconds")? * NS as f64).round() as i64,
        };
        Ok(at_local(ns))
    });
    m.insert("Time.utc", |i, _, a| make(i, &a, true));
    m.insert("Time.local", |i, _, a| make(i, &a, false));
    m.insert("Time.parse", |i, _, a| {
        let text = string(i, a.arg(0), "text")?;
        parse(text.trim())
            .map(|(ns, off, utc)| time(ns, off, utc))
            .ok_or_else(|| i.err_arg(&format!("no time information in {:?}", &*text)))
    });
    m.insert("Time.iso8601", |i, _, a| {
        let text = string(i, a.arg(0), "text")?;
        match DateTime::parse_from_rfc3339(text.trim()) {
            Ok(dt) => Ok(from_datetime(&dt, text.trim().ends_with('Z'))),
            Err(_) => Err(i.err_arg(&format!("invalid ISO 8601 time {:?}", text))),
        }
    });
    m.insert("Time.monotonic", |_, _, _| {
        thread_local! { static START: std::time::Instant = std::time::Instant::now(); }
        Ok(Value::Duration(START.with(|s| {
            s.elapsed().as_nanos().min(i64::MAX as u128) as i64
        })))
    });

    m.insert("Time#year", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.year() as i64))
    });
    m.insert("Time#month", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.month() as i64))
    });
    m.insert("Time#day", |i, r, _| Ok(Value::Int(dt(i, r)?.day() as i64)));
    m.insert("Time#hour", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.hour() as i64))
    });
    m.insert("Time#min", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.minute() as i64))
    });
    m.insert("Time#sec", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.second() as i64))
    });
    m.insert("Time#nsec", |i, r, _| {
        Ok(Value::Int(tv(i, r)?.ns.rem_euclid(NS)))
    });
    m.insert("Time#usec", |i, r, _| {
        Ok(Value::Int(tv(i, r)?.ns.rem_euclid(NS) / 1000))
    });
    m.insert("Time#wday", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.weekday().num_days_from_sunday() as i64))
    });
    m.insert("Time#yday", |i, r, _| {
        Ok(Value::Int(dt(i, r)?.ordinal() as i64))
    });
    for (name, wday) in [
        ("sunday?", 0),
        ("monday?", 1),
        ("tuesday?", 2),
        ("wednesday?", 3),
        ("thursday?", 4),
        ("friday?", 5),
        ("saturday?", 6),
    ] {
        let key: &'static str = Box::leak(format!("Time#{name}").into_boxed_str());
        let f: NativeFn = match wday {
            0 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 0)),
            1 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 1)),
            2 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 2)),
            3 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 3)),
            4 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 4)),
            5 => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 5)),
            _ => |i, r, _| Ok(Value::Bool(dt(i, r)?.weekday().num_days_from_sunday() == 6)),
        };
        m.insert(key, f);
    }
    m.insert("Time#to_i", |i, r, _| {
        Ok(Value::Int(tv(i, r)?.ns.div_euclid(NS)))
    });
    m.insert("Time#to_f", |i, r, _| {
        Ok(Value::Float(tv(i, r)?.ns as f64 / NS as f64))
    });
    m.insert("Time#+", |i, r, a| {
        let t = tv(i, r)?;
        let d = dur(i, a.arg(0))?;
        let ns =
            t.ns.checked_add(d)
                .ok_or_else(|| i.raise(i.exc.range_error, "time out of range"))?;
        Ok(time(ns, t.offset, t.utc))
    });
    m.insert("Time#-", |i, r, a| {
        let t = tv(i, r)?;
        match a.arg(0) {
            Value::Time(o) => Ok(Value::Duration(t.ns - o.ns)),
            v => {
                let d = dur(i, v)?;
                let ns =
                    t.ns.checked_sub(d)
                        .ok_or_else(|| i.raise(i.exc.range_error, "time out of range"))?;
                Ok(time(ns, t.offset, t.utc))
            }
        }
    });
    m.insert("Time#<=>", |i, r, a| {
        Ok(Value::Int(tv(i, r)?.ns.cmp(&tv(i, a.arg(0))?.ns) as i64))
    });
    m.insert("Time#==", |i, r, a| {
        Ok(Value::Bool(
            matches!(a.arg(0), Value::Time(o) if o.ns == tv(i, r)?.ns),
        ))
    });
    m.insert("Time#hash", |i, r, _| Ok(Value::Int(tv(i, r)?.ns)));
    m.insert("Time#utc", |i, r, _| Ok(time(tv(i, r)?.ns, 0, true)));
    m.insert("Time#getlocal", |i, r, _| Ok(at_local(tv(i, r)?.ns)));
    m.insert("Time#localtime", |i, r, _| Ok(at_local(tv(i, r)?.ns)));
    m.insert("Time#utc?", |i, r, _| Ok(Value::Bool(tv(i, r)?.utc)));
    m.insert("Time#utc_offset", |i, r, _| {
        Ok(Value::Int(tv(i, r)?.offset as i64))
    });
    m.insert("Time#zone", |i, r, _| {
        let t = tv(i, r)?;
        Ok(Value::string(if t.utc {
            "UTC".to_string()
        } else {
            format_offset(t.offset, true)
        }))
    });
    m.insert("Time#strftime", |i, r, a| {
        let t = tv(i, r)?;
        let fmt = string(i, a.arg(0), "format")?;
        strftime(&t, fmt)
            .map(Value::string)
            .ok_or_else(|| i.err_arg(&format!("invalid strftime format {:?}", &*fmt)))
    });
    m.insert("Time#iso8601", |i, r, a| {
        let digits = match a.pos.first() {
            Some(v) => int(i, v, "fraction_digits")?.clamp(0, 9) as usize,
            None => 0,
        };
        Ok(Value::string(iso8601(&tv(i, r)?, digits)))
    });
    m.insert("Time#to_s", |i, r, _| {
        Ok(Value::string(time_to_s(&tv(i, r)?, false)))
    });
    m.insert("Time#inspect", |i, r, _| {
        Ok(Value::string(time_to_s(&tv(i, r)?, true)))
    });
}

fn time(ns: i64, offset: i32, utc: bool) -> Value {
    Value::Time(Rc::new(TimeVal { ns, offset, utc }))
}

fn tv(interp: &Interp, v: &Value) -> Result<TimeVal, Flow> {
    match v {
        Value::Time(t) => Ok(**t),
        _ => Err(interp.err_type(&format!("expected a Time, got {}", interp.class_name(v)))),
    }
}

fn dur(interp: &Interp, v: &Value) -> Result<i64, Flow> {
    match v {
        Value::Duration(d) => Ok(*d),
        _ => Err(interp.err_type(&format!(
            "expected a Duration, got {}",
            interp.class_name(v)
        ))),
    }
}

fn dt(interp: &Interp, v: &Value) -> Result<DateTime<FixedOffset>, Flow> {
    Ok(to_datetime(&tv(interp, v)?))
}

pub fn to_datetime(t: &TimeVal) -> DateTime<FixedOffset> {
    let secs = t.ns.div_euclid(NS);
    let nsec = t.ns.rem_euclid(NS) as u32;
    let utc = DateTime::<Utc>::from_timestamp(secs, nsec).unwrap_or_default();
    utc.with_timezone(
        &FixedOffset::east_opt(t.offset).unwrap_or_else(|| FixedOffset::east_opt(0).unwrap()),
    )
}

fn from_datetime<Tz: TimeZone>(dt: &DateTime<Tz>, utc: bool) -> Value {
    time(
        dt.timestamp_nanos_opt().unwrap_or(0),
        dt.offset().fix().local_minus_utc(),
        utc,
    )
}

/// The instant `ns` in the local time zone.
pub(super) fn at_local(ns: i64) -> Value {
    let secs = ns.div_euclid(NS);
    let nsec = ns.rem_euclid(NS) as u32;
    let offset = match Local.timestamp_opt(secs, nsec) {
        LocalResult::Single(dt) | LocalResult::Ambiguous(dt, _) => dt.offset().local_minus_utc(),
        LocalResult::None => Local::now().offset().local_minus_utc(),
    };
    time(ns, offset, false)
}

/// `Time.utc(year, month = 1, day = 1, hour = 0, min = 0, sec = 0)` and
/// `Time.local(...)`.
fn make(interp: &Interp, args: &Args, utc: bool) -> EvalResult {
    let mut parts = [0i64, 1, 1, 0, 0, 0];
    for (k, v) in args.pos.iter().enumerate().take(6) {
        parts[k] = int(interp, v, "time component")?;
    }
    let bad = || interp.err_arg("argument out of range");
    let year = i32::try_from(parts[0]).map_err(|_| bad())?;
    let [month, day, hour, min, sec] =
        [parts[1], parts[2], parts[3], parts[4], parts[5]].map(|p| u32::try_from(p).ok());
    let (Some(month), Some(day), Some(hour), Some(min), Some(sec)) = (month, day, hour, min, sec)
    else {
        return Err(bad());
    };
    if utc {
        match Utc.with_ymd_and_hms(year, month, day, hour, min, sec) {
            LocalResult::Single(dt) => Ok(from_datetime(&dt, true)),
            _ => Err(bad()),
        }
    } else {
        match Local.with_ymd_and_hms(year, month, day, hour, min, sec) {
            LocalResult::Single(dt) | LocalResult::Ambiguous(dt, _) => {
                Ok(from_datetime(&dt, false))
            }
            LocalResult::None => Err(bad()),
        }
    }
}

/// Parse the common written forms: RFC 3339, `YYYY-MM-DD HH:MM:SS[.frac]
/// [+HH:MM|+HHMM|UTC|Z]`, `YYYY-MM-DD HH:MM[:SS]` and `YYYY-MM-DD` (the
/// latter two in local time).
fn parse(text: &str) -> Option<(i64, i32, bool)> {
    if let Ok(dt) = DateTime::parse_from_rfc3339(text) {
        return Some((
            dt.timestamp_nanos_opt()?,
            dt.offset().local_minus_utc(),
            text.ends_with('Z'),
        ));
    }
    let normalized = text.replacen('T', " ", 1);
    let utc_suffix = normalized.ends_with(" UTC") || normalized.ends_with('Z');
    let normalized = normalized
        .trim_end_matches(" UTC")
        .trim_end_matches('Z')
        .to_string();
    let normalized = if utc_suffix {
        format!("{normalized} +0000")
    } else {
        normalized
    };
    for fmt in [
        "%Y-%m-%d %H:%M:%S%.f %z",
        "%Y-%m-%d %H:%M:%S %z",
        "%Y-%m-%d %H:%M %z",
    ] {
        if let Ok(dt) = DateTime::parse_from_str(&normalized, fmt) {
            return Some((
                dt.timestamp_nanos_opt()?,
                dt.offset().local_minus_utc(),
                utc_suffix,
            ));
        }
    }
    for fmt in [
        "%Y-%m-%d %H:%M:%S%.f",
        "%Y-%m-%d %H:%M:%S",
        "%Y-%m-%d %H:%M",
    ] {
        if let Ok(naive) = chrono::NaiveDateTime::parse_from_str(&normalized, fmt) {
            return local_naive(naive);
        }
    }
    if let Ok(date) = chrono::NaiveDate::parse_from_str(&normalized, "%Y-%m-%d") {
        return local_naive(date.and_hms_opt(0, 0, 0)?);
    }
    None
}

fn local_naive(naive: chrono::NaiveDateTime) -> Option<(i64, i32, bool)> {
    let dt = match Local.from_local_datetime(&naive) {
        LocalResult::Single(dt) | LocalResult::Ambiguous(dt, _) => dt,
        LocalResult::None => return None,
    };
    Some((
        dt.timestamp_nanos_opt()?,
        dt.offset().local_minus_utc(),
        false,
    ))
}

fn format_offset(offset: i32, colon: bool) -> String {
    let sign = if offset < 0 { '-' } else { '+' };
    let abs = offset.abs();
    if colon {
        format!("{sign}{:02}:{:02}", abs / 3600, abs % 3600 / 60)
    } else {
        format!("{sign}{:02}{:02}", abs / 3600, abs % 3600 / 60)
    }
}

/// Ruby's `Time#to_s` / `#inspect`: `2026-10-19 12:34:56 +0900`, with
/// the fractional seconds shown by `inspect` when they are not zero.
pub fn time_to_s(t: &TimeVal, inspect: bool) -> String {
    let dt = to_datetime(t);
    let mut out = dt.format("%Y-%m-%d %H:%M:%S").to_string();
    let frac = t.ns.rem_euclid(NS);
    if inspect && frac != 0 {
        let digits = format!("{frac:09}");
        out.push('.');
        out.push_str(digits.trim_end_matches('0'));
    }
    out.push(' ');
    if t.utc {
        out.push_str("UTC");
    } else {
        out.push_str(&format_offset(t.offset, false));
    }
    out
}

fn iso8601(t: &TimeVal, digits: usize) -> String {
    let dt = to_datetime(t);
    let mut out = dt.format("%Y-%m-%dT%H:%M:%S").to_string();
    if digits > 0 {
        let frac = format!("{:09}", t.ns.rem_euclid(NS));
        out.push('.');
        out.push_str(&frac[..digits]);
    }
    if t.utc {
        out.push('Z');
    } else {
        out.push_str(&format_offset(t.offset, true));
    }
    out
}

/// Ruby-style strftime on top of chrono's: `%L` (milliseconds), `%N`
/// (nanoseconds, `%3N`/`%6N`/`%9N`) and `%Z` for UTC are translated.
fn strftime(t: &TimeVal, fmt: &str) -> Option<String> {
    let dt = to_datetime(t);
    let mut translated = String::with_capacity(fmt.len());
    let mut chars = fmt.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '%' {
            translated.push(c);
            continue;
        }
        let mut width = String::new();
        while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
            width.push(*d);
            chars.next();
        }
        match chars.next() {
            Some('L') => translated.push_str("%3f"),
            Some('N') => {
                let n = width.parse::<usize>().unwrap_or(9).clamp(1, 9);
                let _ = write!(translated, "%{n}f");
            }
            Some('Z') if t.utc => translated.push_str("UTC"),
            Some('Z') => translated.push_str("%:z"),
            Some(other) => {
                translated.push('%');
                translated.push_str(&width);
                translated.push(other);
            }
            None => translated.push('%'),
        }
    }
    let mut out = String::new();
    write!(out, "{}", dt.format(&translated)).ok()?;
    Some(out)
}
