//! Semantic versions, version tags and pseudo-versions.

use std::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Version {
    pub major: u64,
    pub minor: u64,
    pub patch: u64,
    /// Pre-release identifiers (`1.0.0-beta.2` → `["beta", "2"]`).
    pub pre: Vec<String>,
}

impl Version {
    pub fn new(major: u64, minor: u64, patch: u64) -> Version {
        Version {
            major,
            minor,
            patch,
            pre: Vec::new(),
        }
    }

    /// `MAJOR.MINOR.PATCH[-PRE]` (build metadata after `+` is ignored).
    pub fn parse(s: &str) -> Option<Version> {
        let s = s.split('+').next()?;
        let (core, pre) = match s.split_once('-') {
            Some((c, p)) => (c, Some(p)),
            None => (s, None),
        };
        let mut parts = core.split('.');
        let num = |p: Option<&str>| -> Option<u64> {
            let p = p?;
            if p.is_empty()
                || !p.bytes().all(|b| b.is_ascii_digit())
                || (p.len() > 1 && p.starts_with('0'))
            {
                return None;
            }
            p.parse().ok()
        };
        let major = num(parts.next())?;
        let minor = num(parts.next())?;
        let patch = num(parts.next())?;
        if parts.next().is_some() {
            return None;
        }
        let pre = match pre {
            Some(p) => {
                let ids: Vec<String> = p.split('.').map(str::to_string).collect();
                if ids.iter().any(|i| {
                    i.is_empty() || !i.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
                }) {
                    return None;
                }
                ids
            }
            None => Vec::new(),
        };
        Some(Version {
            major,
            minor,
            patch,
            pre,
        })
    }

    /// A version tag: `vMAJOR.MINOR.PATCH[-PRE]`.
    pub fn parse_tag(tag: &str) -> Option<Version> {
        Version::parse(tag.strip_prefix('v')?)
    }

    pub fn tag(&self) -> String {
        format!("v{self}")
    }

    /// The version of a commit that no tag names: the patch after `base`
    /// (the nearest version tag among its ancestors), a `0` that sorts it
    /// below any real pre-release of that patch, the commit time (UTC,
    /// seconds since the epoch) and twelve digits of the commit id. After a
    /// pre-release tag, the pre-release is kept and `.0.TIME.REV` added.
    pub fn pseudo(base: Option<&Version>, time: u64, rev: &str) -> Version {
        let stamp = utc_stamp(time);
        let short: String = rev.chars().take(12).collect();
        match base {
            None => Version {
                major: 0,
                minor: 0,
                patch: 0,
                pre: vec!["0".into(), stamp, short],
            },
            Some(b) if !b.pre.is_empty() => {
                let mut pre = b.pre.clone();
                pre.extend(["0".to_string(), stamp, short]);
                Version { pre, ..b.clone() }
            }
            Some(b) => Version {
                major: b.major,
                minor: b.minor,
                // A patch of u64::MAX has no next one; the pseudo-version
                // then sorts with it rather than overflowing.
                patch: b.patch.saturating_add(1),
                pre: vec!["0".into(), stamp, short],
            },
        }
    }

    /// Whether two versions may be unified to the higher one: the same
    /// major, and while the major is 0, the same minor.
    pub fn compatible(&self, other: &Version) -> bool {
        self.major == other.major && (self.major != 0 || self.minor == other.minor)
    }
}

impl std::fmt::Display for Version {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if !self.pre.is_empty() {
            write!(f, "-{}", self.pre.join("."))?;
        }
        Ok(())
    }
}

impl Ord for Version {
    fn cmp(&self, other: &Version) -> Ordering {
        (self.major, self.minor, self.patch)
            .cmp(&(other.major, other.minor, other.patch))
            .then_with(|| match (self.pre.is_empty(), other.pre.is_empty()) {
                (true, true) => Ordering::Equal,
                (true, false) => Ordering::Greater,
                (false, true) => Ordering::Less,
                (false, false) => cmp_pre(&self.pre, &other.pre),
            })
    }
}

impl PartialOrd for Version {
    fn partial_cmp(&self, other: &Version) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Semantic versioning's precedence of pre-release identifiers: numeric
/// ones compare as numbers and below alphanumeric ones, and a longer list
/// sorts after its prefix.
fn cmp_pre(a: &[String], b: &[String]) -> Ordering {
    for (x, y) in a.iter().zip(b) {
        let nx = x.bytes().all(|c| c.is_ascii_digit());
        let ny = y.bytes().all(|c| c.is_ascii_digit());
        let o = match (nx, ny) {
            (true, true) => x.len().cmp(&y.len()).then_with(|| x.cmp(y)),
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => x.cmp(y),
        };
        if o != Ordering::Equal {
            return o;
        }
    }
    a.len().cmp(&b.len())
}

/// `YYYYMMDDhhmmss` in UTC.
fn utc_stamp(secs: u64) -> String {
    let days = (secs / 86400) as i64;
    let rem = secs % 86400;
    // Howard Hinnant's civil-from-days.
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    format!(
        "{year:04}{month:02}{day:02}{:02}{:02}{:02}",
        rem / 3600,
        rem % 3600 / 60,
        rem % 60
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn v(s: &str) -> Version {
        Version::parse(s).unwrap()
    }

    #[test]
    fn parses() {
        assert_eq!(v("1.4.0"), Version::new(1, 4, 0));
        assert_eq!(v("1.0.0-beta.2").pre, vec!["beta", "2"]);
        assert_eq!(Version::parse_tag("v2.0.1"), Some(Version::new(2, 0, 1)));
        assert!(Version::parse("1.4").is_none());
        assert!(Version::parse("01.4.0").is_none());
        assert!(Version::parse_tag("2.0.1").is_none());
    }

    #[test]
    fn orders_as_semver() {
        let order = [
            "1.0.0-alpha",
            "1.0.0-alpha.1",
            "1.0.0-alpha.beta",
            "1.0.0-beta",
            "1.0.0-beta.2",
            "1.0.0-beta.11",
            "1.0.0-rc.1",
            "1.0.0",
            "1.0.1-0.20261023141500.3f2a9c1e0b4d",
            "1.0.1",
        ];
        for w in order.windows(2) {
            assert!(v(w[0]) < v(w[1]), "{} < {}", w[0], w[1]);
        }
    }

    #[test]
    fn pseudo_versions() {
        // 2026-10-23 14:15:00 UTC
        let t = 1_792_764_900;
        let rev = "3f2a9c1e0b4d7c6e8a1f2b3c4d5e6f7a8b9c0d1e";
        assert_eq!(
            Version::pseudo(Some(&v("1.4.0")), t, rev).to_string(),
            "1.4.1-0.20261023141500.3f2a9c1e0b4d"
        );
        assert_eq!(
            Version::pseudo(None, t, rev).to_string(),
            "0.0.0-0.20261023141500.3f2a9c1e0b4d"
        );
        assert_eq!(
            Version::pseudo(Some(&v("2.0.0-rc.1")), t, rev).to_string(),
            "2.0.0-rc.1.0.20261023141500.3f2a9c1e0b4d"
        );
        let p = Version::pseudo(Some(&v("1.4.0")), t, rev);
        assert!(v("1.4.0") < p && p < v("1.4.1-alpha") && p < v("1.4.1"));
    }

    #[test]
    fn compatibility() {
        assert!(v("1.2.0").compatible(&v("1.9.3")));
        assert!(!v("1.2.0").compatible(&v("2.0.0")));
        assert!(v("0.3.1").compatible(&v("0.3.9")));
        assert!(!v("0.3.1").compatible(&v("0.4.0")));
    }
}
