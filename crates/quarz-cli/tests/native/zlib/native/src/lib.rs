//! The zlib cog's native methods (`src/zlib.qz`).

use quarz_ext::{Call, Result, Value};

fn deflate<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let data = cx.get_bytes(a[0])?;
    let level = cx.get_int(a[1])?;
    if !(0..=10).contains(&level) {
        return Err(cx.raise("ArgumentError", "the level is 0 to 10"));
    }
    Ok(cx.bytes(&miniz_oxide::deflate::compress_to_vec_zlib(data, level as u8)))
}

fn inflate<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    let data = cx.get_bytes(a[0])?;
    match miniz_oxide::inflate::decompress_to_vec_zlib(data) {
        Ok(out) => Ok(cx.bytes(&out)),
        Err(_) => Err(cx.raise("Zlib::DataError", "not in the zlib format")),
    }
}

fn crc32<'c>(cx: &Call<'c>, _: Value<'c>, a: &[Value<'c>]) -> Result<Value<'c>> {
    Ok(cx.int(i64::from(crc32fast::hash(cx.get_bytes(a[0])?))))
}

quarz_ext::module! {
    cog: "zlib",
    "Zlib::Codec.deflate" => deflate,
    "Zlib::Codec.inflate" => inflate,
    "Zlib::Codec.crc32" => crc32,
}
