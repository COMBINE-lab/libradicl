/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! This module contains macros used by `libradicl`. These are
//! mostly intended for internal use.

#[macro_export]
macro_rules! u8_to_vec_of {
    ($a:expr, $b:ty) => {
        $a.chunks_exact(std::mem::size_of::<$b>())
            .map(TryInto::try_into)
            .map(Result::unwrap)
            .map(<$b>::from_le_bytes)
            .collect()
    };
}

#[macro_export]
macro_rules! u8_to_vec_of_bool {
    ($a:expr) => {
        $a.iter().map(|x| *x > 0).collect::<Vec<bool>>()
    };
}

#[macro_export]
macro_rules! write_tag_value_array {
    ($v:ident , $len_t:expr, $val_t: ty, $slice_name: ident, $writer:expr, $policy:expr) => {
        // How many elements the declared length type can actually address. Both
        // the length field *and* the payload are bounded by it: writing one
        // without the other is what leaves a reader parsing the next tag from the
        // middle of this one.
        let max_len: usize = match $len_t {
            RadIntId::U8 => u8::MAX as usize,
            RadIntId::U16 => u16::MAX as usize,
            RadIntId::U32 => u32::MAX as usize,
            // A `usize` can never exceed these, so no bound is needed.
            RadIntId::U64 | RadIntId::U128 => usize::MAX,
            _ => {
                anyhow::bail!("signed length values are unsupported in tag value arrays")
            }
        };
        let n: usize = if $v.len() > max_len {
            match $policy {
                $crate::rad_types::OversizedValuePolicy::Error => anyhow::bail!(
                    "array tag value has {} elements, more than the {} a {:?} length \
                     can address; either declare a wider length type or allow truncation",
                    $v.len(),
                    max_len,
                    $len_t
                ),
                $crate::rad_types::OversizedValuePolicy::Truncate => max_len,
            }
        } else {
            $v.len()
        };
        // `n <= max_len` now, so every cast below is exact rather than wrapping.
        match $len_t {
            RadIntId::U8 => {
                let l: u8 = n as u8;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u8")?;
            }
            RadIntId::U16 => {
                let l: u16 = n as u16;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u16")?;
            }
            RadIntId::U32 => {
                let l: u32 = n as u32;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u32")?;
            }
            RadIntId::U64 => {
                let l: u64 = n as u64;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u64")?;
            }
            RadIntId::U128 => {
                let l: u128 = n as u128;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u128")?;
            }
            _ => {
                anyhow::bail!("signed length values are unsupported in tag value arrays")
            }
        }
        // Bound the payload to match the length just written.
        let $slice_name: &[u8] = bytemuck::try_cast_slice(&$v[..n])
            .or_else(|_e| Err(anyhow::anyhow!("could't convert array contents to &[u8]")))
            .context("array conversion failed")?;
        $writer
            .write_all($slice_name)
            .context("couldn't write values of the array")?;
    };
}

#[macro_export]
macro_rules! tag_value_try_into_int {
    ($b:ty) => {
        /// allow converting a [libradicl::rad_types::TagValue] into
        /// an appropriate integer type. This fails
        /// if the value contained is too big to fit
        /// in the corresponidng type.
        impl std::convert::TryInto<$b> for &libradicl::rad_types::TagValue {
            type Error = anyhow::Error;

            fn try_into(self) -> std::result::Result<$b, Self::Error> {
                match *self {
                    TagValue::U8(x) => Ok(x as $b),
                    TagValue::U16(x) => Ok(x as $b),
                    TagValue::U32(x) => {
                        if x as u64 > <$b>::MAX as u64 {
                            bail!("Cannot convert value {x} to u16; too large")
                        } else {
                            Ok(x as $b)
                        }
                    }
                    TagValue::U64(x) => {
                        if x as u64 > <$b>::MAX as u64 {
                            bail!("Cannot convert value {x} to {}; too large", stringify!($b))
                        } else {
                            Ok(x as $b)
                        }
                    }
                    TagValue::U128(x) => {
                        if x as u128 > <$b>::MAX as u128 {
                            bail!("Cannot convert value {x} to {}; too large", stringify!($b))
                        } else {
                            Ok(x as $b)
                        }
                    }
                    TagValue::I8(x) => Ok(x as $b),
                    TagValue::I16(x) => Ok(x as $b),
                    TagValue::I32(x) => {
                        if x as i64 > <$b>::MAX as i64 {
                            bail!("Cannot convert value {x} to i16; too large")
                        } else if (x as i64) < <$b>::MIN as i64 {
                            bail!("Cannot convert value {x} to i16; too small")
                        } else {
                            Ok(x as $b)
                        }
                    }
                    TagValue::I64(x) => {
                        if x as i64 > <$b>::MAX as i64 {
                            bail!("Cannot convert value {x} to {}; too large", stringify!($b))
                        } else if (x as i64) < <$b>::MIN as i64 {
                            bail!("Cannot convert value {x} to i32; too small")
                        } else {
                            Ok(x as $b)
                        }
                    }
                    TagValue::I128(x) => {
                        if x as i128 > <$b>::MAX as i128 {
                            bail!("Cannot convert value {x} to {}; too large", stringify!($b))
                        } else if (x as i128) < <$b>::MIN as i128 {
                            bail!("Cannot convert value {x} to {}; too small", stringify!($b))
                        } else {
                            Ok(x as $b)
                        }
                    }
                    _ => {
                        bail!("cannot convert non-int TagValue to {}", stringify!($b))
                    }
                }
            }
        }
    };
}

/// Convert from an underlying newtype (e.g. a [crate::libradicl::io::NewU8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewU64], [crate::libradicl::io::NewU128]) into a native [u64]. Note that
/// conversion from a [crate::libradicl::io::NewU128] will [panic!] as the underlying native type
/// is too narrow to hold the contents of the integer.
#[macro_export]
macro_rules! as_u64 {
    ("NewU128") => {
        impl std::convert::From<$from_type> for u64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                panic!("cannot convert u128 into u64");
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for u64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as u64
            }
        }
    };
}

/// Convert from an underlying newtype (e.g. a [crate::libradicl::io::NewI8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewI64], [crate::libradicl::io::NewU128]) into a native [u64]. Note that
/// conversion from a [crate::libradicl::io::NewI128] will [panic!] as the underlying native type
/// is too narrow to hold the contents of the integer.
#[macro_export]
macro_rules! as_i64 {
    ("NewI128") => {
        impl std::convert::From<$from_type> for i64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                panic!("cannot convert i128 into i64");
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for i64 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as i64
            }
        }
    };
}

/// Convert from an underlying newtype (e.g. a [crate::libradicl::io::NewU8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewU64], [crate::libradicl::io::NewU128]) into a native [u128].
#[macro_export]
macro_rules! as_u128 {
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for u128 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as u128
            }
        }
    };
}

/// Convert from an underlying newtype (e.g. a [crate::libradicl::io::NewI8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewI64], [crate::libradicl::io::NewU128]) into a native [u128].
#[macro_export]
macro_rules! as_i128 {
    ($from_type: ty) => {
        impl std::convert::From<$from_type> for i128 {
            #[inline(always)]
            fn from(x: $from_type) -> Self {
                x.0 as i128
            }
        }
    };
}

/// Try to convert from an underlying newtype (e.g. a [crate::libradicl::io::NewU8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewU64], [crate::libradicl::io::NewU128]) into a native [u64]. If the
/// conversion is successful, we produce an [Ok]\([u64]\), otherwise we produce an
/// [std::result::Result::Err].
#[macro_export]
macro_rules! try_as_u64 {
    ("NewU128") => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Err("Cannot convert u128 into u64")
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0.0 as u64)
            }
        }
    };
}

/// Try to convert from an underlying newtype (e.g. a [crate::libradicl::io::NewI8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewI64], [crate::libradicl::io::NewU128]) into a native [u64]. If the
/// conversion is successful, we produce an [Ok]\([u64]\), otherwise we produce an
/// [std::result::Result::Err].
#[macro_export]
macro_rules! try_as_i64 {
    ("NewI128") => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for i64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Err("Cannot convert i128 into i64")
            }
        }
    };
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for i64 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0.0 as i64)
            }
        }
    };
}

/// Try to convert from an underlying newtype (e.g. a [crate::libradicl::io::NewU8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewU64], [crate::libradicl::io::NewU128]) into a native [u128]. If the
/// conversion is successful, we produce an [Ok]\([u128]\), otherwise we produce an [std::result::Result::Err].
#[macro_export]
macro_rules! try_as_u128 {
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for u128 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0.0 as u128)
            }
        }
    };
}

/// Try to convert from an underlying newtype (e.g. a [crate::libradicl::io::NewI8], [crate::libradicl::io::NewU16], [crate::libradicl::io::NewU32],
/// [crate::libradicl::io::NewI64], [crate::libradicl::io::NewU128]) into a native [u128]. If the
/// conversion is successful, we produce an [Ok]\([u128]\), otherwise we produce an [std::result::Result::Err].
#[macro_export]
macro_rules! try_as_i128 {
    ($from_type: ty) => {
        impl std::convert::TryFrom<TryWrapper<$from_type>> for i128 {
            type Error = &'static str;
            #[inline(always)]
            fn try_from(x: TryWrapper<$from_type>) -> Result<Self, Self::Error> {
                Ok(x.0.0 as i128)
            }
        }
    };
}
