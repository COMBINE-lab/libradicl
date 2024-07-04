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
    ($v:ident , $len_t:expr, $val_t: ty, $slice_name: ident, $writer:expr) => {
        // the tag_t tells us the width we should use to write
        // the length
        match $len_t {
            RadIntId::U8 => {
                let l: u8 = $v.len() as u8;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u8")?;
            }
            RadIntId::U16 => {
                let l: u16 = $v.len() as u16;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u16")?;
            }
            RadIntId::U32 => {
                let l: u32 = $v.len() as u32;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u32")?;
            }
            RadIntId::U64 => {
                let l: u64 = $v.len() as u64;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u64")?;
            }
            RadIntId::U128 => {
                let l: u128 = $v.len() as u128;
                $writer
                    .write_all(&l.to_le_bytes())
                    .context("couldn't write array length as u128")?;
            }
        }
        let $slice_name: &[u8] = bytemuck::try_cast_slice(&$v)
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
                Ok(x.0 .0 as u64)
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
                Ok(x.0 .0 as u128)
            }
        }
    };
}
