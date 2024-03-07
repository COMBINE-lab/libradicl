// macro generalizing solution from
// https://stackoverflow.com/questions/77388769/convert-vecu8-to-vecfloat-in-rust
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
                    _ => {
                        bail!("cannot convert non-int TagValue to {}", stringify!($b))
                    }
                }
            }
        }
    };
}
