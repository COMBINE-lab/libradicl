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
        impl TryInto<$b> for TagValue {
            type Error = anyhow::Error;

            fn try_into(self) -> std::result::Result<$b, Self::Error> {
                match self {
                    Self::U8(x) => { Ok(x as $b) },
                    Self::U16(x) => { Ok(x as $b) },
                    Self::U32(x) => { 
                        if x as u64 > <$b>::MAX as u64 {
                            bail!("Cannot convert value {x} to u16; too large")
                        } else {
                            Ok(x as $b)
                        }
                    },
                    Self::U64(x) => { 
                        if x as u64 > <$b>::MAX as u64 {
                            bail!("Cannot convert value {x} to {}; too large", stringify!($b))
                        } else {
                            Ok(x as $b)
                        }
                    },
                    _ => { bail!("cannot convert non-int TagValue to {}", stringify!($b)) }
                }
            }
        }
    };
}
