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
