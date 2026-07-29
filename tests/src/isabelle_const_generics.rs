//@ [!isabelle] skip

pub struct ConstGeneric<const N: usize, T> {
    pub values: [T; N],
}

pub fn make4(values: [u8; 4]) -> ConstGeneric<4, u8> {
    ConstGeneric { values }
}

const X: ConstGeneric<4, u8> = ConstGeneric { values: [1u8, 2, 3, 4] };

pub struct Marker<const N: usize>;

pub fn get_n<const N: usize>() -> usize {
    N
}

pub fn wrap<const N: usize>(values: [u8; N]) -> ConstGeneric<N, u8> {
    ConstGeneric { values }
}

pub fn unwrap<const N: usize>(value: ConstGeneric<N, u8>) -> [u8; N] {
    value.values
}

pub fn call_get_n() -> usize {
    get_n::<4>()
}
