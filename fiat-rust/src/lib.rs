pub mod curve25519_32;
pub mod curve25519_64;
pub mod p448_solinas_64;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
