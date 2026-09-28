//! RustCrypto: `aes`, `ctr` (Ctr128BE, the SP 800-38A counter) and `cbc` with PKCS #7 unpadding.
use aes::cipher::{block_padding::Pkcs7, BlockDecrypt, BlockDecryptMut, BlockEncrypt, KeyInit, KeyIvInit, StreamCipher};
use std::io::BufRead;

fn main() {
    for line in std::io::stdin().lock().lines() {
        let line = line.unwrap();
        let f: Vec<&str> = line.split('\t').collect();
        let (suite, id, op) = (f[0], f[1], f[2]);
        let key = hex::decode(f[3]).unwrap();
        let iv = hex::decode(f[4]).unwrap_or_default();
        let input = hex::decode(f[5]).unwrap();
        let out = match suite {
            "block" => {
                let c = aes::Aes256::new_from_slice(&key).unwrap();
                let mut b = aes::Block::clone_from_slice(&input);
                if op == "decrypt" { c.decrypt_block(&mut b) } else { c.encrypt_block(&mut b) }
                hex::encode(b)
            }
            "ctr" => {
                let mut c = ctr::Ctr128BE::<aes::Aes256>::new_from_slices(&key, &iv).unwrap();
                let mut buf = input.clone();
                c.apply_keystream(&mut buf);
                hex::encode(buf)
            }
            "cbc" => {
                let d = cbc::Decryptor::<aes::Aes256>::new_from_slices(&key, &iv).unwrap();
                match d.decrypt_padded_vec_mut::<Pkcs7>(&input) {
                    Ok(p) => hex::encode(p),
                    Err(e) => format!("ERR:{e:?}"),
                }
            }
            _ => "NA".into(),
        };
        println!("{suite}\t{id}\t{out}");
    }
}
