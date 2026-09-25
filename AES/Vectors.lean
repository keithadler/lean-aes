import AES.Spec

/-!
# Known-answer tests, as theorems

Each of these is proved by `decide +kernel`: Lean's kernel runs the key expansion and all fourteen rounds
and compares the result with the published answer. Nothing is compiled or trusted beyond the kernel, so an
independent kernel such as Tenet re-derives the same facts by running the same computation.
-/

namespace AES

set_option maxHeartbeats 0

/-! ## FIPS-197 Appendix A.3: key expansion for a 256-bit key -/

section A3

/-- The cipher key of Appendix A.3. -/
def keyA3 : Key := .ofNat 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4

theorem keyExpansion_length (k : Key) : (keyExpansion k).length = 60 := rfl

/-- The first words the expansion produces, and the last four, which form the final round key. -/
theorem fips197_A3 :
    (keyExpansion keyA3).getD 8 0 = .ofNat 0x9ba35411 ∧
    (keyExpansion keyA3).getD 9 0 = .ofNat 0x8e6925af ∧
    (keyExpansion keyA3).getD 56 0 = .ofNat 0xfe4890d1 ∧
    (keyExpansion keyA3).getD 57 0 = .ofNat 0xe6188d0b ∧
    (keyExpansion keyA3).getD 58 0 = .ofNat 0x046df344 ∧
    (keyExpansion keyA3).getD 59 0 = .ofNat 0x706c631e := by
  decide +kernel

end A3

/-! ## FIPS-197 Appendix C.3: AES-256 -/

/-- The key of Appendix C.3. -/
def keyC3 : Key := .ofNat 0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f

theorem fips197_C3_encrypt :
    encrypt keyC3 (.ofNat 0x00112233445566778899aabbccddeeff) = .ofNat 0x8ea2b7ca516745bfeafc49904b496089 := by
  decide +kernel

theorem fips197_C3_decrypt :
    decrypt keyC3 (.ofNat 0x8ea2b7ca516745bfeafc49904b496089) = .ofNat 0x00112233445566778899aabbccddeeff := by
  decide +kernel

/-! ## NIST SP 800-38A F.1.5: ECB-AES256, four blocks under the Appendix A.3 key -/

theorem sp800_38a_F15 :
    encrypt keyA3 (.ofNat 0x6bc1bee22e409f96e93d7e117393172a) = .ofNat 0xf3eed1bdb5d2a03c064b5a7e3db181f8 ∧
    encrypt keyA3 (.ofNat 0xae2d8a571e03ac9c9eb76fac45af8e51) = .ofNat 0x591ccb10d410ed26dc5ba74a31362870 ∧
    encrypt keyA3 (.ofNat 0x30c81c46a35ce411e5fbc1191a0a52ef) = .ofNat 0xb6ed21b99ca6f4f9f153e7b1beafed1d ∧
    encrypt keyA3 (.ofNat 0xf69f2445df4f9b17ad2b417be66c3710) = .ofNat 0x23304b7a39f9f3ff067d8d8f9e24ecc7 := by
  decide +kernel

end AES
