import AES.Linear

/-!
# Decryption undoes encryption

`InvCipher` inverts `Cipher` for every choice of round keys, not only the ones `KeyExpansion` produces,
so the theorem for AES-256 is a corollary. Each step undoes cleanly: `AddRoundKey` is its own inverse,
`InvShiftRows` puts every byte back, `InvSubBytes` reads the S-box backwards (checked on all 256
bytes), and `InvMixColumns` multiplies by the inverse matrix. The only real work is lining up the rounds:
encryption runs them `1, 2, …, 13` and decryption `13, 12, …, 1`.
-/

namespace AES

/-! ## Each transformation and its inverse -/

theorem addRoundKey_addRoundKey (s k : State) : addRoundKey (addRoundKey s k) k = s := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := s
  simp [addRoundKey, UInt8.xor_assoc]

theorem invShiftRows_shiftRows (s : State) : invShiftRows (shiftRows s) = s := rfl
theorem shiftRows_invShiftRows (s : State) : shiftRows (invShiftRows s) = s := rfl

theorem invSubBytes_subBytes (s : State) : invSubBytes (subBytes s) = s := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := s
  simp [invSubBytes, subBytes, invSbox_sbox]

theorem subBytes_invSubBytes (s : State) : subBytes (invSubBytes s) = s := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨b0, b1, b2, b3⟩, ⟨c0, c1, c2, c3⟩, ⟨d0, d1, d2, d3⟩⟩ := s
  simp [invSubBytes, subBytes, sbox_invSbox]

theorem invMixColumns_mixColumns (s : State) : invMixColumns (mixColumns s) = s := by
  obtain ⟨c0, c1, c2, c3⟩ := s
  simp [invMixColumns, mixColumns, invMixColumn_mixColumn]

theorem mixColumns_invMixColumns (s : State) : mixColumns (invMixColumns s) = s := by
  obtain ⟨c0, c1, c2, c3⟩ := s
  simp [invMixColumns, mixColumns, mixColumn_invMixColumn]

/-! ## Lining up the rounds -/

section
variable (rk : Nat → State)

/-- One middle round of Algorithm 1. -/
abbrev round (r : Nat) (s : State) : State := addRoundKey (mixColumns (shiftRows (subBytes s))) (rk r)

/-- One middle round of Algorithm 3. -/
abbrev invRound (r : Nat) (s : State) : State := invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) (rk r))

/-- `cipherRounds` peels off its first round by definition; this peels off its last. -/
theorem cipherRounds_succ (n r : Nat) (s : State) :
    cipherRounds rk (n + 1) r s = round rk (r + n) (cipherRounds rk n r s) := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    rw [cipherRounds, ih, cipherRounds, Nat.add_right_comm, Nat.add_assoc]

theorem invCipherRounds_succ (n r : Nat) (s : State) :
    invCipherRounds rk (n + 1) r s = invRound rk (r - n) (invCipherRounds rk n r s) := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    rw [invCipherRounds, ih, invCipherRounds, Nat.sub_sub, Nat.add_comm 1 n]

/-- Decryption's round `k` undoes encryption's round `k`, seen through `SubBytes` and `ShiftRows`. -/
theorem invRound_round (k : Nat) (m : State) :
    invRound rk k (shiftRows (subBytes (round rk k m))) = shiftRows (subBytes m) := by
  simp only [invRound, round, invShiftRows_shiftRows, invSubBytes_subBytes, addRoundKey_addRoundKey,
    invMixColumns_mixColumns]

theorem round_invRound (k : Nat) (m : State) :
    round rk k (invSubBytes (invShiftRows (invRound rk k m))) = invSubBytes (invShiftRows m) := by
  simp only [invRound, round, subBytes_invSubBytes, shiftRows_invShiftRows, mixColumns_invMixColumns,
    addRoundKey_addRoundKey]

/-- `n` rounds of decryption, starting from round `r + n`, undo `n` rounds of encryption starting from
round `r + 1`. -/
theorem invCipherRounds_cipherRounds (n r : Nat) (s : State) :
    invCipherRounds rk n (r + n) (shiftRows (subBytes (cipherRounds rk n (r + 1) s))) =
      shiftRows (subBytes s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [cipherRounds_succ, invCipherRounds, show r + 1 + n = r + (n + 1) by omega,
      show r + (n + 1) - 1 = r + n by omega]
    simp only [round, invShiftRows_shiftRows, invSubBytes_subBytes, addRoundKey_addRoundKey,
      invMixColumns_mixColumns, ih]

theorem cipherRounds_invCipherRounds (n r : Nat) (s : State) :
    cipherRounds rk n (r + 1) (invSubBytes (invShiftRows (invCipherRounds rk n (r + n) s))) =
      invSubBytes (invShiftRows s) := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    rw [invCipherRounds_succ, cipherRounds, show r + (n + 1) - n = r + 1 by omega,
      show r + (n + 1) = r + 1 + n by omega]
    simp only [invRound, subBytes_invSubBytes, shiftRows_invShiftRows, mixColumns_invMixColumns,
      addRoundKey_addRoundKey]
    exact ih (r + 1) s

/-- **`InvCipher` inverts `Cipher`**, for any round keys. -/
theorem invCipher_cipher (p : State) : invCipher rk (cipher rk p) = p := by
  simp only [invCipher, cipher, addRoundKey_addRoundKey]
  rw [show Nr - 1 = 0 + 13 from rfl, show (1 : Nat) = 0 + 1 from rfl, invCipherRounds_cipherRounds,
    invShiftRows_shiftRows, invSubBytes_subBytes, addRoundKey_addRoundKey]

/-- **`Cipher` inverts `InvCipher`**, for any round keys. -/
theorem cipher_invCipher (c : State) : cipher rk (invCipher rk c) = c := by
  simp only [invCipher, cipher, addRoundKey_addRoundKey]
  rw [show Nr - 1 = 0 + 13 from rfl, show (1 : Nat) = 0 + 1 from rfl, cipherRounds_invCipherRounds,
    subBytes_invSubBytes, shiftRows_invShiftRows, addRoundKey_addRoundKey]

end

/-! ## AES-256 -/

/-- **Decryption undoes encryption**: for every 256-bit key and every 128-bit block. -/
theorem decrypt_encrypt (key : Key) (p : State) : decrypt key (encrypt key p) = p :=
  invCipher_cipher _ p

/-- And the other way round, so encryption under a fixed key is a permutation of the 2¹²⁸ blocks. -/
theorem encrypt_decrypt (key : Key) (c : State) : encrypt key (decrypt key c) = c :=
  cipher_invCipher _ c

theorem encrypt_injective (key : Key) {p q : State} (h : encrypt key p = encrypt key q) : p = q := by
  rw [← decrypt_encrypt key p, h, decrypt_encrypt]

end AES
