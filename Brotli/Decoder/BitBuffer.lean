module

public import Brotli.Spec.Stream

@[expose] public section

/-!
# The bit buffer

The decoder's bits at hand: a 64-bit word and how many of its low bits count. `lowBits` ties it to the spec's bit
lists, and each operation is proved to do what the spec's `readInt` does.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Numbers as bit lists -/

/-- The low `n` bits of `w`, least significant first, as the spec lists them. -/
def lowBits (w : Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => w.testBit 0 :: lowBits (w / 2) n

@[simp] theorem lowBits_length (w n : Nat) : (lowBits w n).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [lowBits, ih]

private theorem toNat_testBit_zero (w : Nat) : (w.testBit 0).toNat = w % 2 := by
  rw [Nat.testBit_zero]
  have : w % 2 = 0 ∨ w % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

/-- Reading `k` of the low bits as an integer gives `w` modulo `2 ^ k`, and leaves the bits above. -/
theorem readInt_lowBits (f : List Bool) : ∀ (k n w : Nat), k ≤ n →
    readInt k (lowBits w n ++ f) = some (w % 2 ^ k, lowBits (w / 2 ^ k) (n - k) ++ f)
  | 0, n, w, _ => by simp [readInt, Nat.mod_one]
  | k + 1, 0, _, h => by omega
  | k + 1, n + 1, w, h => by
    have ih := readInt_lowBits f k n (w / 2) (by omega)
    simp only [lowBits, List.cons_append, readInt, ih, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [toNat_testBit_zero, Nat.pow_succ', Nat.mod_mul]
    · rw [Nat.div_div_eq_div_mul, Nat.pow_succ', Nat.add_sub_add_right]

/-- Bits above `n` don't change the low `n` bits, and they follow them. -/
theorem lowBits_add : ∀ (n a b m : Nat), a < 2 ^ n →
    lowBits (a + 2 ^ n * b) (n + m) = lowBits a n ++ lowBits b m
  | 0, a, b, m, h => by
    have : a = 0 := by simpa using h
    subst this
    simp [lowBits]
  | n + 1, a, b, m, h => by
    have hsplit : n + 1 + m = (n + m) + 1 := by omega
    rw [hsplit]
    simp only [lowBits, List.cons_append]
    have hp : 2 ^ (n + 1) = 2 * 2 ^ n := Nat.pow_succ'
    have hdiv : (a + 2 ^ (n + 1) * b) / 2 = a / 2 + 2 ^ n * b := by
      rw [hp, Nat.mul_assoc]
      omega
    have hbit : (a + 2 ^ (n + 1) * b).testBit 0 = a.testBit 0 := by
      simp only [Nat.testBit_zero]
      rw [hp, Nat.mul_assoc]
      congr 1
      simp
    rw [hbit, hdiv, lowBits_add n (a / 2) b m (by rw [hp] at h; omega)]

/-- The bits of a stream's byte are its low 8 bits. -/
theorem byte_bits (b : UInt8) : (List.range 8).map b.toNat.testBit = lowBits b.toNat 8 := by
  have key : ∀ (n w : Nat), (List.range n).map w.testBit = lowBits w n := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, lowBits, ← ih (w / 2)]
      congr 1
      apply List.map_congr_left
      intro i _
      simp [Nat.testBit_succ]
  exact key 8 _

/-- A stream's bits, one byte at a time. -/
theorem bits_cons (b : UInt8) (t : List UInt8) : bits (b :: t) = lowBits b.toNat 8 ++ bits t := by
  simp [bits, byte_bits]

/-! ### The buffer -/

/-- The bits at hand: the low `count` bits of `word`. -/
structure BitBuffer where
  word : UInt64
  count : UInt64

/-- A buffer holds at most 64 bits, and nothing above them. -/
structure BitBuffer.Wf (b : BitBuffer) : Prop where
  count_le : b.count.toNat ≤ 64
  word_lt : b.word.toNat < 2 ^ b.count.toNat

/-- The bits a buffer holds, as a spec bit list. -/
def BitBuffer.held (b : BitBuffer) : List Bool :=
  lowBits b.word.toNat b.count.toNat

/-- The empty buffer. -/
def BitBuffer.empty : BitBuffer := ⟨0, 0⟩

theorem BitBuffer.empty_wf : BitBuffer.empty.Wf := ⟨by decide, by decide⟩

theorem BitBuffer.empty_held : BitBuffer.empty.held = [] := rfl

/-- Adds a byte above the bits held. The buffer must have room. -/
@[inline] def BitBuffer.push (b : BitBuffer) (x : UInt8) : BitBuffer :=
  ⟨b.word ||| (x.toUInt64 <<< b.count), b.count + 8⟩

private theorem push_word {b : BitBuffer} {x : UInt8} (hw : b.Wf) (hc : b.count.toNat ≤ 56) :
    (b.push x).word.toNat = b.word.toNat + 2 ^ b.count.toNat * x.toNat := by
  have hx : x.toNat < 256 := x.toNat_lt
  have hlt : b.count.toNat < 64 := by omega
  have hmod : b.count.toNat % 64 = b.count.toNat := Nat.mod_eq_of_lt hlt
  have hbound : 2 ^ b.count.toNat * x.toNat < 2 ^ 64 := by
    have h1 : 2 ^ b.count.toNat ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hc
    have h2 : 2 ^ b.count.toNat * x.toNat ≤ 2 ^ 56 * 255 :=
      Nat.mul_le_mul h1 (by omega)
    exact Nat.lt_of_le_of_lt h2 (by decide)
  have hshift : (x.toUInt64 <<< b.count).toNat = 2 ^ b.count.toNat * x.toNat := by
    simp only [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hmod, Nat.shiftLeft_eq, Nat.mul_comm x.toNat]
    exact Nat.mod_eq_of_lt hbound
  simp only [BitBuffer.push, UInt64.toNat_or, hshift]
  rw [Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hw.word_lt, Nat.or_comm]

theorem BitBuffer.push_count {b : BitBuffer} {x : UInt8} (hc : b.count.toNat ≤ 56) :
    (b.push x).count.toNat = b.count.toNat + 8 := by
  simp only [BitBuffer.push, UInt64.toNat_add]
  have : (8 : UInt64).toNat = 8 := rfl
  rw [this]
  exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
                             omega)

/-- Pushing a byte keeps a buffer well formed. -/
theorem BitBuffer.push_wf {b : BitBuffer} (x : UInt8) (hw : b.Wf) (hc : b.count.toNat ≤ 56) : (b.push x).Wf := by
  refine ⟨by rw [BitBuffer.push_count hc]; omega, ?_⟩
  rw [push_word hw hc, BitBuffer.push_count hc, Nat.pow_add, Nat.mul_comm]
  have hx := x.toNat_lt
  have hp : 0 < 2 ^ b.count.toNat := Nat.two_pow_pos _
  have := hw.word_lt
  have h2 : 2 ^ b.count.toNat * x.toNat + 2 ^ b.count.toNat ≤ 2 ^ b.count.toNat * 2 ^ 8 := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ hx
  simp only [Nat.mul_comm] at *
  omega

/-- Pushing a byte adds its bits after those held. -/
theorem BitBuffer.push_held {b : BitBuffer} (x : UInt8) (hw : b.Wf) (hc : b.count.toNat ≤ 56) :
    (b.push x).held = b.held ++ lowBits x.toNat 8 := by
  simp only [BitBuffer.held]
  rw [push_word hw hc, BitBuffer.push_count hc]
  exact lowBits_add _ _ _ _ hw.word_lt

/-- Pushing bytes one after another adds their bits, in order. -/
theorem BitBuffer.pushAll : ∀ (xs : List UInt8) (b : BitBuffer), b.Wf → b.count.toNat + 8 * xs.length ≤ 64 →
    (xs.foldl BitBuffer.push b).Wf ∧ (xs.foldl BitBuffer.push b).count.toNat = b.count.toNat + 8 * xs.length ∧
      (xs.foldl BitBuffer.push b).held = b.held ++ bits xs
  | [], b, hw, _ => ⟨hw, by simp, by simp [bits]⟩
  | x :: xs, b, hw, hc => by
    simp only [List.length_cons] at hc
    have hc' : b.count.toNat ≤ 56 := by omega
    have h1 := BitBuffer.push_count (x := x) hc'
    obtain ⟨w, c, e⟩ := BitBuffer.pushAll xs (b.push x) (BitBuffer.push_wf x hw hc') (by omega)
    refine ⟨w, ?_, ?_⟩
    · simp only [List.foldl_cons, List.length_cons]
      omega
    · simp only [List.foldl_cons]
      rw [e, BitBuffer.push_held x hw hc', bits_cons, List.append_assoc]

/-- The low bits of a number's remainder are its low bits. -/
theorem lowBits_mod : ∀ (n v : Nat), lowBits (v % 2 ^ n) n = lowBits v n
  | 0, _ => rfl
  | n + 1, v => by
    simp only [lowBits]
    have e : v % 2 ^ (n + 1) = v % 2 + 2 * ((v / 2) % 2 ^ n) := by
      rw [Nat.pow_succ']
      exact Nat.mod_mul
    have hdiv : v % 2 ^ (n + 1) / 2 = (v / 2) % 2 ^ n := by
      rw [e]
      omega
    have hbit : (v % 2 ^ (n + 1)).testBit 0 = v.testBit 0 := by
      simp only [Nat.testBit_zero]
      have h2 : (v % 2 + 2 * ((v / 2) % 2 ^ n)) % 2 = v % 2 := by omega
      rw [e, h2]
    rw [hbit, hdiv, lowBits_mod n (v / 2)]

/-- Fewer low bits are the first of more. -/
theorem lowBits_take : ∀ (n m v : Nat), n ≤ m → (lowBits v m).take n = lowBits v n
  | 0, _, _, _ => by simp [lowBits]
  | _ + 1, 0, _, h => by omega
  | n + 1, m + 1, v, h => by
    simp only [lowBits, List.take_succ_cons]
    rw [lowBits_take n m (v / 2) (by omega)]

/-- Adds `v`, which fits in `n` bits, above the bits held, with room for it. -/
theorem BitBuffer.add_word {word count v : UInt64} {n : Nat} (hc : count.toNat + n ≤ 64) (hc' : count.toNat < 64)
    (hw : word.toNat < 2 ^ count.toNat) (hv : v.toNat < 2 ^ n) :
    (word ||| (v <<< count)).toNat = word.toNat + 2 ^ count.toNat * v.toNat := by
  have hmod : count.toNat % 64 = count.toNat := Nat.mod_eq_of_lt hc'
  have hbound : 2 ^ count.toNat * v.toNat < 2 ^ 64 := by
    calc 2 ^ count.toNat * v.toNat
        < 2 ^ count.toNat * 2 ^ n := Nat.mul_lt_mul_of_pos_left hv (Nat.two_pow_pos _)
      _ = 2 ^ (count.toNat + n) := (Nat.pow_add _ _ _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hc
  have hshift : (v <<< count).toNat = 2 ^ count.toNat * v.toNat := by
    simp only [UInt64.toNat_shiftLeft, hmod, Nat.shiftLeft_eq, Nat.mul_comm v.toNat]
    exact Nat.mod_eq_of_lt hbound
  simp only [UInt64.toNat_or, hshift]
  rw [Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hw, Nat.or_comm]

/-- The low `k` bits as an integer. `k` is below 64. -/
@[inline] def BitBuffer.peek (b : BitBuffer) (k : UInt64) : UInt64 :=
  b.word &&& ((1 <<< k) - 1)

/-- Drops the low `k` bits. `k` is below 64. -/
@[inline] def BitBuffer.drop (b : BitBuffer) (k : UInt64) : BitBuffer :=
  ⟨b.word >>> k, b.count - k⟩

private theorem mask_toNat {k : UInt64} (hk : k.toNat < 64) : ((1 <<< k) - 1 : UInt64).toNat = 2 ^ k.toNat - 1 := by
  have hp : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hk
  have hpos : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
  have hone : ((1 : UInt64) <<< k).toNat = 2 ^ k.toNat := by
    simp only [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hk]
    have : (1 : UInt64).toNat = 1 := rfl
    rw [this, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  have hle : (1 : UInt64) ≤ (1 : UInt64) <<< k := by
    rw [UInt64.le_iff_toNat_le, hone]
    exact hpos
  rw [UInt64.toNat_sub_of_le _ _ hle, hone]
  rfl

/-- `peek` is the low `k` bits. -/
theorem BitBuffer.peek_toNat (b : BitBuffer) {k : UInt64} (hk : k.toNat < 64) :
    (b.peek k).toNat = b.word.toNat % 2 ^ k.toNat := by
  simp only [BitBuffer.peek, UInt64.toNat_and, mask_toNat hk]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem drop_word (b : BitBuffer) {k : UInt64} (hk : k.toNat < 64) :
    (b.drop k).word.toNat = b.word.toNat / 2 ^ k.toNat := by
  simp only [BitBuffer.drop, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

theorem drop_count {b : BitBuffer} {k : UInt64} (hle : k.toNat ≤ b.count.toNat) :
    (b.drop k).count.toNat = b.count.toNat - k.toNat := by
  simp only [BitBuffer.drop]
  exact UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hle)

/-- Dropping bits keeps a buffer well formed. -/
theorem BitBuffer.drop_wf {b : BitBuffer} {k : UInt64} (hw : b.Wf) (hk : k.toNat < 64)
    (hle : k.toNat ≤ b.count.toNat) : (b.drop k).Wf := by
  refine ⟨by rw [drop_count hle]; have := hw.count_le; omega, ?_⟩
  rw [drop_word b hk, drop_count hle]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, Nat.add_sub_cancel' hle]
  exact hw.word_lt

/-- Reading `k` bits from what's held, whatever follows, is `peek` then `drop`. -/
theorem BitBuffer.readInt_held {b : BitBuffer} {k : UInt64} (f : List Bool) (hk : k.toNat < 64)
    (hle : k.toNat ≤ b.count.toNat) :
    readInt k.toNat (b.held ++ f) = some ((b.peek k).toNat, (b.drop k).held ++ f) := by
  simp only [BitBuffer.held]
  rw [readInt_lowBits f _ _ _ hle, BitBuffer.peek_toNat b hk, drop_word b hk, drop_count hle]

end Brotli.Decoder
