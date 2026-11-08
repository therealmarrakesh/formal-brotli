module

public import Brotli.Decoder.Builder
public import Brotli.Decoder.CmdLut

@[expose] public section

/-!
# The fast command loop's table arena

The fast command loop reads all its tables from one array, the header's arena. Its first 4608 bytes are a prefix
written at the header's end: the masks `2 ^ n - 1` for `n < 32`, 8 bytes each, then the shared distance table, 8 bytes
per distance symbol. The prefix codes' tables follow, as the header builds them, and after them the tables the header's
end derives from them. This file has the byte-level reads and writes and the loops that append the derived tables,
with what each leaves in the array.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Little-endian numbers in an array -/

/-- The byte at `i`, 0 past the end. -/
def byteN (t : ByteArray) (i : Nat) : Nat := (t.data[i]?.getD 0).toNat

/-- The `n` bytes from `i` as a little-endian number. -/
def leAt (t : ByteArray) (i : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => byteN t i + 256 * leAt t (i + 1) n

theorem byteN_lt (t : ByteArray) (i : Nat) : byteN t i < 256 := (t.data[i]?.getD 0).toNat_lt

theorem leAt_lt (t : ByteArray) (i : Nat) : ∀ n, leAt t i n < 256 ^ n
  | 0 => by simp [leAt]
  | n + 1 => by
    have h1 := byteN_lt t i
    have h2 := leAt_lt t (i + 1) n
    rw [leAt, Nat.pow_succ]
    omega

/-- Two arrays that agree on the bytes read give the same number. -/
theorem leAt_congr {t t' : ByteArray} {i : Nat} :
    ∀ {n : Nat}, (∀ q, i ≤ q → q < i + n → t'.data[q]? = t.data[q]?) → leAt t' i n = leAt t i n
  | 0, _ => rfl
  | n + 1, h => by
    rw [leAt, leAt, leAt_congr (n := n) (fun q h1 h2 => h q (by omega) (by omega))]
    unfold byteN
    rw [h i (Nat.le_refl _) (by omega)]

/-- Two arrays with the same bytes there give the same number. -/
theorem leAt_congrB {t t' : ByteArray} {i : Nat} :
    ∀ {n : Nat}, (∀ q, i ≤ q → q < i + n → byteN t' q = byteN t q) → leAt t' i n = leAt t i n
  | 0, _ => rfl
  | n + 1, h => by
    rw [leAt, leAt, leAt_congrB (n := n) (fun q h1 h2 => h q (by omega) (by omega)), h i (Nat.le_refl _) (by omega)]

/-- Bytes that are the base-256 digits of `v` read back as `v`, cut to their number. -/
theorem leAt_digits {t : ByteArray} : ∀ {n i v : Nat}, (∀ j, j < n → byteN t (i + j) = (v / 256 ^ j) % 256) →
    leAt t i n = v % 256 ^ n
  | 0, _, v, _ => by simp [leAt, Nat.mod_one]
  | n + 1, i, v, h => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one] at h0
    have ih := leAt_digits (n := n) (i := i + 1) (v := v / 256) (fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega, h (j + 1) (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_succ'])
    rw [leAt, h0, ih, Nat.pow_succ', Nat.mod_mul]

/-! ### Positions -/

theorem fastIdx_add {i : USize} {k : Nat} (h : i.toNat + k < 2 ^ 32) : (i + USize.ofNat k).toNat = i.toNat + k := by
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs
  have hk : (USize.ofNat k).toNat = k := by
    rw [USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_add, hk]
  exact Nat.mod_eq_of_lt (by omega)

/-- A position given as a number below `2 ^ 32` is that number. -/
theorem fastLit {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

/-- A position below another moves on by one without wrapping. -/
theorem fastIdx_succ {j n : USize} (h : j < n) : (j + USize.ofNat 1).toNat = j.toNat + 1 := by
  have hj := USize.lt_iff_toNat_lt.mp h
  have hn := n.toNat_lt_size
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs hn
  have hk : (USize.ofNat 1).toNat = 1 := by
    rw [USize.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_add, hk]
  exact Nat.mod_eq_of_lt (by omega)

/-! ### Loads -/

/-- A byte or'ed in above `K` bits that hold a number below `2 ^ K`. -/
theorem or_byte {acc : UInt64} {b : UInt8} {k : UInt64} {K P A : Nat} (hk : k.toNat = K) (hK : K + 8 ≤ 64)
    (hP : 2 ^ K = P) (ha : acc.toNat = A) (hA : A < P) : (acc ||| (b.toUInt64 <<< k)).toNat = A + P * b.toNat := by
  have hb : b.toUInt64.toNat < 2 ^ 8 := by rw [UInt8.toNat_toUInt64]; exact b.toNat_lt
  rw [BitBuffer.add_word (n := 8) (by rw [hk]; exact hK) (by rw [hk]; omega) (by rw [ha, hk, hP]; exact hA) hb, ha, hk,
    hP, UInt8.toNat_toUInt64]

theorem eight_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (b0.toUInt64 ||| (b1.toUInt64 <<< 8) ||| (b2.toUInt64 <<< 16) ||| (b3.toUInt64 <<< 24) |||
      (b4.toUInt64 <<< 32) ||| (b5.toUInt64 <<< 40) ||| (b6.toUInt64 <<< 48) ||| (b7.toUInt64 <<< 56)).toNat =
    b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 * (b4.toNat + 256 * (b5.toNat +
      256 * (b6.toNat + 256 * b7.toNat)))))) := by
  have c0 : b0.toNat < 256 := b0.toNat_lt
  have c1 : b1.toNat < 256 := b1.toNat_lt
  have c2 : b2.toNat < 256 := b2.toNat_lt
  have c3 : b3.toNat < 256 := b3.toNat_lt
  have c4 : b4.toNat < 256 := b4.toNat_lt
  have c5 : b5.toNat < 256 := b5.toNat_lt
  have c6 : b6.toNat < 256 := b6.toNat_lt
  have e1 := or_byte (b := b1) (k := 8) (K := 8) (P := 256) rfl (by decide) rfl (UInt8.toNat_toUInt64 b0) c0
  have e2 := or_byte (b := b2) (k := 16) (K := 16) (P := 65536) rfl (by decide) rfl e1 (by omega)
  have e3 := or_byte (b := b3) (k := 24) (K := 24) (P := 16777216) rfl (by decide) rfl e2 (by omega)
  have e4 := or_byte (b := b4) (k := 32) (K := 32) (P := 4294967296) rfl (by decide) rfl e3 (by omega)
  have e5 := or_byte (b := b5) (k := 40) (K := 40) (P := 1099511627776) rfl (by decide) rfl e4 (by omega)
  have e6 := or_byte (b := b6) (k := 48) (K := 48) (P := 281474976710656) rfl (by decide) rfl e5 (by omega)
  have e7 := or_byte (b := b7) (k := 56) (K := 56) (P := 72057594037927936) rfl (by decide) rfl e6 (by omega)
  rw [e7]
  omega

/-- The 8 bytes from `i` as one little-endian word, which compiles to one 8-byte load. -/
@[inline] def load64 (t : ByteArray) (i : USize) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) : UInt64 :=
  (t.uget i (by omega)).toUInt64 |||
    ((t.uget (i + USize.ofNat 1) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 8) |||
    ((t.uget (i + USize.ofNat 2) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 16) |||
    ((t.uget (i + USize.ofNat 3) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 24) |||
    ((t.uget (i + USize.ofNat 4) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 32) |||
    ((t.uget (i + USize.ofNat 5) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 40) |||
    ((t.uget (i + USize.ofNat 6) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 48) |||
    ((t.uget (i + USize.ofNat 7) (by rw [fastIdx_add (by omega)]; omega)).toUInt64 <<< 56)

theorem load64_toNat (t : ByteArray) (i : USize) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    (load64 t i h h32).toNat = leAt t i.toNat 8 := by
  unfold load64
  rw [eight_bytes]
  simp only [uget_toNat]
  rw [fastIdx_add (k := 1) (by omega), fastIdx_add (k := 2) (by omega), fastIdx_add (k := 3) (by omega),
    fastIdx_add (k := 4) (by omega), fastIdx_add (k := 5) (by omega), fastIdx_add (k := 6) (by omega),
    fastIdx_add (k := 7) (by omega)]
  simp only [leAt, byteN, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

/-! ### Writes in place -/

/-- Writes the low `n` bytes of `v` from `i`, little-endian. -/
def putLE (t : ByteArray) (i : USize) (v : UInt64) : (n : Nat) → i.toNat + n ≤ t.size → t.size < 2 ^ 32 → ByteArray
  | 0, _, _ => t
  | n + 1, h, h32 =>
    putLE (t.uset i v.toUInt8 (by omega)) (i + USize.ofNat 1) (v >>> 8) n
      (by rw [size_uset', fastIdx_add (by omega)]; omega) (by rw [size_uset']; exact h32)

theorem size_putLE : ∀ (n : Nat) (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + n ≤ t.size)
    (h32 : t.size < 2 ^ 32), (putLE t i v n h h32).size = t.size
  | 0, _, _, _, _, _ => rfl
  | n + 1, t, i, v, h, h32 => by rw [putLE, size_putLE n, size_uset']

/-- Bytes outside the ones written stay. -/
theorem putLE_out : ∀ (n : Nat) (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + n ≤ t.size)
    (h32 : t.size < 2 ^ 32) (q : Nat), (q < i.toNat ∨ i.toNat + n ≤ q) → (putLE t i v n h h32).data[q]? = t.data[q]?
  | 0, _, _, _, _, _, _, _ => rfl
  | n + 1, t, i, v, h, h32, q, hq => by
    rw [putLE, putLE_out n _ _ _ _ _ q (by rw [fastIdx_add (by omega)]; omega), uset_get_ne (by omega) (by omega)]

private theorem shr8_digit (v : UInt64) (j : Nat) : (v >>> 8).toNat / 256 ^ j = v.toNat / 256 ^ (j + 1) := by
  rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 8 = 256 from rfl, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- The bytes written are `v`'s. -/
theorem putLE_in : ∀ (n : Nat) (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + n ≤ t.size)
    (h32 : t.size < 2 ^ 32) (q : Nat), i.toNat ≤ q → q < i.toNat + n →
    byteN (putLE t i v n h h32) q = (v.toNat / 256 ^ (q - i.toNat)) % 256
  | 0, _, _, _, _, _, _, h1, h2 => absurd h2 (by omega)
  | n + 1, t, i, v, h, h32, q, h1, h2 => by
    have hi1 := fastIdx_add (i := i) (k := 1) (by omega)
    rw [putLE]
    by_cases hq : q = i.toNat
    · subst hq
      unfold byteN
      rw [putLE_out n _ _ _ _ _ _ (by rw [hi1]; omega), uset_get_same (by omega), UInt64.toNat_toUInt8, Nat.sub_self,
        Nat.pow_zero, Nat.div_one]
    · rw [putLE_in n _ _ _ _ _ q (by rw [hi1]; omega) (by rw [hi1]; omega), hi1, shr8_digit,
        show q - (i.toNat + 1) + 1 = q - i.toNat by omega]

/-- A whole word written reads back. -/
theorem leAt_putLE (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    leAt (putLE t i v 8 h h32) i.toNat 8 = v.toNat := by
  rw [leAt_digits (v := v.toNat) (fun j hj => by rw [putLE_in 8 t i v h h32 _ (by omega) (by omega), Nat.add_sub_cancel_left])]
  exact Nat.mod_eq_of_lt (by have := v.toNat_lt; exact this)

/-! ### Appending -/

/-- Appends the low `n` bytes of `v`, little-endian. -/
def pushLE (t : ByteArray) (v : UInt64) : Nat → ByteArray
  | 0 => t
  | n + 1 => pushLE (t.push v.toUInt8) (v >>> 8) n

theorem size_pushLE : ∀ (n : Nat) (t : ByteArray) (v : UInt64), (pushLE t v n).size = t.size + n
  | 0, _, _ => rfl
  | n + 1, t, v => by rw [pushLE, size_pushLE n, ByteArray.size_push]; omega

/-- What was there stays. -/
theorem pushLE_keep : ∀ (n : Nat) (t : ByteArray) (v : UInt64) (q : Nat), q < t.size → (pushLE t v n).data[q]? = t.data[q]?
  | 0, _, _, _, _ => rfl
  | n + 1, t, v, q, hq => by
    rw [pushLE, pushLE_keep n _ _ q (by rw [ByteArray.size_push]; omega), ByteArray.data_push, Array.getElem?_push,
      ite_eq_right (show ¬ q = t.data.size from fun e => by have : q < t.data.size := hq; omega)]

/-- The bytes appended are `v`'s. -/
theorem pushLE_in : ∀ (n : Nat) (t : ByteArray) (v : UInt64) (q : Nat), t.size ≤ q → q < t.size + n →
    byteN (pushLE t v n) q = (v.toNat / 256 ^ (q - t.size)) % 256
  | 0, _, _, _, h1, h2 => absurd h2 (by omega)
  | n + 1, t, v, q, h1, h2 => by
    rw [pushLE]
    by_cases hq : q = t.size
    · subst hq
      unfold byteN
      rw [pushLE_keep n _ _ _ (by rw [ByteArray.size_push]; omega), ByteArray.data_push, Array.getElem?_push,
        ite_eq_left (show t.size = t.data.size from rfl), Option.getD_some, UInt64.toNat_toUInt8, Nat.sub_self,
        Nat.pow_zero, Nat.div_one]
    · rw [pushLE_in n _ _ q (by rw [ByteArray.size_push]; omega) (by rw [ByteArray.size_push]; omega),
        ByteArray.size_push, shr8_digit, show q - (t.size + 1) + 1 = q - t.size by omega]

/-- An appended entry reads back, cut to its width. -/
theorem leAt_pushLE (t : ByteArray) (v : UInt64) (n : Nat) : leAt (pushLE t v n) t.size n = v.toNat % 256 ^ n :=
  leAt_digits (fun j hj => by rw [pushLE_in n t v _ (by omega) (by omega), Nat.add_sub_cancel_left])

/-! ### Arrays that grow -/

/-- `t'` begins with `t`. -/
def Extends (t t' : ByteArray) : Prop := t.size ≤ t'.size ∧ ∀ q, q < t.size → t'.data[q]? = t.data[q]?

theorem Extends.refl (t : ByteArray) : Extends t t := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem Extends.trans {t1 t2 t3 : ByteArray} (h1 : Extends t1 t2) (h2 : Extends t2 t3) : Extends t1 t3 :=
  ⟨Nat.le_trans h1.1 h2.1, fun q hq => (h2.2 q (by have := h1.1; omega)).trans (h1.2 q hq)⟩

theorem Extends.pushLE (t : ByteArray) (v : UInt64) (n : Nat) : Extends t (pushLE t v n) :=
  ⟨by rw [size_pushLE]; omega, fun q hq => pushLE_keep n t v q hq⟩

theorem Extends.append (t z : ByteArray) : Extends t (t ++ z) := by
  refine ⟨by rw [ByteArray.size_append]; omega, fun q hq => ?_⟩
  rw [← Array.getElem?_toList, ByteArray.toList_data_append, List.getElem?_append_left (by simpa using hq),
    Array.getElem?_toList]

theorem Extends.leAt {t t' : ByteArray} (h : Extends t t') {i n : Nat} (hi : i + n ≤ t.size) : _root_.Brotli.Decoder.leAt t' i n = _root_.Brotli.Decoder.leAt t i n :=
  leAt_congr fun q _ h2 => h.2 q (by omega)

theorem Extends.slotAt {t t' : ByteArray} (h : Extends t t') {q : Nat} (hq : 2 * q + 1 < t.size) :
    _root_.Brotli.Decoder.slotAt t' q = _root_.Brotli.Decoder.slotAt t q := by
  simp only [Brotli.Decoder.slotAt, slotNum]
  rw [h.2 _ (by omega), h.2 _ (by omega)]

theorem TableFits.extend {t t' : ByteArray} {b : Nat} (hf : TableFits t b) (h : Extends t t') : TableFits t' b := by
  have hr := hf.root
  have hs : ∀ r, r < 256 → _root_.Brotli.Decoder.slotAt t' (b + r) = _root_.Brotli.Decoder.slotAt t (b + r) :=
    fun r hr' => h.slotAt (by omega)
  refine ⟨by have := h.1; omega, fun r hr' hb => ?_⟩
  rw [hs r hr'] at hb ⊢
  obtain ⟨h1, h2⟩ := hf.sub r hr' hb
  exact ⟨h1, by have := h.1; omega⟩

theorem lookupSlots_extend {t t' : ByteArray} {b w : Nat} (hf : TableFits t b) (h : Extends t t') :
    lookupSlots t' b w = lookupSlots t b w := by
  have hr := hf.root
  have hw : w % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold lookupSlots
  dsimp only
  rw [h.slotAt (by omega)]
  split
  · rfl
  · rename_i hb
    obtain ⟨_, h2⟩ := hf.sub _ hw (by omega)
    have hj : (w / 256) % 2 ^ ((Brotli.Decoder.slotAt t (b + w % 256)).1 - 8) <
        2 ^ ((Brotli.Decoder.slotAt t (b + w % 256)).1 - 8) := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [h.slotAt (by omega)]

/-- A lookup reads the same in an array that begins with the one it was made for. -/
theorem lookup_extend {t t' : ByteArray} {base : USize} {w : UInt64} (hf : TableFits t base.toNat)
    (h32 : t.size < 2 ^ 32) (hf' : TableFits t' base.toNat) (h32' : t'.size < 2 ^ 32) (h : Extends t t') :
    lookup t' base w hf' h32' = lookup t base w hf h32 := by
  obtain ⟨a1, a2⟩ := lookup_spec (w := w) hf' h32'
  obtain ⟨b1, b2⟩ := lookup_spec (w := w) hf h32
  rw [lookupSlots_extend hf h] at a1 a2
  apply UInt64.toNat_inj.mp
  rw [← Nat.div_add_mod (lookup t' base w hf' h32').toNat 16, ← Nat.div_add_mod (lookup t base w hf h32).toNat 16,
    a1, a2, b1, b2]

/-! ### Writing entries in a loop

A pass that appends entries makes room for all of them at once (`zeroExtend`, which writes in place into an array with
room) and then writes each in place. Appending a byte at a time checked the array's room and its exclusivity once per
byte, through a call. -/

theorem mul_step {w a b : Nat} (h : a < b) : w + w * (b - (a + 1)) = w * (b - a) := by
  rw [show b - a = (b - (a + 1)) + 1 by omega, Nat.mul_succ]
  omega

/-- `putLE` of 4 bytes written out, with no loop over the count. -/
@[inline] def tput4 (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    ByteArray :=
  have e1 : (i + USize.ofNat 1).toNat = i.toNat + 1 := fastIdx_add (by omega)
  have e2 : (i + USize.ofNat 1 + USize.ofNat 1).toNat = i.toNat + 2 := by
    rw [fastIdx_add (i := i + USize.ofNat 1) (k := 1) (by omega), e1]
  have e3 : (i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1).toNat = i.toNat + 3 := by
    rw [fastIdx_add (i := i + USize.ofNat 1 + USize.ofNat 1) (k := 1) (by omega), e2]
  (((t.uset i v.toUInt8 (by omega)).uset (i + USize.ofNat 1) (v >>> 8).toUInt8 (by rw [size_uset', e1]; omega)).uset
    (i + USize.ofNat 1 + USize.ofNat 1) (v >>> 8 >>> 8).toUInt8 (by rw [size_uset', size_uset', e2]; omega)).uset
    (i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1) (v >>> 8 >>> 8 >>> 8).toUInt8
    (by rw [size_uset', size_uset', size_uset', e3]; omega)

theorem tput4_eq (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 4 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    tput4 t i v h h32 = putLE t i v 4 h h32 := rfl

/-- `putLE` of 8 bytes written out, with no loop over the count. -/
@[inline] def tput8 (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    ByteArray :=
  have e1 : (i + USize.ofNat 1).toNat = i.toNat + 1 := fastIdx_add (by omega)
  have e2 : (i + USize.ofNat 1 + USize.ofNat 1).toNat = i.toNat + 2 := by
    rw [fastIdx_add (i := i + USize.ofNat 1) (k := 1) (by omega), e1]
  have e3 : (i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1).toNat = i.toNat + 3 := by
    rw [fastIdx_add (i := i + USize.ofNat 1 + USize.ofNat 1) (k := 1) (by omega), e2]
  have e4 : (i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1).toNat = i.toNat + 4 := by
    rw [fastIdx_add (i := i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1) (k := 1) (by omega), e3]
  tput4 (tput4 t i v (by omega) h32) (i + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1 + USize.ofNat 1)
    (v >>> 8 >>> 8 >>> 8 >>> 8) (by rw [tput4_eq, size_putLE, e4]; omega) (by rw [tput4_eq, size_putLE]; exact h32)

theorem tput8_eq (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    tput8 t i v h h32 = putLE t i v 8 h h32 := rfl

/-- `putLE`, written out for the widths the tables use. -/
@[inline] def putW (t : ByteArray) (i : USize) (v : UInt64) (n : Nat) (h : i.toNat + n ≤ t.size) (h32 : t.size < 2 ^ 32) :
    ByteArray :=
  if h4 : n = 4 then tput4 t i v (h4 ▸ h) h32
  else if h8 : n = 8 then tput8 t i v (h8 ▸ h) h32
  else putLE t i v n h h32

theorem putW_eq (t : ByteArray) (i : USize) (v : UInt64) (n : Nat) (h : i.toNat + n ≤ t.size) (h32 : t.size < 2 ^ 32) :
    putW t i v n h h32 = putLE t i v n h h32 := by
  unfold putW
  split
  · rename_i h4
    subst h4
    exact tput4_eq t i v h h32
  · split
    · rename_i h8
      subst h8
      exact tput8_eq t i v h h32
    · rfl

/-- A whole entry written reads back, cut to its width. -/
theorem leAt_putLE' (n : Nat) (t : ByteArray) (i : USize) (v : UInt64) (h : i.toNat + n ≤ t.size) (h32 : t.size < 2 ^ 32) :
    leAt (putLE t i v n h h32) i.toNat n = v.toNat % 256 ^ n :=
  leAt_digits fun j hj => by rw [putLE_in n t i v h h32 _ (by omega) (by omega), Nat.add_sub_cancel_left]

/-- An array grown by zeros begins with the array. -/
theorem Extends.zeroExtend (t : ByteArray) (k : Nat) : Extends t (zeroExtend t k) := by
  refine ⟨by rw [size_zeroExtend]; omega, fun q hq => ?_⟩
  rw [zeroExtend_data, Array.getElem?_append_left (by exact hq)]

/-- Writing past an array's beginning keeps it. -/
theorem Extends.putLE {t0 t : ByteArray} (he : Extends t0 t) {i : USize} {v : UInt64} {n : Nat}
    (h : i.toNat + n ≤ t.size) (h32 : t.size < 2 ^ 32) (hi : t0.size ≤ i.toNat) : Extends t0 (putLE t i v n h h32) :=
  ⟨by rw [size_putLE]; exact he.1, fun q hq => by rw [putLE_out n t i v h h32 q (Or.inl (by omega))]; exact he.2 q hq⟩

/-- Writes `w`-byte little-endian entries in place from `o`, `f t h _ j _` for each `j` from `j` below `n`, each computed
from the array so far. The array begins with `t0`, which `P` holds of, and the entries go after it, so that `P` holds of
the array on the way and `f` can read it without checks. -/
@[specialize] def fillLoop (P : ByteArray → Prop) (w : Nat) (hP : ∀ t t', P t → Extends t t' → P t') (n : USize)
    (f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64) (t0 : ByteArray) (h0 : P t0)
    (t : ByteArray) (he : Extends t0 t) (h32 : t.size < 2 ^ 32) (o j : USize) (hi : t0.size ≤ o.toNat)
    (ho : o.toNat + w * (n.toNat - j.toNat) ≤ t.size) : ByteArray :=
  if hj : j < n then
    have hm := mul_step (w := w) (USize.lt_iff_toNat_lt.mp hj)
    have hw : o.toNat + w ≤ t.size := by omega
    fillLoop P w hP n f t0 h0 (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32)
      (by rw [putW_eq]; exact he.putLE hw h32 hi) (by rw [putW_eq, size_putLE]; exact h32) (o + USize.ofNat w)
      (j + USize.ofNat 1) (by rw [fastIdx_add (by omega)]; omega)
      (by rw [putW_eq, size_putLE, fastIdx_add (by omega), fastIdx_succ hj]; omega)
  else t
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.mp hj
  rw [fastIdx_succ hj]
  omega

/-- What the writing loop leaves: the size and the bytes before `o` as they were, and each entry from `o` on, when each
entry depends only on the bytes there were. -/
theorem fillLoop_spec {P : ByteArray → Prop} {w : Nat} {hP : ∀ t t', P t → Extends t t' → P t'} {n : USize}
    {f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64} {t0 : ByteArray} {h0 : P t0}
    (hf : ∀ t t' h h' s s' j hj, Extends t t' → f t' h' s' j hj = f t h s j hj) :
    ∀ (N : Nat) (t : ByteArray) (he : Extends t0 t) (h32 : t.size < 2 ^ 32) (o j : USize) (hi : t0.size ≤ o.toNat)
      (ho : o.toNat + w * (n.toNat - j.toNat) ≤ t.size), n.toNat - j.toNat = N →
      (fillLoop P w hP n f t0 h0 t he h32 o j hi ho).size = t.size ∧
      (∀ q, q < o.toNat → (fillLoop P w hP n f t0 h0 t he h32 o j hi ho).data[q]? = t.data[q]?) ∧
      ∀ (k : USize) (hk : k < n), j ≤ k →
        leAt (fillLoop P w hP n f t0 h0 t he h32 o j hi ho) (o.toNat + w * (k.toNat - j.toNat)) w =
          (f t0 h0 (Nat.lt_of_le_of_lt he.1 h32) k hk).toNat % 256 ^ w := by
  intro N
  induction N with
  | zero =>
    intro t he h32 o j hi ho hN
    have hj : ¬ j < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [fillLoop, dite_eq_right hj]
    refine ⟨rfl, fun _ _ => rfl, fun k h2 h1 => ?_⟩
    have := USize.le_iff_toNat_le.mp h1
    have := USize.lt_iff_toNat_lt.mp h2
    omega
  | succ N ih =>
    intro t he h32 o j hi ho hN
    have hj : j < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hjn := USize.lt_iff_toNat_lt.mp hj
    have hs := fastIdx_succ hj
    have hm := mul_step (w := w) hjn
    have hw : o.toNat + w ≤ t.size := by omega
    have ho1 : (o + USize.ofNat w).toNat = o.toNat + w := fastIdx_add (by omega)
    rw [fillLoop, dite_eq_left hj]
    dsimp only
    have hv0 := hf t0 t h0 (hP t0 t h0 he) (Nat.lt_of_le_of_lt he.1 h32) h32 j hj he
    have hsz : (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32).size = t.size := by rw [putW_eq, size_putLE]
    obtain ⟨i1, i2, i3⟩ := ih (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32)
      (by rw [putW_eq]; exact he.putLE hw h32 hi) (by rw [hsz]; exact h32) (o + USize.ofNat w) (j + USize.ofNat 1)
      (by rw [ho1]; omega) (by rw [hsz, ho1, hs]; omega) (by rw [hs]; omega)
    generalize fillLoop P w hP n f t0 h0 (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32) _ _ (o + USize.ofNat w)
      (j + USize.ofNat 1) _ _ = r at i1 i2 i3
    refine ⟨by rw [i1, hsz], fun q hq => ?_, fun k h2 h1 => ?_⟩
    · rw [i2 q (by rw [ho1]; omega), putW_eq, putLE_out w t o _ hw h32 q (Or.inl hq)]
    · have hk1 := USize.le_iff_toNat_le.mp h1
      by_cases hk : k = j
      · subst hk
        rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero,
          leAt_congr (fun q h3 h4 => i2 q (by rw [ho1]; omega)), putW_eq, leAt_putLE', hv0]
      · have hk2 : j.toNat + 1 ≤ k.toNat := by
          have : j.toNat ≠ k.toNat := fun e => hk (USize.toNat_inj.mp e).symm
          omega
        have e := i3 k h2 (USize.le_iff_toNat_le.mpr (by rw [hs]; exact hk2))
        rw [ho1, hs] at e
        rw [show o.toNat + w * (k.toNat - j.toNat) = o.toNat + w + w * (k.toNat - (j.toNat + 1)) by
          rw [Nat.add_assoc, mul_step (show j.toNat < k.toNat by omega)]]
        exact e

/-- The writing loop leaves the bytes after its entries as they were. -/
theorem fillLoop_above {P : ByteArray → Prop} {w : Nat} {hP : ∀ t t', P t → Extends t t' → P t'} {n : USize}
    {f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64} {t0 : ByteArray} {h0 : P t0} :
    ∀ (N : Nat) (t : ByteArray) (he : Extends t0 t) (h32 : t.size < 2 ^ 32) (o j : USize) (hi : t0.size ≤ o.toNat)
      (ho : o.toNat + w * (n.toNat - j.toNat) ≤ t.size), n.toNat - j.toNat = N →
      ∀ q, o.toNat + w * (n.toNat - j.toNat) ≤ q → (fillLoop P w hP n f t0 h0 t he h32 o j hi ho).data[q]? = t.data[q]? := by
  intro N
  induction N with
  | zero =>
    intro t he h32 o j hi ho hN q _
    have hj : ¬ j < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [fillLoop, dite_eq_right hj]
  | succ N ih =>
    intro t he h32 o j hi ho hN q hq
    have hj : j < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hjn := USize.lt_iff_toNat_lt.mp hj
    have hs := fastIdx_succ hj
    have hm := mul_step (w := w) hjn
    have hw : o.toNat + w ≤ t.size := by omega
    have ho1 : (o + USize.ofNat w).toNat = o.toNat + w := fastIdx_add (by omega)
    have hsz : (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32).size = t.size := by rw [putW_eq, size_putLE]
    rw [fillLoop, dite_eq_left hj]
    dsimp only
    have e := ih (putW t o (f t (hP t0 t h0 he) h32 j hj) w hw h32)
      (by rw [putW_eq]; exact he.putLE hw h32 hi) (by rw [hsz]; exact h32) (o + USize.ofNat w) (j + USize.ofNat 1)
      (by rw [ho1]; omega) (by rw [hsz, ho1, hs]; omega) (by rw [hs]; omega) q (by rw [ho1, hs]; omega)
    rw [e, putW_eq, putLE_out w t o _ hw h32 q (Or.inr (by omega))]

/-- Appends `w`-byte little-endian entries, `f t h _ j _` for each `j` from `j` below `n`, each computed from the array
so far: room for all of them at once, then each written in place. `P` holds of every array on the way, so that `f` can
read the array without checks, and the array stays below `2 ^ 32` bytes. -/
@[specialize] def pushLoop (P : ByteArray → Prop) (w : Nat) (hP : ∀ t t', P t → Extends t t' → P t') (n : USize)
    (f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64)
    (t : ByteArray) (h : P t) (j : USize) (hc : t.size + w * (n.toNat - j.toNat) < 2 ^ 32) : ByteArray :=
  fillLoop P w hP n f t h (zeroExtend t (w * (n.toNat - j.toNat))) (Extends.zeroExtend t _)
    (by rw [size_zeroExtend]; exact hc) (USize.ofNat t.size) j (by rw [fastLit (by omega)]; exact Nat.le_refl _)
    (by rw [fastLit (by omega), size_zeroExtend]; exact Nat.le_refl _)

/-- What the loop leaves: the array so far, then each entry, when each entry depends only on the bytes there were. -/
theorem pushLoop_spec {P : ByteArray → Prop} {w : Nat} {hP : ∀ t t', P t → Extends t t' → P t'} {n : USize}
    {f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64}
    (hf : ∀ t t' h h' s s' j hj, Extends t t' → f t' h' s' j hj = f t h s j hj) :
    ∀ (N : Nat) (t : ByteArray) (h : P t) (j : USize) (hc : t.size + w * (n.toNat - j.toNat) < 2 ^ 32),
      n.toNat - j.toNat = N →
      (pushLoop P w hP n f t h j hc).size = t.size + w * (n.toNat - j.toNat) ∧
      Extends t (pushLoop P w hP n f t h j hc) ∧
      ∀ (k : USize) (hk : k < n), j ≤ k →
        leAt (pushLoop P w hP n f t h j hc) (t.size + w * (k.toNat - j.toNat)) w =
          (f t h (by omega) k hk).toNat % 256 ^ w := by
  intro N t h j hc hN
  have h32 : t.size < 2 ^ 32 := by omega
  have hz := size_zeroExtend t (w * (n.toNat - j.toNat))
  have hT : (USize.ofNat t.size).toNat = t.size := fastLit h32
  unfold pushLoop
  obtain ⟨i1, i2, i3⟩ := fillLoop_spec (P := P) (w := w) (hP := hP) (n := n) (f := f) (t0 := t) (h0 := h) hf N
    (zeroExtend t (w * (n.toNat - j.toNat))) (Extends.zeroExtend t _) (by rw [hz]; exact hc) (USize.ofNat t.size) j
    (by rw [hT]; exact Nat.le_refl _) (by rw [hT, hz]; exact Nat.le_refl _) hN
  refine ⟨by rw [i1, hz], ⟨by rw [i1, hz]; omega, fun q hq => ?_⟩, fun k hk h1 => ?_⟩
  · rw [i2 q (by rw [hT]; exact hq)]
    exact (Extends.zeroExtend t _).2 q hq
  · have e := i3 k hk h1
    have hpos : (USize.ofNat t.size).toNat + w * (k.toNat - j.toNat) = t.size + w * (k.toNat - j.toNat) := by rw [hT]
    rw [hpos] at e
    exact e

/-! ### The masks

The arena's first 256 bytes are the masks `2 ^ n - 1` for `n < 32`, 8 bytes each, written when a header's arena is
made, before any table. -/

/-- The mask `2 ^ j - 1`. -/
@[inline] def maskEntry (_t : ByteArray) (_h : True) (_s : _t.size < 2 ^ 32) (j : USize) (_hj : j < USize.ofNat 32) :
    UInt64 :=
  ((1 : UInt64) <<< j.toUInt64) - 1

theorem usize32 : (USize.ofNat 32).toNat = 32 := fastLit (by decide)

/-- Appends the 32 masks. -/
def writeMasks (t : ByteArray) (h : t.size + 256 < 2 ^ 32) : ByteArray :=
  pushLoop (fun _ => True) 8 (fun _ _ _ _ => trivial) (USize.ofNat 32) maskEntry t trivial 0 (by
    rw [usize32]
    exact h)

private theorem maskEntry_val {j : USize} (hj : j.toNat < 32) : (((1 : UInt64) <<< j.toUInt64) - 1).toNat = 2 ^ j.toNat - 1 := by
  have h1 : ((1 : UInt64) <<< j.toUInt64).toNat = 2 ^ j.toNat := by
    rw [UInt64.toNat_shiftLeft, USize.toNat_toUInt64, Nat.mod_eq_of_lt (show j.toNat < 64 by omega),
      show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (show 1 < 2 by decide) (by omega))
  have hp := Nat.two_pow_pos j.toNat
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [h1]; exact hp)), h1]
  rfl

/-- The masks, once written, read back. -/
theorem writeMasks_spec (t : ByteArray) (h : t.size + 256 < 2 ^ 32) :
    (writeMasks t h).size = t.size + 256 ∧ Extends t (writeMasks t h) ∧
      ∀ n, n < 32 → leAt (writeMasks t h) (t.size + 8 * n) 8 = 2 ^ n - 1 := by
  have h0 : (0 : USize).toNat = 0 := rfl
  unfold writeMasks
  obtain ⟨s1, s2, s3⟩ := pushLoop_spec (P := fun _ => True) (w := 8) (hP := fun _ _ _ _ => trivial)
    (n := USize.ofNat 32) (f := maskEntry) (fun _ _ _ _ _ _ _ _ _ => rfl) 32 t trivial 0
    (by rw [usize32, h0]; exact h) (by rw [usize32, h0])
  refine ⟨by rw [s1, usize32, h0], s2, fun n hn => ?_⟩
  have hk : (USize.ofNat n).toNat = n := fastLit (by omega)
  have e := s3 (USize.ofNat n) (USize.lt_iff_toNat_lt.mpr (by rw [hk, usize32]; exact hn))
    (USize.le_iff_toNat_le.mpr (by rw [h0]; omega))
  rw [show t.size + 8 * n = t.size + 8 * ((USize.ofNat n).toNat - USize.toNat 0) by rw [hk, h0, Nat.sub_zero], e]
  unfold maskEntry
  rw [maskEntry_val (by rw [hk]; exact hn), hk]
  have hp : 2 ^ n ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) (by omega)
  have h64 : (2 : Nat) ^ 32 < 256 ^ 8 := by decide
  exact Nat.mod_eq_of_lt (by omega)

/-! ### More on positions and slots -/

theorem fastAdd {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt (by omega)

theorem fastDiv {J : USize} {k : Nat} (hk : k < 2 ^ 32) : (J / USize.ofNat k).toNat = J.toNat / k := by
  rw [USize.toNat_div, fastLit hk]

theorem fastMod {J : USize} {k : Nat} (hk : k < 2 ^ 32) : (J % USize.ofNat k).toNat = J.toNat % k := by
  rw [USize.toNat_mod, fastLit hk]

theorem fastLt {J : USize} {k : Nat} (hk : k < 2 ^ 32) (h : J < USize.ofNat k) : J.toNat < k := by
  have := USize.lt_iff_toNat_lt.mp h
  rwa [fastLit hk] at this

theorem fastToU64 {J : USize} : J.toUInt64 = UInt64.ofNat J.toNat := by
  apply UInt64.toNat_inj.mp
  rw [USize.toNat_toUInt64, UInt64.toNat_ofNat']
  have := J.toNat_lt
  exact (Nat.mod_eq_of_lt this).symm

/-- A slot's number reads the same in an array that begins with it. -/
theorem Extends.slotNum {t t' : ByteArray} (h : Extends t t') {q : Nat} (hq : 2 * q + 1 < t.size) :
    _root_.Brotli.Decoder.slotNum t' q = _root_.Brotli.Decoder.slotNum t q := by
  simp only [Brotli.Decoder.slotNum]
  rw [h.2 _ (by omega), h.2 _ (by omega)]

theorem slotNum_lt (t : ByteArray) (q : Nat) : slotNum t q < 65536 := by
  unfold slotNum
  have := (t.data[2 * q]?.getD 0).toNat_lt
  have := (t.data[2 * q + 1]?.getD 0).toNat_lt
  omega

/-- A slot's word is its number. -/
theorem slot16_eq {t : ByteArray} {i : USize} (h : 2 * i.toNat + 2 ≤ t.size) (h32 : t.size < 2 ^ 32) :
    slot16 t i h h32 = UInt64.ofNat (slotNum t i.toNat) := by
  apply UInt64.toNat_inj.mp
  rw [slot16_toNat, UInt64.toNat_ofNat']
  have := slotNum_lt t i.toNat
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-! ### The fused insert-and-copy entries

From `f0`, for each insert-and-copy tree, 256 entries of 8 bytes indexed by the next 8 bits. -/

/-- The fused entry of a code word of `l ≤ 8` bits for symbol `sym`, at root index `j`, every field whole bytes, so
that each is one plain load: byte 0 the bits taken, byte 1 the symbol's class (`codeClass`, the state's `code`); then,
when the code word and both extra bits fit the 8 bits, the insert and copy lengths in bytes 4–5 and 6–7, and otherwise
the extra bits in bytes 2 and 3 and the lengths' lowest values in bytes 4–5 and 6–7. -/
@[inline] def icEntryOf (l sym j : UInt64) (hs : sym.toNat < 704) : UInt64 :=
  let ib := rowBits (insertRow sym hs)
  let cb := rowBits (copyRow sym hs)
  let ibase := rowBase (insertRow sym hs)
  let cbase := rowBase (copyRow sym hs)
  if l + ib + cb ≤ 8 then
    (l + ib + cb) ||| (codeClass sym <<< 8) ||| ((ibase + ((j >>> l) &&& (((1 : UInt64) <<< ib) - 1))) <<< 32) |||
      ((cbase + ((j >>> (l + ib)) &&& (((1 : UInt64) <<< cb) - 1))) <<< 48)
  else l ||| (codeClass sym <<< 8) ||| (ib <<< 16) ||| (cb <<< 24) ||| (ibase <<< 32) ||| (cbase <<< 48)

/-- The fused entry for root index `j` of an insert-and-copy code whose root slot there holds the word `v`, or 255 when
its code word is longer than 8 bits. -/
def icEntryU (v j : UInt64) : UInt64 :=
  if h : v &&& 15 ≤ 8 ∧ (v >>> 4) &&& 4095 < 704 then icEntryOf (v &&& 15) ((v >>> 4) &&& 4095) j (lt704 h.2) else 255

/-- What the fused entries' loop needs of the array: every tree's root slots are in it. -/
def ICReady (icBase : ByteArray) (nI : Nat) (t : ByteArray) : Prop :=
  ∀ ti, ti < nI → 2 * (u32At icBase ti + 256) ≤ t.size

theorem ICReady.extend {icBase t t' : ByteArray} {nI : Nat} (h : ICReady icBase nI t) (he : Extends t t') :
    ICReady icBase nI t' := fun ti hti => Nat.le_trans (h ti hti) he.1

theorem icStep_idx {icBase : ByteArray} {nI : Nat} (hn : nI ≤ 256) (hb : icBase.size = 4 * nI) {J : USize}
    (hJ : J < USize.ofNat (256 * nI)) : 4 * (J / USize.ofNat 256).toNat + 4 ≤ icBase.size := by
  have := fastLt (by omega) hJ
  rw [fastDiv (by decide), hb]
  omega

/-- Where entry `J`'s root slot is: tree `J / 256`'s root slot `J % 256`. -/
theorem icStep_pos {icBase t : ByteArray} {nI : Nat} (hn : nI ≤ 256) (hb : icBase.size = 4 * nI)
    (hb32 : icBase.size < 2 ^ 32) (h : ICReady icBase nI t) (s : t.size < 2 ^ 32) {J : USize}
    (hJ : J < USize.ofNat (256 * nI)) :
    ((slotWord icBase (J / USize.ofNat 256) (icStep_idx hn hb hJ) hb32).toUSize + J % USize.ofNat 256).toNat =
      u32At icBase (J.toNat / 256) + J.toNat % 256 ∧ 2 * (u32At icBase (J.toNat / 256) + J.toNat % 256) + 2 ≤ t.size := by
  have hJ' := fastLt (by omega) hJ
  have hv := slotWord_toNat (icStep_idx hn hb hJ) hb32
  rw [fastDiv (by decide)] at hv
  have hl := u32At_lt icBase (J.toNat / 256)
  have hm : (J % USize.ofNat 256).toNat = J.toNat % 256 := fastMod (by decide)
  have hmlt : J.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have hr := h (J.toNat / 256) (by omega)
  have hu : (slotWord icBase (J / USize.ofNat 256) (icStep_idx hn hb hJ) hb32).toUSize.toNat = u32At icBase (J.toNat / 256) := by
    rw [word_toUSize (by rw [hv]; exact hl), hv]
  refine ⟨?_, by omega⟩
  rw [fastAdd (by rw [hu, hm]; omega), hu, hm]

/-- Fused entry `J`, read from the array's root slot. -/
@[inline] def icStep (icBase : ByteArray) (nI : Nat) (hn : nI ≤ 256) (hb : icBase.size = 4 * nI)
    (hb32 : icBase.size < 2 ^ 32) (t : ByteArray) (h : ICReady icBase nI t) (s : t.size < 2 ^ 32) (J : USize)
    (hJ : J < USize.ofNat (256 * nI)) : UInt64 :=
  icEntryU (slot16 t ((slotWord icBase (J / USize.ofNat 256) (icStep_idx hn hb hJ) hb32).toUSize + J % USize.ofNat 256)
    (by rw [(icStep_pos hn hb hb32 h s hJ).1]; exact (icStep_pos hn hb hb32 h s hJ).2) s) (J % USize.ofNat 256).toUInt64

theorem icStep_eq {icBase : ByteArray} {nI : Nat} {hn : nI ≤ 256} {hb : icBase.size = 4 * nI}
    {hb32 : icBase.size < 2 ^ 32} {t : ByteArray} {h : ICReady icBase nI t} {s : t.size < 2 ^ 32} {J : USize}
    {hJ : J < USize.ofNat (256 * nI)} :
    icStep icBase nI hn hb hb32 t h s J hJ =
      icEntryU (UInt64.ofNat (slotNum t (u32At icBase (J.toNat / 256) + J.toNat % 256))) (UInt64.ofNat (J.toNat % 256)) := by
  unfold icStep
  rw [slot16_eq, (icStep_pos hn hb hb32 h s hJ).1, fastToU64, fastMod (by decide)]

/-- The fused entries of every insert-and-copy tree, appended. -/
def pushIC (icBase : ByteArray) (nI : Nat) (hn : nI ≤ 256) (hb : icBase.size = 4 * nI) (hb32 : icBase.size < 2 ^ 32)
    (t : ByteArray) (h : ICReady icBase nI t) (hc : t.size + 2048 * nI < 2 ^ 32) : ByteArray :=
  pushLoop (ICReady icBase nI) 8 (fun _ _ hr he => hr.extend he) (USize.ofNat (256 * nI))
    (icStep icBase nI hn hb hb32) t h 0
    (show t.size + 8 * ((USize.ofNat (256 * nI)).toNat - (0 : USize).toNat) < 2 ^ 32 by
      rw [fastLit (by omega), show (0 : USize).toNat = 0 from rfl, Nat.sub_zero]
      omega)

theorem pushIC_spec {icBase : ByteArray} {nI : Nat} {hn : nI ≤ 256} {hb : icBase.size = 4 * nI}
    {hb32 : icBase.size < 2 ^ 32} {t : ByteArray} {h : ICReady icBase nI t} {hc : t.size + 2048 * nI < 2 ^ 32} :
    (pushIC icBase nI hn hb hb32 t h hc).size = t.size + 2048 * nI ∧ Extends t (pushIC icBase nI hn hb hb32 t h hc) ∧
      ∀ ti, ti < nI → ∀ j, j < 256 → leAt (pushIC icBase nI hn hb hb32 t h hc) (t.size + 2048 * ti + 8 * j) 8 =
        (icEntryU (UInt64.ofNat (slotNum t (u32At icBase ti + j))) (UInt64.ofNat j)).toNat := by
  have h0 : (0 : USize).toNat = 0 := rfl
  have hN : (USize.ofNat (256 * nI)).toNat = 256 * nI := fastLit (by omega)
  have hf : ∀ (t t' : ByteArray) (h : ICReady icBase nI t) (h' : ICReady icBase nI t') s s' j hj, Extends t t' →
      icStep icBase nI hn hb hb32 t' h' s' j hj = icStep icBase nI hn hb hb32 t h s j hj := by
    intro t t' h h' s s' j hj he
    rw [icStep_eq, icStep_eq, he.slotNum (by have := (icStep_pos hn hb hb32 h s hj).2; omega)]
  unfold pushIC
  obtain ⟨s1, s2, s3⟩ := pushLoop_spec (w := 8) hf _ t h 0 (by rw [hN, h0, Nat.sub_zero]; omega) rfl
  refine ⟨by rw [s1, hN, h0]; omega, s2, fun ti hti j hj => ?_⟩
  have hk : (USize.ofNat (256 * ti + j)).toNat = 256 * ti + j := fastLit (by omega)
  have e := s3 (USize.ofNat (256 * ti + j)) (USize.lt_iff_toNat_lt.mpr (by rw [hk, hN]; omega))
    (USize.le_iff_toNat_le.mpr (by rw [h0]; omega))
  rw [show t.size + 2048 * ti + 8 * j = t.size + 8 * ((USize.ofNat (256 * ti + j)).toNat - USize.toNat 0) by
    rw [hk, h0]; omega, e, icStep_eq, hk, show (256 * ti + j) / 256 = ti by omega, show (256 * ti + j) % 256 = j by omega]
  exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-! ### The resolved context maps

From `l0`, for each literal block type and context, 4 bytes: its tree's table base; from `d0`, the same for each distance
block type and context. -/

theorem mapStep_base {base map : ByteArray} {nT : Nat} (hb : base.size = 4 * nT)
    (hlt : ∀ p : USize, ∀ h : p.toNat < map.size, (map.uget p h).toNat < nT) {J : USize} (hJ : J.toNat < map.size) :
    4 * (map.uget J hJ).toUSize.toNat + 4 ≤ base.size := by
  have := hlt J hJ
  rw [UInt8.toNat_toUSize, hb]
  omega

/-- The table base of the tree a map's entry `J` names. -/
@[inline] def mapStep (base map : ByteArray) (nT : Nat) (hb : base.size = 4 * nT) (hb32 : base.size < 2 ^ 32)
    (hm32 : map.size < 2 ^ 32) (hlt : ∀ p : USize, ∀ h : p.toNat < map.size, (map.uget p h).toNat < nT) (t : ByteArray)
    (_h : True) (_s : t.size < 2 ^ 32) (J : USize) (hJ : J < USize.ofNat map.size) : UInt64 :=
  slotWord base (map.uget J (fastLt hm32 hJ)).toUSize (mapStep_base hb hlt (fastLt hm32 hJ)) hb32

theorem mapStep_toNat {base map : ByteArray} {nT : Nat} {hb : base.size = 4 * nT} {hb32 : base.size < 2 ^ 32}
    {hm32 : map.size < 2 ^ 32} {hlt : ∀ p : USize, ∀ h : p.toNat < map.size, (map.uget p h).toNat < nT} {t : ByteArray}
    {h : True} {s : t.size < 2 ^ 32} {J : USize} {hJ : J < USize.ofNat map.size} :
    (mapStep base map nT hb hb32 hm32 hlt t h s J hJ).toNat = u32At base (byteN map J.toNat) := by
  unfold mapStep
  rw [slotWord_toNat, UInt8.toNat_toUSize, uget_toNat]
  rfl

/-- A map's entries resolved to their trees' table bases, appended. -/
def pushMap (base map : ByteArray) (nT : Nat) (hb : base.size = 4 * nT) (hb32 : base.size < 2 ^ 32)
    (hm32 : map.size < 2 ^ 32) (hlt : ∀ p : USize, ∀ h : p.toNat < map.size, (map.uget p h).toNat < nT) (t : ByteArray)
    (hc : t.size + 4 * map.size < 2 ^ 32) : ByteArray :=
  pushLoop (fun _ => True) 4 (fun _ _ _ _ => trivial) (USize.ofNat map.size) (mapStep base map nT hb hb32 hm32 hlt) t trivial 0
    (by rw [fastLit hm32, show (0 : USize).toNat = 0 from rfl, Nat.sub_zero]; exact hc)

theorem pushMap_spec {base map : ByteArray} {nT : Nat} {hb : base.size = 4 * nT} {hb32 : base.size < 2 ^ 32}
    {hm32 : map.size < 2 ^ 32} {hlt : ∀ p : USize, ∀ h : p.toNat < map.size, (map.uget p h).toNat < nT} {t : ByteArray}
    {hc : t.size + 4 * map.size < 2 ^ 32} :
    (pushMap base map nT hb hb32 hm32 hlt t hc).size = t.size + 4 * map.size ∧ Extends t (pushMap base map nT hb hb32 hm32 hlt t hc) ∧
      ∀ J, J < map.size → leAt (pushMap base map nT hb hb32 hm32 hlt t hc) (t.size + 4 * J) 4 = u32At base (byteN map J) := by
  have h0 : (0 : USize).toNat = 0 := rfl
  have hN : (USize.ofNat map.size).toNat = map.size := fastLit hm32
  unfold pushMap
  obtain ⟨s1, s2, s3⟩ := pushLoop_spec (P := fun _ => True) (w := 4) (hP := fun _ _ _ _ => trivial)
    (f := mapStep base map nT hb hb32 hm32 hlt) (fun _ _ _ _ _ _ _ _ _ => rfl) _ t trivial 0
    (by rw [hN, h0, Nat.sub_zero]; exact hc) rfl
  refine ⟨by rw [s1, hN, h0, Nat.sub_zero], s2, fun J hJ => ?_⟩
  have hk : (USize.ofNat J).toNat = J := fastLit (by omega)
  have e := s3 (USize.ofNat J) (USize.lt_iff_toNat_lt.mpr (by rw [hk, hN]; exact hJ)) (USize.le_iff_toNat_le.mpr (by rw [h0]; omega))
  rw [show t.size + 4 * J = t.size + 4 * ((USize.ofNat J).toNat - USize.toNat 0) by rw [hk, h0, Nat.sub_zero], e,
    mapStep_toNat, hk]
  exact Nat.mod_eq_of_lt (u32At_lt _ _)

/-! ### The shared distance table

From byte 256 of the arena, after the masks, 8 bytes for each distance symbol below 520: from 16 on, its extra bits in
the low byte, and in the high 4 bytes the distance before its extra bits, which add to it shifted by NPOSTFIX. -/

/-- The shared distance table's entry for distance symbol `dc`. -/
@[inline] def dEntry (np nd dc : UInt64) : UInt64 :=
  if dc < 16 then 0 else extraBitsFast np nd dc ||| (distFast np nd 0 0 0 0 dc 0 <<< 32)

@[inline] def dStep (np nd : UInt64) (t : ByteArray) (_h : True) (_s : t.size < 2 ^ 32) (j : USize)
    (_hj : j < USize.ofNat 520) : UInt64 :=
  dEntry np nd j.toUInt64

/-- The shared distance table, written in place from byte 256, in an array with room for it. -/
def writeDsh (np nd : UInt64) (t : ByteArray) (h : 4416 ≤ t.size) (h32 : t.size < 2 ^ 32) : ByteArray :=
  fillLoop (fun _ => True) 8 (fun _ _ _ _ => trivial) (USize.ofNat 520) (dStep np nd) ByteArray.empty trivial t
    ⟨Nat.zero_le _, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩ h32 (USize.ofNat 256) 0
    (by rw [fastLit (n := 256) (by decide)]; exact Nat.zero_le _)
    (by rw [fastLit (n := 256) (by decide), fastLit (n := 520) (by decide), show (0 : USize).toNat = 0 from rfl]; omega)

theorem writeDsh_spec {np nd : UInt64} {t : ByteArray} {h : 4416 ≤ t.size} {h32 : t.size < 2 ^ 32} :
    (writeDsh np nd t h h32).size = t.size ∧ (∀ q, q < 256 → (writeDsh np nd t h h32).data[q]? = t.data[q]?) ∧
      (∀ q, 4416 ≤ q → (writeDsh np nd t h h32).data[q]? = t.data[q]?) ∧
      ∀ dc, dc < 520 → leAt (writeDsh np nd t h h32) (256 + 8 * dc) 8 = (dEntry np nd (UInt64.ofNat dc)).toNat := by
  have h0 : (0 : USize).toNat = 0 := rfl
  have hN : (USize.ofNat 520).toNat = 520 := fastLit (by decide)
  have hO : (USize.ofNat 256).toNat = 256 := fastLit (by decide)
  have he : Extends ByteArray.empty t := ⟨Nat.zero_le _, fun _ hq => absurd hq (Nat.not_lt_zero _)⟩
  unfold writeDsh
  obtain ⟨s1, s2, s3⟩ := fillLoop_spec (P := fun _ => True) (w := 8) (hP := fun _ _ _ _ => trivial) (f := dStep np nd)
    (t0 := ByteArray.empty) (h0 := trivial) (fun _ _ _ _ _ _ _ _ _ => rfl) _ t he h32 (USize.ofNat 256) 0
    (by rw [hO]; exact Nat.zero_le _) (by rw [hO, hN, h0]; omega) rfl
  have s4 := fillLoop_above (P := fun _ => True) (w := 8) (hP := fun _ _ _ _ => trivial) (f := dStep np nd)
    (t0 := ByteArray.empty) (h0 := trivial) _ t he h32 (USize.ofNat 256) 0
    (by rw [hO]; exact Nat.zero_le _) (by rw [hO, hN, h0]; omega) rfl
  refine ⟨s1, fun q hq => s2 q (by rw [hO]; exact hq), fun q hq => s4 q (by rw [hO, hN, h0]; omega), fun dc hdc => ?_⟩
  have hk : (USize.ofNat dc).toNat = dc := fastLit (by omega)
  have e := s3 (USize.ofNat dc) (USize.lt_iff_toNat_lt.mpr (by rw [hk, hN]; exact hdc))
    (USize.le_iff_toNat_le.mpr (by rw [h0]; omega))
  rw [show 256 + 8 * dc = (USize.ofNat 256).toNat + 8 * ((USize.ofNat dc).toNat - USize.toNat 0) by rw [hk, h0, hO,
    Nat.sub_zero], e]
  unfold dStep
  rw [fastToU64, hk]
  exact Nat.mod_eq_of_lt (UInt64.toNat_lt _)

/-! ### Appended arrays -/

theorem byteN_append {t z : ByteArray} (q : Nat) : byteN (t ++ z) (t.size + q) = byteN z q := by
  unfold byteN
  rw [ByteArray.data_append, Array.getElem?_append_right (show t.data.size ≤ t.size + q from Nat.le_add_right _ _),
    show t.size + q - t.data.size = q from Nat.add_sub_cancel_left t.size q]

theorem leAt_append {t z : ByteArray} : ∀ {n q : Nat}, leAt (t ++ z) (t.size + q) n = leAt z q n
  | 0, _ => rfl
  | n + 1, q => by
    rw [leAt, leAt, byteN_append, show t.size + q + 1 = t.size + (q + 1) by omega, leAt_append]

/-- Four bytes from `4 i` are `u32At`'s number. -/
theorem leAt_u32 (z : ByteArray) (i : Nat) : leAt z (4 * i) 4 = u32At z i := by
  simp only [leAt, byteN, u32At, Nat.add_assoc, Nat.reduceAdd]
  omega

/-! ### The two-literal tables

For each literal block type the header chose, 256 entries of 4 bytes indexed by the next 8 bits: the bits taken in the
low byte, then how many literals the entry gives (2, 1, or 0 when the first code word is longer than 8 bits), then the
literals' bytes. Then, for each literal block type, 4 bytes: where its table is, or `0xFFFFFFFF`. -/

theorem slotAt_lt (t : ByteArray) (q : Nat) : (slotAt t q).1 < 16 ∧ (slotAt t q).2 < 4096 := by
  have := slotNum_lt t q
  simp only [slotAt]
  omega

theorem lookupSlots_lt (t : ByteArray) (base w : Nat) : (lookupSlots t base w).1 < 16 ∧ (lookupSlots t base w).2 < 4096 := by
  unfold lookupSlots
  dsimp only
  split
  · exact slotAt_lt _ _
  · exact slotAt_lt _ _

/-- `lookup`'s word, from the slot it ends at. -/
def lookupW (t : ByteArray) (base w : Nat) : UInt64 :=
  UInt64.ofNat ((lookupSlots t base w).1 + 16 * (lookupSlots t base w).2)

theorem lookup_eq_W {t : ByteArray} {base : USize} {w : UInt64} (hf : TableFits t base.toNat) (h32 : t.size < 2 ^ 32) :
    lookup t base w hf h32 = lookupW t base.toNat w.toNat := by
  obtain ⟨e1, e2⟩ := lookup_spec (w := w) hf h32
  have hl := lookup_lt (w := w) hf h32
  apply UInt64.toNat_inj.mp
  unfold lookupW
  rw [UInt64.toNat_ofNat', ← e1, ← e2, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The two-literal entry for a root index whose first literal's lookup word is `v1` and the second's, after it, `v2`. -/
def pairEntryU (v1 v2 : UInt64) : UInt64 :=
  let l1 := v1 &&& 15
  let l2 := v2 &&& 15
  let b1 := (v1 >>> 4) &&& 255
  let b2 := (v2 >>> 4) &&& 255
  if l1 ≤ 8 then
    if l1 + l2 ≤ 8 then (l1 + l2) ||| ((2 : UInt64) <<< 8) ||| (b1 <<< 16) ||| (b2 <<< 24)
    else l1 ||| ((1 : UInt64) <<< 8) ||| (b1 <<< 16)
  else 0

/-- The two-literal entry for root index `j` of the table at `tb`. -/
def pairAt (t : ByteArray) (tb j : Nat) : UInt64 :=
  pairEntryU (lookupW t tb j) (lookupW t tb (j / 2 ^ (lookupSlots t tb j).1))

/-- The entry after a first lookup `v1` at root index `j`. -/
@[inline] def pairWith (t : ByteArray) (tb : USize) (h : TableFits t tb.toNat) (s : t.size < 2 ^ 32) (j v1 : UInt64) :
    UInt64 :=
  pairEntryU v1 (lookup t tb (j >>> (v1 &&& 15)) h s)

@[inline] def pairStep (tb : USize) (t : ByteArray) (h : TableFits t tb.toNat) (s : t.size < 2 ^ 32) (j : USize)
    (_hj : j < USize.ofNat 256) : UInt64 :=
  pairWith t tb h s j.toUInt64 (lookup t tb j.toUInt64 h s)

theorem pairStep_eq {tb : USize} {t : ByteArray} {h : TableFits t tb.toNat} {s : t.size < 2 ^ 32} {j : USize}
    {hj : j < USize.ofNat 256} : pairStep tb t h s j hj = pairAt t tb.toNat j.toNat := by
  unfold pairStep pairWith pairAt
  rw [lookup_eq_W h s, lookup_eq_W h s, USize.toNat_toUInt64]
  congr 3
  have hb := lookupSlots_lt t tb.toNat j.toNat
  have hX : (lookupW t tb.toNat j.toNat).toNat = (lookupSlots t tb.toNat j.toNat).1 + 16 * (lookupSlots t tb.toNat j.toNat).2 :=
    u64_lit (by omega)
  have e : (lookupW t tb.toNat j.toNat &&& 15).toNat = (lookupSlots t tb.toNat j.toNat).1 := by
    rw [UInt64.toNat_and, hX, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [UInt64.toNat_shiftRight, e, USize.toNat_toUInt64, Nat.mod_eq_of_lt (show (lookupSlots t tb.toNat j.toNat).1 < 64 by omega),
    Nat.shiftRight_eq_div_pow]

/-- Whether type `ti`'s flag is set in four words of flags. -/
@[inline] def flagBit (w0 w1 w2 w3 ti : UInt64) : Bool :=
  ((if ti < 64 then w0 else if ti < 128 then w1 else if ti < 192 then w2 else w3) >>> (ti &&& 63)) &&& 1 == 1

/-- Whether literal type `k` gets a table: its flag is set and its contexts share a table. -/
def pairOnN (w0 w1 w2 w3 : UInt64) (lTriv : ByteArray) (k : Nat) : Bool :=
  flagBit w0 w1 w2 w3 (UInt64.ofNat k) && u32At lTriv k != 4294967295

/-- What the pair passes need of the array: each literal type's shared table, when it has one, fits. -/
def PairReady (lTriv : ByteArray) (nL : Nat) (t : ByteArray) : Prop :=
  ∀ ti, ti < nL → u32At lTriv ti ≠ 4294967295 → TableFits t (u32At lTriv ti)

theorem PairReady.extend {lTriv t t' : ByteArray} {nL : Nat} (h : PairReady lTriv nL t) (he : Extends t t') :
    PairReady lTriv nL t' := fun ti hti hne => (h ti hti hne).extend he

/-- Type `ti`'s shared table base, from its 4 bytes. -/
@[inline] def trivAt (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL) (hl32 : lTriv.size < 2 ^ 32) (ti : USize)
    (hti : ti.toNat < nL) : UInt64 :=
  slotWord lTriv ti (by rw [ht]; omega) hl32

theorem trivAt_toNat {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32} {ti : USize}
    {hti : ti.toNat < nL} : (trivAt lTriv nL ht hl32 ti hti).toNat = u32At lTriv ti.toNat := slotWord_toNat _ _

theorem trivAt_usize {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32} {ti : USize}
    {hti : ti.toNat < nL} : (trivAt lTriv nL ht hl32 ti hti).toUSize.toNat = u32At lTriv ti.toNat := by
  rw [word_toUSize (by rw [trivAt_toNat]; exact u32At_lt _ _), trivAt_toNat]

/-- Whether type `ti` gets a table. -/
@[inline] def pairOn (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL) (hl32 : lTriv.size < 2 ^ 32)
    (w0 w1 w2 w3 : UInt64) (ti : USize) (hti : ti.toNat < nL) : Bool :=
  flagBit w0 w1 w2 w3 ti.toUInt64 && trivAt lTriv nL ht hl32 ti hti != 4294967295

theorem pairOn_eq {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32}
    {w0 w1 w2 w3 : UInt64} {ti : USize} {hti : ti.toNat < nL} :
    pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti = pairOnN w0 w1 w2 w3 lTriv ti.toNat := by
  unfold pairOn pairOnN
  rw [fastToU64]
  congr 1
  have e : (trivAt lTriv nL ht hl32 ti hti != 4294967295) = (u32At lTriv ti.toNat != 4294967295) := by
    have hv := trivAt_toNat (ht := ht) (hl32 := hl32) (hti := hti)
    by_cases hc : u32At lTriv ti.toNat = 4294967295
    · have : trivAt lTriv nL ht hl32 ti hti = 4294967295 := UInt64.toNat_inj.mp (by rw [hv, hc]; rfl)
      rw [this, hc]
      rfl
    · have : trivAt lTriv nL ht hl32 ti hti ≠ 4294967295 := fun e => hc (by rw [← hv, e]; rfl)
      rw [bne_iff_ne.mpr this, bne_iff_ne.mpr hc]
  exact e

theorem pairOn_fits {lTriv t : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32}
    {w0 w1 w2 w3 : UInt64} {ti : USize} {hti : ti.toNat < nL} (h : PairReady lTriv nL t)
    (hon : pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti = true) :
    TableFits t (trivAt lTriv nL ht hl32 ti hti).toUSize.toNat := by
  rw [pairOn_eq] at hon
  unfold pairOnN at hon
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hon
  rw [trivAt_usize]
  exact h _ hti hon.2

/-- How many of the indices in `[a, a + len)` `fl` holds of. -/
def cntOn (fl : Nat → Bool) (a : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => (if fl a then 1 else 0) + cntOn fl (a + 1) len

theorem cntOn_le (fl : Nat → Bool) : ∀ (a len : Nat), cntOn fl a len ≤ len
  | _, 0 => Nat.le_refl _
  | a, len + 1 => by
    have := cntOn_le fl (a + 1) len
    simp only [cntOn]
    split <;> omega

theorem cntOn_succ (fl : Nat → Bool) (a len : Nat) :
    cntOn fl a (len + 1) = (if fl a then 1 else 0) + cntOn fl (a + 1) len := rfl

/-- One literal type's table, appended. -/
def pushPair (tb : USize) (t : ByteArray) (hf : TableFits t tb.toNat) (hc : t.size + 1024 < 2 ^ 32) : ByteArray :=
  pushLoop (fun t => TableFits t tb.toNat) 4 (fun _ _ h he => h.extend he) (USize.ofNat 256)
    (pairStep tb) t hf 0
    (show t.size + 4 * ((USize.ofNat 256).toNat - (0 : USize).toNat) < 2 ^ 32 by
      rw [fastLit (by decide), show (0 : USize).toNat = 0 from rfl]; exact hc)

theorem pushPair_spec {tb : USize} {t : ByteArray} {hf : TableFits t tb.toNat} {hc : t.size + 1024 < 2 ^ 32} :
    (pushPair tb t hf hc).size = t.size + 1024 ∧ Extends t (pushPair tb t hf hc) ∧
      ∀ j, j < 256 → leAt (pushPair tb t hf hc) (t.size + 4 * j) 4 = (pairAt t tb.toNat j).toNat % 2 ^ 32 := by
  have h0 : (0 : USize).toNat = 0 := rfl
  have hN : (USize.ofNat 256).toNat = 256 := fastLit (by decide)
  have hs : t.size < 2 ^ 32 := by omega
  have hfe : ∀ (t t' : ByteArray) (h : TableFits t tb.toNat) (h' : TableFits t' tb.toNat) s s' j hj, Extends t t' →
      pairStep tb t' h' s' j hj = pairStep tb t h s j hj := by
    intro t t' h h' s s' j hj he
    unfold pairStep pairWith
    rw [lookup_extend h s h' s' he, lookup_extend h s h' s' he]
  unfold pushPair
  obtain ⟨s1, s2, s3⟩ := pushLoop_spec (w := 4) hfe _ t hf 0 (by rw [hN, h0]; omega) rfl
  refine ⟨by rw [s1, hN, h0], s2, fun j hj => ?_⟩
  have hk : (USize.ofNat j).toNat = j := fastLit (by omega)
  have e := s3 (USize.ofNat j) (USize.lt_iff_toNat_lt.mpr (by rw [hk, hN]; exact hj)) (USize.le_iff_toNat_le.mpr (by rw [h0]; omega))
  rw [show t.size + 4 * j = t.size + 4 * ((USize.ofNat j).toNat - USize.toNat 0) by rw [hk, h0, Nat.sub_zero], e, pairStep_eq,
    hk]

/-- The chosen literal types' tables, from type `ti` on, appended in order. -/
def pairsPass (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL) (hl32 : lTriv.size < 2 ^ 32) (w0 w1 w2 w3 : UInt64)
    (n : USize) (hn : n.toNat = nL) (t : ByteArray) (h : PairReady lTriv nL t) (ti : USize)
    (hc : t.size + 1024 * (n.toNat - ti.toNat) < 2 ^ 32) : ByteArray :=
  if hti : ti < n then
    have hti' : ti.toNat < nL := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hti
    have hs := fastIdx_succ hti
    have hm := mul_step (w := 1024) (USize.lt_iff_toNat_lt.mp hti)
    if hon : pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti' = true then
      pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn
        (pushPair (trivAt lTriv nL ht hl32 ti hti').toUSize t (pairOn_fits h hon) (by omega))
        (h.extend pushPair_spec.2.1) (ti + USize.ofNat 1) (by rw [pushPair_spec.1, hs]; omega)
    else pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn t h (ti + USize.ofNat 1) (by rw [hs]; omega)
  else t
termination_by n.toNat - ti.toNat
decreasing_by
  all_goals
    have := USize.lt_iff_toNat_lt.mp hti
    rw [fastIdx_succ hti]
    omega

/-- A two-literal entry reads the same in an array that begins with the one it was made for. -/
theorem pairAt_extend {t t' : ByteArray} {tb : Nat} (hf : TableFits t tb) (he : Extends t t') (j : Nat) :
    pairAt t' tb j = pairAt t tb j := by
  unfold pairAt lookupW
  rw [lookupSlots_extend hf he, lookupSlots_extend hf he]

theorem pairsPass_spec {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32}
    {w0 w1 w2 w3 : UInt64} {n : USize} {hn : n.toNat = nL} :
    ∀ (N : Nat) (t : ByteArray) (h : PairReady lTriv nL t) (ti : USize)
      (hc : t.size + 1024 * (n.toNat - ti.toNat) < 2 ^ 32), n.toNat - ti.toNat = N →
      Extends t (pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn t h ti hc) ∧
      (pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn t h ti hc).size =
        t.size + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat (n.toNat - ti.toNat) ∧
      ∀ k, ti.toNat ≤ k → k < nL → pairOnN w0 w1 w2 w3 lTriv k = true → ∀ j, j < 256 →
        leAt (pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn t h ti hc)
          (t.size + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat (k - ti.toNat) + 4 * j) 4 =
          (pairAt t (u32At lTriv k) j).toNat % 2 ^ 32 := by
  intro N
  induction N with
  | zero =>
    intro t h ti hc hN
    have hti : ¬ ti < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [pairsPass, dite_eq_right hti]
    refine ⟨Extends.refl t, by rw [hN]; rfl, fun k h1 h2 _ => ?_⟩
    omega
  | succ N ih =>
    intro t h ti hc hN
    have hti : ti < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hti' : ti.toNat < nL := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hti
    have hs := fastIdx_succ hti
    have hlen : n.toNat - ti.toNat = (n.toNat - (ti.toNat + 1)) + 1 := by omega
    rw [pairsPass, dite_eq_left hti]
    dsimp only
    by_cases hon : pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti' = true
    · rw [dite_eq_left hon]
      have hon' := hon
      rw [pairOn_eq] at hon'
      obtain ⟨p1, p2, p3⟩ := pushPair_spec (tb := (trivAt lTriv nL ht hl32 ti hti').toUSize) (t := t)
        (hf := pairOn_fits h hon) (hc := by omega)
      have hm := mul_step (w := 1024) (USize.lt_iff_toNat_lt.mp hti)
      obtain ⟨i1, i2, i3⟩ := ih _ (h.extend p2) (ti + USize.ofNat 1) (by rw [p1, hs]; omega) (by rw [hs]; omega)
      generalize pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn _ _ (ti + USize.ofNat 1) _ = r at i1 i2 i3
      refine ⟨p2.trans i1, ?_, fun k h1 h2 hk j hj => ?_⟩
      · rw [i2, p1, hs, hlen, cntOn_succ, ite_eq_left hon']
        omega
      · by_cases hke : k = ti.toNat
        · subst hke
          rw [Nat.sub_self, show cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat 0 = 0 from rfl, Nat.mul_zero, Nat.add_zero,
            i1.leAt (by rw [p1]; omega), p3 j hj, trivAt_usize]
        · have hk1 : k - ti.toNat = (k - (ti.toNat + 1)) + 1 := by omega
          have e := i3 k (by rw [hs]; omega) h2 hk j hj
          rw [hs, p1, pairAt_extend (h k h2 (by unfold pairOnN at hk; simp only [Bool.and_eq_true, bne_iff_ne] at hk; exact hk.2))
            p2] at e
          rw [hk1, cntOn_succ, ite_eq_left hon', Nat.mul_add, Nat.mul_one, ← Nat.add_assoc]
          exact e
    · rw [dite_eq_right hon]
      have hon' : pairOnN w0 w1 w2 w3 lTriv ti.toNat = false := by
        rw [← pairOn_eq (ht := ht) (hl32 := hl32) (hti := hti')]
        cases e : pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti' with
        | true => exact absurd e hon
        | false => rfl
      obtain ⟨i1, i2, i3⟩ := ih t h (ti + USize.ofNat 1) (by rw [hs]; omega) (by rw [hs]; omega)
      generalize pairsPass lTriv nL ht hl32 w0 w1 w2 w3 n hn t h (ti + USize.ofNat 1) _ = r at i1 i2 i3
      have hoff : ¬ pairOnN w0 w1 w2 w3 lTriv ti.toNat = true := by rw [hon']; decide
      refine ⟨i1, ?_, fun k h1 h2 hk j hj => ?_⟩
      · rw [i2, hs, hlen, cntOn_succ, ite_eq_right hoff, Nat.zero_add]
      · have hke : k ≠ ti.toNat := fun e => by rw [e, hon'] at hk; cases hk
        have hk1 : k - ti.toNat = (k - (ti.toNat + 1)) + 1 := by omega
        have e := i3 k (by rw [hs]; omega) h2 hk j hj
        rw [hs] at e
        rw [hk1, cntOn_succ, ite_eq_right hoff, Nat.zero_add]
        exact e

/-- The chosen types' tables' positions, from type `ti` on, appended: the next chosen type's table at `p0 + 1024 cnt`,
`0xFFFFFFFF` for a type not chosen. -/
def ixPass (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL) (hl32 : lTriv.size < 2 ^ 32) (w0 w1 w2 w3 : UInt64)
    (n : USize) (hn : n.toNat = nL) (p0 : UInt64) (t : ByteArray) (ti : USize) (cnt : UInt64) : ByteArray :=
  if hti : ti < n then
    have hti' : ti.toNat < nL := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hti
    ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0
      (pushLE t (if pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti' then p0 + 1024 * cnt else 4294967295) 4)
      (ti + USize.ofNat 1) (if pairOn lTriv nL ht hl32 w0 w1 w2 w3 ti hti' then cnt + 1 else cnt)
  else t
termination_by n.toNat - ti.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.mp hti
  rw [fastIdx_succ hti]
  omega

theorem ixPass_spec {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32}
    {w0 w1 w2 w3 : UInt64} {n : USize} {hn : n.toNat = nL} {p0 : UInt64} :
    ∀ (N : Nat) (t : ByteArray) (ti : USize) (cnt : UInt64), n.toNat - ti.toNat = N →
      p0.toNat + 1024 * (cnt.toNat + cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat (n.toNat - ti.toNat)) < 2 ^ 32 →
      Extends t (ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0 t ti cnt) ∧
      (ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0 t ti cnt).size = t.size + 4 * (n.toNat - ti.toNat) ∧
      ∀ k, ti.toNat ≤ k → k < nL → leAt (ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0 t ti cnt) (t.size + 4 * (k - ti.toNat)) 4 =
        if pairOnN w0 w1 w2 w3 lTriv k then p0.toNat + 1024 * (cnt.toNat + cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat (k - ti.toNat))
        else 4294967295 := by
  intro N
  induction N with
  | zero =>
    intro t ti cnt hN _
    have hti : ¬ ti < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [ixPass, dite_eq_right hti]
    refine ⟨Extends.refl t, by rw [hN]; rfl, fun k h1 h2 => ?_⟩
    omega
  | succ N ih =>
    intro t ti cnt hN hp
    have hti : ti < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hti' : ti.toNat < nL := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hti
    have hs := fastIdx_succ hti
    have hlen : n.toNat - ti.toNat = (n.toNat - (ti.toNat + 1)) + 1 := by omega
    rw [ixPass, dite_eq_left hti]
    dsimp only
    rw [pairOn_eq]
    have hcl := cntOn_le (pairOnN w0 w1 w2 w3 lTriv) (ti.toNat + 1) (n.toNat - (ti.toNat + 1))
    rw [hlen, cntOn_succ] at hp
    have hcnt : (cnt + 1).toNat = cnt.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by split at hp <;> omega)
    by_cases hb : pairOnN w0 w1 w2 w3 lTriv ti.toNat = true
    · rw [ite_eq_left hb] at hp
      rw [ite_eq_left hb, ite_eq_left hb]
      have hv : (p0 + 1024 * cnt).toNat = p0.toNat + 1024 * cnt.toNat := by
        rw [UInt64.toNat_add, UInt64.toNat_mul, show (1024 : UInt64).toNat = 1024 from rfl,
          Nat.mod_eq_of_lt (a := 1024 * cnt.toNat) (by omega)]
        exact Nat.mod_eq_of_lt (by omega)
      obtain ⟨i1, i2, i3⟩ := ih (pushLE t (p0 + 1024 * cnt) 4) (ti + USize.ofNat 1) (cnt + 1) (by rw [hs]; omega)
        (by rw [hs, hcnt]; omega)
      generalize ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0 (pushLE t (p0 + 1024 * cnt) 4) (ti + USize.ofNat 1) (cnt + 1) = r
        at i1 i2 i3
      have he1 := Extends.pushLE t (p0 + 1024 * cnt) 4
      have hsz := size_pushLE 4 t (p0 + 1024 * cnt)
      refine ⟨he1.trans i1, by rw [i2, hsz, hs, hlen]; omega, fun k h1 h2 => ?_⟩
      by_cases hke : k = ti.toNat
      · subst hke
        rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, i1.leAt (Nat.le_of_eq hsz.symm), leAt_pushLE, ite_eq_left hb,
          show cntOn (pairOnN w0 w1 w2 w3 lTriv) ti.toNat 0 = 0 from rfl, Nat.add_zero, hv]
        exact Nat.mod_eq_of_lt (by omega)
      · have hk1 : k - ti.toNat = (k - (ti.toNat + 1)) + 1 := by omega
        have e := i3 k (by rw [hs]; omega) h2
        rw [hsz, hs, hcnt] at e
        rw [show t.size + 4 * (k - ti.toNat) = t.size + 4 + 4 * (k - (ti.toNat + 1)) by rw [hk1]; omega, e, hk1, cntOn_succ,
          ite_eq_left hb]
        by_cases hk : pairOnN w0 w1 w2 w3 lTriv k = true
        · rw [ite_eq_left hk, ite_eq_left hk]
          omega
        · rw [ite_eq_right hk, ite_eq_right hk]
    · rw [ite_eq_right hb] at hp
      rw [ite_eq_right hb, ite_eq_right hb]
      obtain ⟨i1, i2, i3⟩ := ih (pushLE t 4294967295 4) (ti + USize.ofNat 1) cnt (by rw [hs]; omega) (by rw [hs]; omega)
      generalize ixPass lTriv nL ht hl32 w0 w1 w2 w3 n hn p0 (pushLE t 4294967295 4) (ti + USize.ofNat 1) cnt = r at i1 i2 i3
      have he1 := Extends.pushLE t 4294967295 4
      have hsz := size_pushLE 4 t 4294967295
      refine ⟨he1.trans i1, by rw [i2, hsz, hs, hlen]; omega, fun k h1 h2 => ?_⟩
      by_cases hke : k = ti.toNat
      · subst hke
        rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, i1.leAt (Nat.le_of_eq hsz.symm), leAt_pushLE, ite_eq_right hb]
        rfl
      · have hk1 : k - ti.toNat = (k - (ti.toNat + 1)) + 1 := by omega
        have e := i3 k (by rw [hs]; omega) h2
        rw [hsz, hs] at e
        rw [show t.size + 4 * (k - ti.toNat) = t.size + 4 + 4 * (k - (ti.toNat + 1)) by rw [hk1]; omega, e, hk1, cntOn_succ,
          ite_eq_right hb, Nat.zero_add]

/-! ### Which literal types get two-literal tables (a policy, with no claim but its bounds) -/

/-- How many of a shared table's 256 root indices give two literals, from `j` on. -/
def pairCount (t : ByteArray) (tb : USize) (h : TableFits t tb.toNat) (s : t.size < 2 ^ 32) (j : USize) (acc : UInt64) :
    UInt64 :=
  if hj : j < USize.ofNat 256 then
    pairCount t tb h s (j + USize.ofNat 1) (if (pairStep tb t h s j hj >>> 8) &&& 255 == 2 then acc + 1 else acc)
  else acc
termination_by 256 - j.toNat
decreasing_by
  have := fastLt (by decide) hj
  rw [fastIdx_succ hj]
  omega

/-- Sets type `q`'s flag in the word for the types from `lo`. -/
@[inline] def setFlag (q lo w : UInt64) : UInt64 :=
  if lo ≤ q ∧ q < lo + 64 then w ||| ((1 : UInt64) <<< (q &&& 63)) else w

theorem pairFlags_fits {lTriv t : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hl32 : lTriv.size < 2 ^ 32}
    {ti : USize} {hti : ti.toNat < nL} (hr : PairReady lTriv nL t) (hne : ¬ trivAt lTriv nL ht hl32 ti hti = 4294967295) :
    TableFits t (trivAt lTriv nL ht hl32 ti hti).toUSize.toNat := by
  rw [trivAt_usize]
  refine hr _ hti fun e => hne (UInt64.toNat_inj.mp ?_)
  rw [trivAt_toNat, e]
  rfl

/-- The flags of the literal types from `ti` on whose contexts share a table whose root indices give two literals at
least 75% of the time (P46). -/
def pairFlags (t : ByteArray) (s : t.size < 2 ^ 32) (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL)
    (hl32 : lTriv.size < 2 ^ 32) (hr : PairReady lTriv nL t) (n : USize) (hn : n.toNat = nL) (ti : USize)
    (w0 w1 w2 w3 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
  if hti : ti < n then
    have hti' : ti.toNat < nL := by rw [← hn]; exact USize.lt_iff_toNat_lt.mp hti
    if hne : trivAt lTriv nL ht hl32 ti hti' = 4294967295 then
      pairFlags t s lTriv nL ht hl32 hr n hn (ti + USize.ofNat 1) w0 w1 w2 w3
    else if 192 ≤ pairCount t (trivAt lTriv nL ht hl32 ti hti').toUSize (pairFlags_fits hr hne) s 0 0 then
      pairFlags t s lTriv nL ht hl32 hr n hn (ti + USize.ofNat 1) (setFlag ti.toUInt64 0 w0) (setFlag ti.toUInt64 64 w1)
        (setFlag ti.toUInt64 128 w2) (setFlag ti.toUInt64 192 w3)
    else pairFlags t s lTriv nL ht hl32 hr n hn (ti + USize.ofNat 1) w0 w1 w2 w3
  else (w0, w1, w2, w3)
termination_by n.toNat - ti.toNat
decreasing_by
  all_goals
    have := USize.lt_iff_toNat_lt.mp hti
    rw [fastIdx_succ hti]
    omega

/-- A root slot's insertion and copy lengths at their middles, added to the sums when its code word is at most 8 bits. -/
@[inline] def expAdd (v ins cpy : UInt64) : UInt64 × UInt64 :=
  if h : v &&& 15 ≤ 8 ∧ (v >>> 4) &&& 4095 < 704 then
    (ins + (2 : UInt64) * rowBase (insertRow ((v >>> 4) &&& 4095) (lt704 h.2)) +
        (((1 : UInt64) <<< rowBits (insertRow ((v >>> 4) &&& 4095) (lt704 h.2))) - 1),
      cpy + (2 : UInt64) * rowBase (copyRow ((v >>> 4) &&& 4095) (lt704 h.2)) +
        (((1 : UInt64) <<< rowBits (copyRow ((v >>> 4) &&& 4095) (lt704 h.2))) - 1))
  else (ins, cpy)

theorem expLits_idx {t : ByteArray} {base j : USize} (hr : 2 * (base.toNat + 256) ≤ t.size) (s : t.size < 2 ^ 32)
    (hj : j < USize.ofNat 256) : 2 * (base + j).toNat + 2 ≤ t.size := by
  have := fastLt (by decide) hj
  rw [fastAdd (by omega)]
  omega

/-- The insert-and-copy root slots' weights from `j` on, each slot one share. -/
def expLits (t : ByteArray) (s : t.size < 2 ^ 32) (base : USize) (hr : 2 * (base.toNat + 256) ≤ t.size) (j : USize)
    (ins cpy : UInt64) : UInt64 × UInt64 :=
  if hj : j < USize.ofNat 256 then
    match expAdd (slot16 t (base + j) (expLits_idx hr s hj) s) ins cpy with
    | (a, b) => expLits t s base hr (j + USize.ofNat 1) a b
  else (ins, cpy)
termination_by 256 - j.toNat
decreasing_by
  have := fastLt (by decide) hj
  rw [fastIdx_succ hj]
  omega

/-! ### The derived tables -/

/-- The table at `base` lies within the first `lim` bytes. -/
structure TableIn (t : ByteArray) (base lim : Nat) : Prop where
  root : 2 * (base + 256) ≤ lim
  sub : ∀ r, r < 256 → 8 < (slotAt t (base + r)).1 →
    (slotAt t (base + r)).1 ≤ 15 ∧ 2 * (base + (slotAt t (base + r)).2 + 2 ^ ((slotAt t (base + r)).1 - 8)) ≤ lim

theorem TableIn.fits {t : ByteArray} {b lim : Nat} (h : TableIn t b lim) (hl : lim ≤ t.size) : TableFits t b :=
  ⟨Nat.le_trans h.root hl, fun r hr hb => ⟨(h.sub r hr hb).1, Nat.le_trans (h.sub r hr hb).2 hl⟩⟩

theorem TableFits.tableIn {t t' : ByteArray} {b lim : Nat} (h : TableFits t b) (he : Extends t t') (hl : t.size ≤ lim) :
    TableIn t' b lim := by
  have hr := h.root
  have hs : ∀ r, r < 256 → slotAt t' (b + r) = slotAt t (b + r) := fun r hr' => he.slotAt (by omega)
  refine ⟨by omega, fun r hr' hb => ?_⟩
  rw [hs r hr'] at hb ⊢
  obtain ⟨h1, h2⟩ := h.sub r hr' hb
  exact ⟨h1, by omega⟩

/-- The most the derived tables add to an arena: up to 15 bytes of padding (at least 8, after the last table), the fused
entries, the resolved maps, the trees' bases, a two-literal table for each literal type and their positions. -/
def tabMax (nL nI nD : Nat) : Nat := 15 + 2052 * nI + 1284 * nL + 16 * nD

/-- The padding after the last table: at least 8 bytes, so that an 8-byte read of a slot stays in the arena, up to a
multiple of 8. -/
def padOf (n : Nat) : Nat := 8 + (8 - n % 8) % 8

theorem padOf_spec (n : Nat) : 8 ≤ padOf n ∧ padOf n ≤ 15 ∧ (n + padOf n) % 8 = 0 := by
  unfold padOf
  omega

/-- What the builder needs of a header's arrays other than the arena, with no mention of the spec. -/
structure TabArrs (litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat) : Prop where
  nL256 : nL ≤ 256
  nI256 : nI ≤ 256
  nD256 : nD ≤ 256
  litSize : litBase.size = 4 * treesL
  trees256 : treesL ≤ 256
  lMapSize : lMap.size = 64 * nL
  lMapLt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < treesL
  icSize : icBase.size = 4 * nI
  dSize : dBase.size = 4 * treesD
  treesD256 : treesD ≤ 256
  dMapSize : dMap.size = 4 * nD
  dMapLt : ∀ p : USize, ∀ h : p.toNat < dMap.size, (dMap.uget p h).toNat < treesD
  trivSize : lTriv.size = 4 * nL

/-- What the builder needs of a header's arena and arrays, with no mention of the spec. -/
structure TabArgs (A litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat) : Prop where
  arrs : TabArrs litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD
  size : A.size + tabMax nL nI nD < 2 ^ 32
  pre : 4416 ≤ A.size
  masks : ∀ n, n < 32 → leAt A (8 * n) 8 = 2 ^ n - 1
  litFits : ∀ tree, tree < treesL → TableFits A (u32At litBase tree)
  icFits : ∀ t, t < nI → TableFits A (u32At icBase t)
  dFits : ∀ tree, tree < treesD → TableFits A (u32At dBase tree)
  trivFits : ∀ t, t < nL → u32At lTriv t ≠ 4294967295 → TableFits A (u32At lTriv t)

/-! ### The stages, each taking the array so far and never the arena it began as -/

/-- The two-literal tables, then their positions. -/
def tabLast (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL) (hn : nL ≤ 256) (w0 w1 w2 w3 : UInt64)
    (T : ByteArray) (hP : PairReady lTriv nL T) (hs : T.size + 1028 * nL < 2 ^ 32) : ByteArray :=
  ixPass lTriv nL ht (by omega) w0 w1 w2 w3 (USize.ofNat nL) (fastLit (by omega)) (UInt64.ofNat T.size)
    (pairsPass lTriv nL ht (by omega) w0 w1 w2 w3 (USize.ofNat nL) (fastLit (by omega)) T hP 0
      (by rw [fastLit (by omega), show (0 : USize).toNat = 0 from rfl, Nat.sub_zero]; omega)) 0 0

/-- The insert-and-copy trees' bases, then the rest. -/
def tab6 (icBase lTriv : ByteArray) (nL nI : Nat) (hic : icBase.size = 4 * nI) (ht : lTriv.size = 4 * nL) (hn : nL ≤ 256)
    (w0 w1 w2 w3 : UInt64) (T : ByteArray) (hP : PairReady lTriv nL T) (hs : T.size + 4 * nI + 1028 * nL < 2 ^ 32) :
    ByteArray :=
  tabLast lTriv nL ht hn w0 w1 w2 w3 (T ++ icBase) (hP.extend (Extends.append T icBase))
    (by rw [ByteArray.size_append, hic]; omega)

/-- The resolved distance map, then the rest. -/
def tab4 (icBase dBase dMap lTriv : ByteArray) (nL nI nD treesD : Nat) (hic : icBase.size = 4 * nI)
    (hd : dBase.size = 4 * treesD) (hd256 : treesD ≤ 256) (hdm : dMap.size = 4 * nD) (hnD : nD ≤ 256)
    (hdlt : ∀ p : USize, ∀ h : p.toNat < dMap.size, (dMap.uget p h).toNat < treesD) (ht : lTriv.size = 4 * nL)
    (hn : nL ≤ 256) (w0 w1 w2 w3 : UInt64) (T : ByteArray) (hP : PairReady lTriv nL T)
    (hs : T.size + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32) : ByteArray :=
  tab6 icBase lTriv nL nI hic ht hn w0 w1 w2 w3
    (pushMap dBase dMap treesD hd (by omega) (by omega) hdlt T (by rw [hdm]; omega)) (hP.extend pushMap_spec.2.1)
    (by rw [pushMap_spec.1, hdm]; omega)

/-- The resolved literal map, then the rest. -/
def tab3 (litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat)
    (ha : TabArrs litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) (w0 w1 w2 w3 : UInt64) (T : ByteArray)
    (hP : PairReady lTriv nL T) (hs : T.size + 256 * nL + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32) : ByteArray :=
  tab4 icBase dBase dMap lTriv nL nI nD treesD ha.icSize ha.dSize ha.treesD256 ha.dMapSize ha.nD256 ha.dMapLt ha.trivSize
    ha.nL256 w0 w1 w2 w3
    (pushMap litBase lMap treesL ha.litSize (by have := ha.litSize; have := ha.trees256; omega)
      (by have := ha.lMapSize; have := ha.nL256; omega) ha.lMapLt T (by rw [ha.lMapSize]; omega))
    (hP.extend pushMap_spec.2.1) (by rw [pushMap_spec.1, ha.lMapSize]; omega)

/-- The fused insert-and-copy entries, then the rest. -/
def tabFrom (litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat)
    (ha : TabArrs litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) (w0 w1 w2 w3 : UInt64) (T : ByteArray)
    (hI : ICReady icBase nI T) (hP : PairReady lTriv nL T)
    (hs : T.size + 2048 * nI + 256 * nL + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32) : ByteArray :=
  tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3
    (pushIC icBase nI ha.nI256 ha.icSize (by have := ha.icSize; have := ha.nI256; omega) T hI (by omega))
    (hP.extend pushIC_spec.2.1) (by rw [pushIC_spec.1]; omega)

/-- The derived tables appended to the arena `A`, after its padding, with the two-literal tables for the literal types
flagged in `w0`–`w3`. -/
def buildTab (A litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat)
    (h : TabArgs A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) (w0 w1 w2 w3 : UInt64) : ByteArray :=
  tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h.arrs w0 w1 w2 w3 (pushLE A 0 (padOf A.size))
    (fun ti hti => Nat.le_trans (h.icFits ti hti).root (by rw [size_pushLE]; omega))
    (PairReady.extend (fun ti hti hne => h.trivFits ti hti hne) (Extends.pushLE A 0 _))
    (by have h1 := h.size; have h2 := padOf_spec A.size; rw [size_pushLE]; unfold tabMax at h1; omega)

/-! ### What the stages leave, in the array they end with -/

/-- The two-literal tables from `p0`, then their positions. -/
def PairsAt (r lTriv : ByteArray) (nL : Nat) (w0 w1 w2 w3 : UInt64) (p0 : Nat) : Prop :=
  r.size = p0 + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL + 4 * nL ∧
  ∀ ti, ti < nL →
    leAt r (p0 + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL + 4 * ti) 4 =
      (if pairOnN w0 w1 w2 w3 lTriv ti then p0 + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 ti else 4294967295) ∧
    (pairOnN w0 w1 w2 w3 lTriv ti = true → ∀ j, j < 256 →
      leAt r (p0 + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 ti + 4 * j) 4 = (pairAt r (u32At lTriv ti) j).toNat % 2 ^ 32)

/-- The insert-and-copy trees' bases from `p`. -/
def IresAt (r icBase : ByteArray) (nI p : Nat) : Prop := ∀ t, t < nI → leAt r (p + 4 * t) 4 = u32At icBase t

/-- The shared distance table from `p`. -/
def DshAt (r : ByteArray) (np nd : UInt64) (p : Nat) : Prop :=
  ∀ dc, dc < 520 → leAt r (p + 8 * dc) 8 = (dEntry np nd (UInt64.ofNat dc)).toNat

/-- A resolved map from `p`. -/
def MapAt (r base map : ByteArray) (p : Nat) : Prop := ∀ J, J < map.size → leAt r (p + 4 * J) 4 = u32At base (byteN map J)

/-- The fused insert-and-copy entries from `p`. -/
def IcAt (r icBase : ByteArray) (nI p : Nat) : Prop :=
  ∀ t, t < nI → ∀ j, j < 256 →
    leAt r (p + 2048 * t + 8 * j) 8 = (icEntryU (UInt64.ofNat (slotNum r (u32At icBase t + j))) (UInt64.ofNat j)).toNat

theorem PairsAt.at {r lTriv : ByteArray} {nL : Nat} {w0 w1 w2 w3 : UInt64} {p p' : Nat}
    (h : PairsAt r lTriv nL w0 w1 w2 w3 p) (e : p = p') : PairsAt r lTriv nL w0 w1 w2 w3 p' := by subst e; exact h

theorem IresAt.at {r icBase : ByteArray} {nI p p' : Nat} (h : IresAt r icBase nI p) (e : p = p') : IresAt r icBase nI p' := by
  subst e; exact h

theorem DshAt.at {r : ByteArray} {np nd : UInt64} {p p' : Nat} (h : DshAt r np nd p) (e : p = p') : DshAt r np nd p' := by
  subst e; exact h

theorem MapAt.at {r base map : ByteArray} {p p' : Nat} (h : MapAt r base map p) (e : p = p') : MapAt r base map p' := by
  subst e; exact h

theorem IcAt.at {r icBase : ByteArray} {nI p p' : Nat} (h : IcAt r icBase nI p) (e : p = p') : IcAt r icBase nI p' := by
  subst e; exact h

theorem cntOn_lt (fl : Nat → Bool) : ∀ (len a k : Nat), fl k = true → a ≤ k → k < a + len →
    cntOn fl a (k - a) + 1 ≤ cntOn fl a len
  | 0, _, _, _, _, h2 => absurd h2 (by omega)
  | len + 1, a, k, hk, h1, h2 => by
    rw [cntOn_succ]
    by_cases hka : k = a
    · subst hka
      rw [Nat.sub_self, show cntOn fl k 0 = 0 from rfl, ite_eq_left hk]
      omega
    · have ih := cntOn_lt fl len (a + 1) k hk (by omega) (by omega)
      rw [show k - a = (k - (a + 1)) + 1 by omega, cntOn_succ]
      omega

theorem tabLast_spec {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL} {hn : nL ≤ 256} {w0 w1 w2 w3 : UInt64}
    {T : ByteArray} {hP : PairReady lTriv nL T} {hs : T.size + 1028 * nL < 2 ^ 32} :
    Extends T (tabLast lTriv nL ht hn w0 w1 w2 w3 T hP hs) ∧
      PairsAt (tabLast lTriv nL ht hn w0 w1 w2 w3 T hP hs) lTriv nL w0 w1 w2 w3 T.size := by
  have hN : (USize.ofNat nL).toNat = nL := fastLit (by omega)
  have h0 : (0 : USize).toNat = 0 := rfl
  have hl32 : lTriv.size < 2 ^ 32 := by omega
  have hcl := cntOn_le (pairOnN w0 w1 w2 w3 lTriv) 0 nL
  unfold tabLast
  obtain ⟨a1, a2, a3⟩ := pairsPass_spec (ht := ht) (hl32 := hl32) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3)
    (n := USize.ofNat nL) (hn := fastLit (by omega)) _ T hP 0 (by rw [hN, h0, Nat.sub_zero]; omega) rfl
  have a2' : _ = T.size + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL := a2.trans (by rw [hN]; rfl)
  have hp0 : (UInt64.ofNat T.size).toNat = T.size := u64_lit (by omega)
  obtain ⟨b1, b2, b3⟩ := ixPass_spec (ht := ht) (hl32 := hl32) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3)
    (n := USize.ofNat nL) (hn := fastLit (by omega)) (p0 := UInt64.ofNat T.size) _
    (pairsPass lTriv nL ht hl32 w0 w1 w2 w3 (USize.ofNat nL) (fastLit (by omega)) T hP 0
      (by rw [hN, h0, Nat.sub_zero]; omega)) 0 0 rfl
    (by rw [hp0, hN, h0, Nat.sub_zero, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_add]; omega)
  have b2' : _ = T.size + 1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL + 4 * nL := b2.trans (by rw [a2', hN]; rfl)
  refine ⟨a1.trans b1, b2', fun ti hti => ⟨?_, fun hon j hj => ?_⟩⟩
  · have e := b3 ti (by rw [h0]; omega) hti
    rw [a2'] at e
    simp only [hp0, show USize.toNat 0 = 0 from rfl, show UInt64.toNat 0 = 0 from rfl, Nat.sub_zero, Nat.zero_add] at e
    exact e
  · have hlt := cntOn_lt (pairOnN w0 w1 w2 w3 lTriv) nL 0 ti hon (Nat.zero_le _) (by omega)
    rw [Nat.sub_zero] at hlt
    have e := a3 ti (by rw [h0]; omega) hti hon j hj
    simp only [show USize.toNat 0 = 0 from rfl, Nat.sub_zero] at e
    have hne : u32At lTriv ti ≠ 4294967295 := by
      unfold pairOnN at hon
      simp only [Bool.and_eq_true, bne_iff_ne] at hon
      exact hon.2
    rw [pairAt_extend (hP ti hti hne) (a1.trans b1), b1.leAt (by rw [a2']; omega)]
    exact e

theorem tab6_spec {icBase lTriv : ByteArray} {nL nI : Nat} {hic : icBase.size = 4 * nI} {ht : lTriv.size = 4 * nL}
    {hn : nL ≤ 256} {w0 w1 w2 w3 : UInt64} {T : ByteArray} {hP : PairReady lTriv nL T}
    {hs : T.size + 4 * nI + 1028 * nL < 2 ^ 32} :
    Extends T (tab6 icBase lTriv nL nI hic ht hn w0 w1 w2 w3 T hP hs) ∧
      IresAt (tab6 icBase lTriv nL nI hic ht hn w0 w1 w2 w3 T hP hs) icBase nI T.size ∧
      PairsAt (tab6 icBase lTriv nL nI hic ht hn w0 w1 w2 w3 T hP hs) lTriv nL w0 w1 w2 w3 (T.size + 4 * nI) := by
  unfold tab6
  obtain ⟨c1, c2⟩ := tabLast_spec (ht := ht) (hn := hn) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (T := T ++ icBase)
    (hP := hP.extend (Extends.append T icBase)) (hs := by rw [ByteArray.size_append, hic]; omega)
  refine ⟨(Extends.append T icBase).trans c1, fun t hti => ?_, c2.at (by rw [ByteArray.size_append, hic])⟩
  rw [c1.leAt (by rw [ByteArray.size_append, hic]; omega), leAt_append, leAt_u32]

theorem tab4_spec {icBase dBase dMap lTriv : ByteArray} {nL nI nD treesD : Nat} {hic : icBase.size = 4 * nI}
    {hd : dBase.size = 4 * treesD} {hd256 : treesD ≤ 256} {hdm : dMap.size = 4 * nD} {hnD : nD ≤ 256}
    {hdlt : ∀ p : USize, ∀ h : p.toNat < dMap.size, (dMap.uget p h).toNat < treesD} {ht : lTriv.size = 4 * nL}
    {hn : nL ≤ 256} {w0 w1 w2 w3 : UInt64} {T : ByteArray} {hP : PairReady lTriv nL T}
    {hs : T.size + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32} :
    Extends T (tab4 icBase dBase dMap lTriv nL nI nD treesD hic hd hd256 hdm hnD hdlt ht hn w0 w1 w2 w3 T hP hs) ∧
      MapAt (tab4 icBase dBase dMap lTriv nL nI nD treesD hic hd hd256 hdm hnD hdlt ht hn w0 w1 w2 w3 T hP hs)
        dBase dMap T.size ∧
      IresAt (tab4 icBase dBase dMap lTriv nL nI nD treesD hic hd hd256 hdm hnD hdlt ht hn w0 w1 w2 w3 T hP hs)
        icBase nI (T.size + 16 * nD) ∧
      PairsAt (tab4 icBase dBase dMap lTriv nL nI nD treesD hic hd hd256 hdm hnD hdlt ht hn w0 w1 w2 w3 T hP hs)
        lTriv nL w0 w1 w2 w3 (T.size + 16 * nD + 4 * nI) := by
  unfold tab4
  obtain ⟨d1, d2, d3⟩ := pushMap_spec (base := dBase) (map := dMap) (nT := treesD) (hb := hd) (hb32 := by omega)
    (hm32 := by omega) (hlt := hdlt) (t := T) (hc := by rw [hdm]; omega)
  obtain ⟨e1, e2, e3⟩ := tab6_spec (hic := hic) (ht := ht) (hn := hn) (w0 := w0) (w1 := w1)
    (w2 := w2) (w3 := w3) (T := pushMap dBase dMap treesD hd (by omega) (by omega) hdlt T (by rw [hdm]; omega))
    (hP := hP.extend d2) (hs := by rw [d1, hdm]; omega)
  exact ⟨d2.trans e1, fun J hJ => by rw [e1.leAt (by rw [d1]; omega)]; exact d3 J hJ, e2.at (by rw [d1, hdm]; omega),
    e3.at (by rw [d1, hdm]; omega)⟩

theorem tab3_spec {litBase lMap icBase dBase dMap lTriv : ByteArray} {nL nI nD treesL treesD : Nat}
    {ha : TabArrs litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD} {w0 w1 w2 w3 : UInt64}
    {T : ByteArray} {hP : PairReady lTriv nL T} {hs : T.size + 256 * nL + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32} :
    Extends T (tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hP hs) ∧
      MapAt (tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hP hs)
        litBase lMap T.size ∧
      MapAt (tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hP hs)
        dBase dMap (T.size + 256 * nL) ∧
      IresAt (tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hP hs)
        icBase nI (T.size + 256 * nL + 16 * nD) ∧
      PairsAt (tab3 litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hP hs)
        lTriv nL w0 w1 w2 w3 (T.size + 256 * nL + 16 * nD + 4 * nI) := by
  unfold tab3
  have hl1 : litBase.size < 2 ^ 32 := by have := ha.litSize; have := ha.trees256; omega
  have hl2 : lMap.size < 2 ^ 32 := by have := ha.lMapSize; have := ha.nL256; omega
  obtain ⟨d1, d2, d3⟩ := pushMap_spec (base := litBase) (map := lMap) (nT := treesL) (hb := ha.litSize) (hb32 := hl1)
    (hm32 := hl2) (hlt := ha.lMapLt) (t := T) (hc := by rw [ha.lMapSize]; omega)
  obtain ⟨e1, e2, e3, e4⟩ := tab4_spec (hic := ha.icSize) (hd := ha.dSize) (hd256 := ha.treesD256) (hdm := ha.dMapSize)
    (hnD := ha.nD256) (hdlt := ha.dMapLt) (ht := ha.trivSize) (hn := ha.nL256) (w0 := w0) (w1 := w1)
    (w2 := w2) (w3 := w3) (T := pushMap litBase lMap treesL ha.litSize hl1 hl2 ha.lMapLt T (by rw [ha.lMapSize]; omega))
    (hP := hP.extend d2) (hs := by rw [d1, ha.lMapSize]; omega)
  exact ⟨d2.trans e1, fun J hJ => by rw [e1.leAt (by rw [d1]; omega)]; exact d3 J hJ,
    e2.at (by rw [d1, ha.lMapSize]; omega), e3.at (by rw [d1, ha.lMapSize]; omega), e4.at (by rw [d1, ha.lMapSize]; omega)⟩

theorem tabFrom_spec {litBase lMap icBase dBase dMap lTriv : ByteArray} {nL nI nD treesL treesD : Nat}
    {ha : TabArrs litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD} {w0 w1 w2 w3 : UInt64}
    {T : ByteArray} {hI : ICReady icBase nI T} {hP : PairReady lTriv nL T}
    {hs : T.size + 2048 * nI + 256 * nL + 16 * nD + 4 * nI + 1028 * nL < 2 ^ 32} :
    Extends T (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs) ∧
      IcAt (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs)
        icBase nI T.size ∧
      MapAt (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs)
        litBase lMap (T.size + 2048 * nI) ∧
      MapAt (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs)
        dBase dMap (T.size + 2048 * nI + 256 * nL) ∧
      IresAt (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs)
        icBase nI (T.size + 2048 * nI + 256 * nL + 16 * nD) ∧
      PairsAt (tabFrom litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD ha w0 w1 w2 w3 T hI hP hs)
        lTriv nL w0 w1 w2 w3 (T.size + 2048 * nI + 256 * nL + 16 * nD + 4 * nI) := by
  unfold tabFrom
  have hi32 : icBase.size < 2 ^ 32 := by have := ha.icSize; have := ha.nI256; omega
  obtain ⟨d1, d2, d3⟩ := pushIC_spec (icBase := icBase) (nI := nI) (hn := ha.nI256) (hb := ha.icSize) (hb32 := hi32)
    (t := T) (h := hI) (hc := by omega)
  obtain ⟨e1, e2, e3, e4, e5⟩ := tab3_spec (ha := ha) (w0 := w0) (w1 := w1) (w2 := w2)
    (w3 := w3) (T := pushIC icBase nI ha.nI256 ha.icSize hi32 T hI (by omega)) (hP := hP.extend d2)
    (hs := by rw [d1]; omega)
  refine ⟨d2.trans e1, fun ti hti j hj => ?_, e2.at (by rw [d1]), e3.at (by rw [d1]), e4.at (by rw [d1]),
    e5.at (by rw [d1])⟩
  have hr := hI ti hti
  rw [e1.leAt (by rw [d1]; omega), d3 ti hti j hj, (d2.trans e1).slotNum (by omega)]

/-! ### What the built arena holds -/

/-- What the fast command loop's table arena holds, with no mention of the spec: the masks and the shared distance
table after them, the tables the header built (each within `f0 - 8` bytes, so an 8-byte read of a slot stays in the
arena), and the derived tables from `f0`. -/
structure TabOk (T litBase lMap icBase dBase dMap lTriv : ByteArray) (nL nI nD treesL treesD : Nat) (np nd : UInt64)
    (f0 : Nat) : Prop where
  size32 : T.size < 2 ^ 32
  masks : ∀ n, n < 32 → leAt T (8 * n) 8 = 2 ^ n - 1
  f0Ok : 4424 ≤ f0 ∧ f0 % 8 = 0
  sizeOk : f0 + 2048 * nI + 256 * nL + 16 * nD + 4 * nI + 4 * nL ≤ T.size
  lFit : ∀ tree, tree < treesL → TableIn T (u32At litBase tree) (f0 - 8)
  iFit : ∀ t, t < nI → TableIn T (u32At icBase t) (f0 - 8)
  dFit : ∀ tree, tree < treesD → TableIn T (u32At dBase tree) (f0 - 8)
  trivFit : ∀ t, t < nL → u32At lTriv t ≠ 4294967295 → TableIn T (u32At lTriv t) (f0 - 8)
  ic : IcAt T icBase nI f0
  lres : MapAt T litBase lMap (f0 + 2048 * nI)
  dres : MapAt T dBase dMap (f0 + 2048 * nI + 256 * nL)
  dsh : DshAt T np nd 256
  ires : IresAt T icBase nI (f0 + 2048 * nI + 256 * nL + 16 * nD)
  pix : ∀ ti, ti < nL → leAt T (T.size - 4 * nL + 4 * ti) 4 ≠ 4294967295 →
    u32At lTriv ti ≠ 4294967295 ∧ leAt T (T.size - 4 * nL + 4 * ti) 4 + 1024 ≤ T.size - 4 * nL ∧
      ∀ j, j < 256 → leAt T (leAt T (T.size - 4 * nL + 4 * ti) 4 + 4 * j) 4 = (pairAt T (u32At lTriv ti) j).toNat % 2 ^ 32

/-- The built arena holds what the fast command loop reads. -/
theorem buildTab_ok {A litBase lMap icBase dBase dMap lTriv : ByteArray} {nL nI nD treesL treesD : Nat}
    (h : TabArgs A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) {np nd : UInt64} (hd : DshAt A np nd 256)
    (w0 w1 w2 w3 : UInt64) :
    TabOk (buildTab A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h w0 w1 w2 w3) litBase lMap icBase
      dBase dMap lTriv nL nI nD treesL treesD np nd (A.size + padOf A.size) := by
  have hp := padOf_spec A.size
  have hsz := h.size
  unfold tabMax at hsz
  have hT1 := size_pushLE (padOf A.size) A 0
  have hE1 := Extends.pushLE A 0 (padOf A.size)
  obtain ⟨T, hT⟩ : ∃ T, buildTab A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h w0 w1 w2 w3 = T :=
    ⟨_, rfl⟩
  rw [hT]
  unfold buildTab at hT
  obtain ⟨e1, e2, e3, e4, e6, e7⟩ := tabFrom_spec (ha := h.arrs) (w0 := w0) (w1 := w1)
    (w2 := w2) (w3 := w3) (T := pushLE A 0 (padOf A.size))
    (hI := fun ti hti => Nat.le_trans (h.icFits ti hti).root (by rw [size_pushLE]; omega))
    (hP := PairReady.extend (fun ti hti hne => h.trivFits ti hti hne) (Extends.pushLE A 0 _))
    (hs := by rw [size_pushLE]; omega)
  replace e2 := e2.at hT1
  replace e3 := e3.at (by rw [hT1])
  replace e4 := e4.at (by rw [hT1])
  replace e6 := e6.at (by rw [hT1])
  replace e7 := e7.at (by rw [hT1])
  rw [hT] at e1 e2 e3 e4 e6 e7
  have hE := hE1.trans e1
  obtain ⟨p1, p2⟩ := e7
  have hcl := cntOn_le (pairOnN w0 w1 w2 w3 lTriv) 0 nL
  have hx : T.size - 4 * nL = A.size + padOf A.size + 2048 * nI + 256 * nL + 16 * nD + 4 * nI +
      1024 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL := by rw [p1]; omega
  have hlim : A.size ≤ A.size + padOf A.size - 8 := by omega
  have hpre := h.pre
  refine ⟨by rw [p1]; omega, fun n hn => ?_, ⟨by omega, hp.2.2⟩, by rw [p1]; omega,
    fun tree ht => (h.litFits tree ht).tableIn hE hlim, fun t ht => (h.icFits t ht).tableIn hE hlim,
    fun tree ht => (h.dFits tree ht).tableIn hE hlim, fun t ht hne => (h.trivFits t ht hne).tableIn hE hlim,
    e2, e3, e4, fun dc hdc => ?_, e6, fun ti hti hne => ?_⟩
  · rw [hE.leAt (by omega)]
    exact h.masks n hn
  · rw [hE.leAt (by omega)]
    exact hd dc hdc
  · rw [hx] at hne ⊢
    obtain ⟨q1, q2⟩ := p2 ti hti
    rw [q1] at hne ⊢
    by_cases hon : pairOnN w0 w1 w2 w3 lTriv ti = true
    · rw [ite_eq_left hon] at hne ⊢
      have hlt := cntOn_lt (pairOnN w0 w1 w2 w3 lTriv) nL 0 ti hon (Nat.zero_le _) (by omega)
      rw [Nat.sub_zero] at hlt
      refine ⟨?_, by omega, q2 hon⟩
      unfold pairOnN at hon
      simp only [Bool.and_eq_true, bne_iff_ne] at hon
      exact hon.2
    · rw [ite_eq_right hon] at hne
      exact absurd rfl hne

/-- The built arena begins with the arena it was built from. -/
theorem buildTab_extends {A litBase lMap icBase dBase dMap lTriv : ByteArray} {nL nI nD treesL treesD : Nat}
    (h : TabArgs A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) (w0 w1 w2 w3 : UInt64) :
    Extends A (buildTab A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h w0 w1 w2 w3) := by
  have hp := padOf_spec A.size
  have hsz := h.size
  unfold tabMax at hsz
  unfold buildTab
  exact (Extends.pushLE A 0 (padOf A.size)).trans (tabFrom_spec (ha := h.arrs) (w0 := w0)
    (w1 := w1) (w2 := w2) (w3 := w3) (T := pushLE A 0 (padOf A.size))
    (hI := fun ti hti => Nat.le_trans (h.icFits ti hti).root (by rw [size_pushLE]; omega))
    (hP := PairReady.extend (fun ti hti hne => h.trivFits ti hti hne) (Extends.pushLE A 0 _))
    (hs := by rw [size_pushLE]; omega)).1

/-- The built arena takes at most `tabMax` more than the arena it was built from. -/
theorem buildTab_size {A litBase lMap icBase dBase dMap lTriv : ByteArray} {nL nI nD treesL treesD : Nat}
    (h : TabArgs A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD) (w0 w1 w2 w3 : UInt64) :
    (buildTab A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h w0 w1 w2 w3).size ≤
      A.size + tabMax nL nI nD := by
  have hp := padOf_spec A.size
  have hsz := h.size
  unfold tabMax at hsz ⊢
  have hT1 := size_pushLE (padOf A.size) A 0
  obtain ⟨T, hT⟩ : ∃ T, buildTab A litBase lMap icBase dBase dMap lTriv nL nI nD treesL treesD h w0 w1 w2 w3 = T :=
    ⟨_, rfl⟩
  rw [hT]
  unfold buildTab at hT
  obtain ⟨_, _, _, _, _, e7⟩ := tabFrom_spec (ha := h.arrs) (w0 := w0) (w1 := w1)
    (w2 := w2) (w3 := w3) (T := pushLE A 0 (padOf A.size))
    (hI := fun ti hti => Nat.le_trans (h.icFits ti hti).root (by rw [size_pushLE]; omega))
    (hP := PairReady.extend (fun ti hti hne => h.trivFits ti hti hne) (Extends.pushLE A 0 _))
    (hs := by rw [size_pushLE]; omega)
  replace e7 := e7.at (by rw [hT1])
  rw [hT] at e7
  have hcl := cntOn_le (pairOnN w0 w1 w2 w3 lTriv) 0 nL
  rw [e7.1]
  omega

/-! ### The policy's entry -/

theorem bigLits_idx {icBase : ByteArray} {nI : Nat} (hic : icBase.size = 4 * nI) (hn : 0 < nI) :
    4 * (0 : USize).toNat + 4 ≤ icBase.size := by
  rw [hic]
  show 0 + 4 ≤ 4 * nI
  omega

theorem bigLits_root {A icBase : ByteArray} {nI : Nat} (hic : icBase.size = 4 * nI) (hi32 : icBase.size < 2 ^ 32)
    (hI : ICReady icBase nI A) (hn : 0 < nI) :
    2 * ((slotWord icBase 0 (bigLits_idx hic hn) hi32).toUSize.toNat + 256) ≤ A.size := by
  have hv := slotWord_toNat (bigLits_idx hic hn) hi32
  rw [word_toUSize (by rw [hv]; exact u32At_lt _ _), hv]
  exact hI 0 hn

/-- Whether the meta-block is expected to hold at least 32 KiB of literals, from the first insert-and-copy tree's root
slots (P46's gate on the two-literal tables). -/
def bigLits (A : ByteArray) (s : A.size < 2 ^ 32) (icBase : ByteArray) (nI : Nat) (hic : icBase.size = 4 * nI)
    (hi32 : icBase.size < 2 ^ 32) (hI : ICReady icBase nI A) (mlen : UInt64) : Bool :=
  if hn : 0 < nI then
    match expLits A s (slotWord icBase 0 (bigLits_idx hic hn) hi32).toUSize (bigLits_root hic hi32 hI hn) 0 0 0 with
    | (ins, cpy) => ins + cpy != 0 && 32768 ≤ mlen * ins / (ins + cpy)
  else false

/-- The flags of the literal types that get two-literal tables, with the arena handed back unchanged, so that it is
read before it grows. Which types are chosen is a policy and changes no claim. -/
@[noinline] def tabPolicy (A : ByteArray) (s : A.size < 2 ^ 32) (icBase : ByteArray) (nI : Nat) (hic : icBase.size = 4 * nI)
    (hi32 : icBase.size < 2 ^ 32) (hI : ICReady icBase nI A) (lTriv : ByteArray) (nL : Nat) (ht : lTriv.size = 4 * nL)
    (hn : nL ≤ 256) (hP : PairReady lTriv nL A) (mlen : UInt64) :
    { p : (UInt64 × UInt64 × UInt64 × UInt64) × ByteArray // p.2 = A } :=
  ⟨(if bigLits A s icBase nI hic hi32 hI mlen then
      pairFlags A s lTriv nL ht (by omega) hP (USize.ofNat nL) (fastLit (by omega)) 0 0 0 0 0
    else (0, 0, 0, 0), A), rfl⟩

end Brotli.Decoder
