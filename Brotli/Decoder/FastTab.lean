module

public import Brotli.Decoder.Builder

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

/-! ### Appending entries in a loop -/

private theorem mul_step {w a b : Nat} (h : a < b) : w + w * (b - (a + 1)) = w * (b - a) := by
  rw [show b - a = (b - (a + 1)) + 1 by omega, Nat.mul_succ]
  omega

/-- Appends `w`-byte little-endian entries, `f t h _ j _` for each `j` from `j` below `n`, each computed from the array
so far. `P` holds of every array on the way, so that `f` can read the array without checks, and the array stays below
`2 ^ 32` bytes. -/
@[specialize] def pushLoop (P : ByteArray → Prop) (w : Nat) (hP : ∀ t v, P t → P (pushLE t v w)) (n : USize)
    (f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64)
    (t : ByteArray) (h : P t) (j : USize) (hc : t.size + w * (n.toNat - j.toNat) < 2 ^ 32) : ByteArray :=
  if hj : j < n then
    pushLoop P w hP n f (pushLE t (f t h (by omega) j hj) w) (hP _ _ h) (j + USize.ofNat 1) (by
      rw [size_pushLE, fastIdx_succ hj, Nat.add_assoc, mul_step (USize.lt_iff_toNat_lt.mp hj)]
      exact hc)
  else t
termination_by n.toNat - j.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.mp hj
  rw [fastIdx_succ hj]
  omega

/-- What the loop leaves: the array so far, then each entry, when each entry depends only on the bytes there were. -/
theorem pushLoop_spec {P : ByteArray → Prop} {w : Nat} {hP : ∀ t v, P t → P (pushLE t v w)} {n : USize}
    {f : (t : ByteArray) → P t → t.size < 2 ^ 32 → (j : USize) → j < n → UInt64}
    (hf : ∀ t t' h h' s s' j hj, Extends t t' → f t' h' s' j hj = f t h s j hj) :
    ∀ (N : Nat) (t : ByteArray) (h : P t) (j : USize) (hc : t.size + w * (n.toNat - j.toNat) < 2 ^ 32),
      n.toNat - j.toNat = N →
      (pushLoop P w hP n f t h j hc).size = t.size + w * (n.toNat - j.toNat) ∧
      Extends t (pushLoop P w hP n f t h j hc) ∧
      ∀ (k : USize) (hk : k < n), j ≤ k →
        leAt (pushLoop P w hP n f t h j hc) (t.size + w * (k.toNat - j.toNat)) w =
          (f t h (by omega) k hk).toNat % 256 ^ w := by
  intro N
  induction N with
  | zero =>
    intro t h j hc hN
    have hj : ¬ j < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [pushLoop, dite_eq_right hj]
    refine ⟨by rw [hN, Nat.mul_zero, Nat.add_zero], Extends.refl t, fun k h2 h1 => ?_⟩
    have := USize.le_iff_toNat_le.mp h1
    have := USize.lt_iff_toNat_lt.mp h2
    omega
  | succ N ih =>
    intro t h j hc hN
    have hj : j < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hjn := USize.lt_iff_toNat_lt.mp hj
    have hs := fastIdx_succ hj
    rw [pushLoop, dite_eq_left hj]
    have hsz1 := size_pushLE w t (f t h (by omega) j hj)
    have hc1 : (pushLE t (f t h (by omega) j hj) w).size + w * (n.toNat - (j + USize.ofNat 1).toNat) < 2 ^ 32 := by
      rw [size_pushLE, hs, Nat.add_assoc, mul_step hjn]
      exact hc
    obtain ⟨i1, i2, i3⟩ := ih (pushLE t (f t h (by omega) j hj) w) (hP _ _ h) (j + USize.ofNat 1) hc1 (by rw [hs]; omega)
    generalize pushLoop P w hP n f (pushLE t (f t h (by omega) j hj) w) (hP _ _ h) (j + USize.ofNat 1) _ = r at i1 i2 i3
    have he1 := Extends.pushLE t (f t h (by omega) j hj) w
    refine ⟨?_, he1.trans i2, fun k h2 h1 => ?_⟩
    · rw [i1, hsz1, hs, Nat.add_assoc, mul_step hjn]
    · have hk1 := USize.le_iff_toNat_le.mp h1
      by_cases hk : k = j
      · subst hk
        rw [Nat.sub_self, Nat.mul_zero, Nat.add_zero, i2.leAt (Nat.le_of_eq hsz1.symm), leAt_pushLE]
      · have hk2 : j.toNat + 1 ≤ k.toNat := by
          have : j.toNat ≠ k.toNat := fun e => hk (USize.toNat_inj.mp e).symm
          omega
        have e := i3 k h2 (USize.le_iff_toNat_le.mpr (by rw [hs]; exact hk2))
        rw [hsz1, hs, hf t _ h _ _ _ k h2 he1] at e
        rw [show t.size + w * (k.toNat - j.toNat) = t.size + w + w * (k.toNat - (j.toNat + 1)) by
          rw [Nat.add_assoc, mul_step (show j.toNat < k.toNat by omega)]]
        exact e

/-! ### The masks

The arena's first 256 bytes are the masks `2 ^ n - 1` for `n < 32`, 8 bytes each, written when a header's arena is
made, before any table. -/

/-- The mask `2 ^ j - 1`. -/
@[inline] def maskEntry (_t : ByteArray) (_h : True) (_s : _t.size < 2 ^ 32) (j : USize) (_hj : j < USize.ofNat 32) :
    UInt64 :=
  ((1 : UInt64) <<< j.toUInt64) - 1

/-- A position given as a number below `2 ^ 32` is that number. -/
theorem fastLit {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  have hs := USize.le_size
  rw [USize.size_eq_two_pow] at hs
  rw [USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem usize32 : (USize.ofNat 32).toNat = 32 := fastLit (by decide)

/-- Appends the 32 masks. -/
def writeMasks (t : ByteArray) (h : t.size + 256 < 2 ^ 32) : ByteArray :=
  pushLoop (fun _ => True) 8 (fun _ _ _ => trivial) (USize.ofNat 32) maskEntry t trivial 0 (by
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
  obtain ⟨s1, s2, s3⟩ := pushLoop_spec (P := fun _ => True) (w := 8) (hP := fun _ _ _ => trivial)
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

end Brotli.Decoder
