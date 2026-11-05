module

public import Brotli.Decoder.Lookup

@[expose] public section

/-!
# Reading one thing from the bit buffer

The small reads the command loop is made of, in the spec's terms: a symbol through a table, and an integer. Each says
what the spec's reader does on the bits held followed by anything.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- A lookup word's bit count, its low 4 bits. -/
@[inline] def wordBits (v : UInt64) : UInt64 := v &&& 15

/-- A lookup word's symbol, its 12 bits above the bit count. -/
@[inline] def wordSym (v : UInt64) : UInt64 := (v >>> 4) &&& 4095

/-- A lookup word's value. -/
def wordValue (v : UInt64) : Nat := (wordSym v).toNat

theorem wordValue_lt (v : UInt64) : wordValue v < 2 ^ 16 := by
  unfold wordValue wordSym
  rw [UInt64.toNat_and, show (4095 : UInt64).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have := Nat.mod_lt ((v >>> 4).toNat) (Nat.two_pow_pos 12)
  omega

theorem wordBits_eq (v : UInt64) : (wordBits v).toNat = v.toNat % 16 := by
  unfold wordBits
  rw [UInt64.toNat_and, show (15 : UInt64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem wordBits_lt (v : UInt64) : (wordBits v).toNat < 64 := by
  rw [wordBits_eq]
  omega

theorem wordValue_eq (v : UInt64) : wordValue v = v.toNat / 16 % 4096 := by
  unfold wordValue wordSym
  rw [UInt64.toNat_and, show (4095 : UInt64).toNat = 2 ^ 12 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- What a table lookup means for `decodeSymbol`: with enough bits held, the symbol and the bits after it, whatever
follows; with too few, it has nothing to give from the bits held alone. -/
theorem lookup_read {t : ByteArray} {base : USize} {b : BitBuffer} {c : PrefixCode} (hok : TableOk t base.toNat c)
    (hfit : TableFits t base.toNat) (h32 : t.size < 2 ^ 32) (hC : Complete c) :
    let v := lookup t base b.word hfit h32
    (wordBits v).toNat ≤ 15 ∧
      (wordBits v ≤ b.count → ∀ f : List Bool,
        decodeSymbol c (b.held ++ f) = some (wordValue v, (b.drop (wordBits v)).held ++ f)) ∧
      (¬ wordBits v ≤ b.count → decodeSymbol c b.held = none) := by
  intro v
  obtain ⟨h1, h2⟩ := lookup_spec (w := b.word) hfit h32
  have hh : Hit c b.word.toNat (v.toNat % 16) (v.toNat / 16) := by
    have := hok.hit b.word.toNat
    rw [← h1, ← h2] at this
    exact this
  have hb := wordBits_eq v
  have hk : (wordBits v).toNat < 64 := wordBits_lt v
  have hv16 : v.toNat < 65536 := lookup_lt hfit h32
  refine ⟨by omega, ?_, ?_⟩
  · intro hle f
    have hle' := UInt64.le_iff_toNat_le.mp hle
    rw [hb] at hle'
    have hd := hh.decode hC hle' f
    have hw := drop_word b hk
    have hc := drop_count (b := b) (k := wordBits v) (UInt64.le_iff_toNat_le.mp hle)
    have ev : wordValue v = v.toNat / 16 := by
      rw [wordValue_eq]
      omega
    simp only [BitBuffer.held] at hd ⊢
    rw [hw, hc, hb, ev]
    exact hd
  · intro hnot
    have hlt : b.count.toNat < v.toNat % 16 := by
      rw [← hb]
      exact Nat.lt_of_not_le fun h => hnot (UInt64.le_iff_toNat_le.mpr h)
    exact hh.short hC hlt

/-- Reading an integer's bits with enough bits held. -/
theorem read_int {b : BitBuffer} {k : UInt64} (f : List Bool) (hk : k.toNat < 64) (hle : k ≤ b.count) :
    readInt k.toNat (b.held ++ f) = some ((b.peek k).toNat, (b.drop k).held ++ f) :=
  BitBuffer.readInt_held f hk (UInt64.le_iff_toNat_le.mp hle)

/-- With fewer bits held than an integer has, there's nothing to read from them alone. -/
theorem readInt_short {b : BitBuffer} {k : Nat} (h : b.count.toNat < k) : readInt k b.held = none := by
  have key : ∀ (k : Nat) (l : List Bool), l.length < k → readInt k l = none := by
    intro k
    induction k with
    | zero => intro l hl; omega
    | succ k ih =>
      intro l hl
      cases l with
      | nil => rfl
      | cons x xs =>
        simp only [readInt]
        rw [ih xs (by simpa using hl)]
        rfl
  apply key
  simpa [BitBuffer.held] using h

end Brotli.Decoder
