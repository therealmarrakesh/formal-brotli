import Brotli.Properties.Lookups

/-!
# The dictionary as bytes

The spec keeps the dictionary as one number per line of the RFC, so its `DICT` walks a list and shifts a large number for
each byte. Here the same bytes are one array, built once, and `dictWord` is proved to be the spec's `dictionaryWord`.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A line's 32 bytes, first the most significant. -/
def lineBytes (line : Nat) : List UInt8 :=
  (List.range 32).map fun j => ((line >>> (8 * (31 - j))) &&& 255).toUInt8

/-- The dictionary's bytes. -/
def dictBytes : ByteArray :=
  (dictLines.flatMap lineBytes).toByteArray

private theorem length_lineBytes (line : Nat) : (lineBytes line).length = 32 := by
  simp [lineBytes]

private theorem flatMap_get : ∀ (l : List Nat) (i : Nat), i / 32 < l.length →
    (l.flatMap lineBytes)[i]? = some ((l.getD (i / 32) 0 >>> (8 * (31 - i % 32))) &&& 255).toUInt8
  | [], _, h => by simp at h
  | x :: xs, i, h => by
    rw [List.flatMap_cons]
    by_cases hi : i < 32
    · rw [List.getElem?_append_left (by rw [length_lineBytes]; exact hi)]
      have h1 : i / 32 = 0 := by omega
      have h2 : i % 32 = i := by omega
      rw [h1, h2]
      simp [lineBytes, hi]
    · rw [List.getElem?_append_right (by rw [length_lineBytes]; omega), length_lineBytes,
        flatMap_get xs (i - 32) (by simp only [List.length_cons] at h; omega)]
      have h1 : i / 32 = (i - 32) / 32 + 1 := by omega
      have h2 : (i - 32) % 32 = i % 32 := by omega
      rw [h1, h2, List.getD_cons_succ]

private theorem get_toByteArray {l : List UInt8} {i : Nat} {v : UInt8} (h : l[i]? = some v) : l.toByteArray.get! i = v := by
  have hd : l.toByteArray.data = l.toArray := List.data_toByteArray
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp h
  cases hb : l.toByteArray with
  | mk bs =>
    rw [hb] at hd
    have hbs : bs = l.toArray := hd
    subst hbs
    show l.toArray[i]! = v
    simp [hlt, hv]

/-- A byte of the array is the spec's byte of the dictionary. -/
theorem dictBytes_get {i : Nat} (h : i / 32 < dictLines.length) : (dictBytes.get! i).toNat = DICT i := by
  have hg := get_toByteArray (flatMap_get dictLines i h)
  unfold dictBytes
  rw [hg]
  unfold DICT
  have hlt : (dictLines.getD (i / 32) 0 >>> (8 * (31 - i % 32))) &&& 255 < 256 :=
    Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt hlt

/-- `dictionaryWord`, reading the array. -/
def dictWord (length distance maxDistance : Nat) : Option (List Nat) :=
  if length < 4 ∨ 24 < length then none
  else
    let wordId := distance - (maxDistance + 1)
    let offset := wordOffset length (wordId % NWORDS length)
    let baseWord := (List.range length).map fun k => (dictBytes.get! (offset + k)).toNat
    transforms[wordId >>> NDBITS.getD length 0]?.map fun t => applyTransform t baseWord

/-- `dictWord` is the spec's `dictionaryWord`. -/
theorem dictWord_eq (length distance maxDistance : Nat) :
    dictWord length distance maxDistance = dictionaryWord length distance maxDistance := by
  unfold dictWord dictionaryWord
  split
  · rfl
  · rename_i hl
    dsimp only
    have hbase : ((List.range length).map fun k =>
          (dictBytes.get! (wordOffset length ((distance - (maxDistance + 1)) % NWORDS length) + k)).toNat) =
        (List.range length).map fun k => DICT (wordOffset length ((distance - (maxDistance + 1)) % NWORDS length) + k) := by
      apply List.map_congr_left
      intro k hk
      exact dictBytes_get (dictionary_in_range (by omega) (by omega) (List.mem_range.mp hk)).2.2
    rw [hbase]

end Brotli.Decoder
