module

public import Brotli.Spec.Transform
public import Brotli.Spec.DictionaryData

@[expose] public section

/-!
# Static dictionary

RFC 7932 §8 and Appendix A.
-/

namespace Brotli.Spec

/-- The maximum backward distance (§8). -/
def maxBackwardDistance (windowSize produced : Nat) : Nat :=
  min windowSize produced

/-- A distance above the maximum is a static dictionary reference (§8). -/
def isDictionaryReference (distance maxDistance : Nat) : Bool :=
  maxDistance < distance

/-- A distance is not a dictionary reference exactly when it is at most the window size and the bytes
produced (§8, §9.1, §10). -/
theorem backwardDistance_iff {w p d : Nat} :
    isDictionaryReference d (maxBackwardDistance w p) = false ↔ d ≤ w ∧ d ≤ p := by
  unfold isDictionaryReference maxBackwardDistance
  rw [decide_eq_false_iff_not]
  omega

/-- NDBITS[0..24] (§8, Appendix A). -/
def NDBITS : List Nat :=
  [0, 0, 0, 0, 10, 10, 11, 11, 10, 10,
   10, 10, 10, 9, 9, 8, 7, 7, 8, 7,
   7, 6, 6, 5, 5]

theorem NDBITS_length : NDBITS.length = 25 := by
  decide +kernel

/-- The number of words of a length (§8). -/
def NWORDS (length : Nat) : Nat :=
  if length < 4 then 0 else 1 <<< NDBITS.getD length 0

/-- The byte offset of the words of a length (§8). -/
def DOFFSET : Nat → Nat
  | 0 => 0
  | length + 1 => DOFFSET length + length * NWORDS length

/-- The dictionary's size in bytes (§8). -/
def DICTSIZE : Nat :=
  DOFFSET 24 + 24 * NWORDS 24

/-- The array's length, 122,784 bytes, is DICTSIZE (Appendix A). -/
theorem DICTSIZE_eq : DICTSIZE = 122784 ∧ dictLines.length * 32 = 122784 := by
  decide +kernel

/-- Byte `i` of the dictionary (§8, Appendix A). -/
def DICT (i : Nat) : Nat :=
  (dictLines.getD (i / 32) 0 >>> (8 * (31 - i % 32))) &&& 255

/-- The byte offset of a word (§8). -/
def wordOffset (length index : Nat) : Nat :=
  DOFFSET length + index * length

/-- The last word of each length ends inside the array. -/
theorem wordOffset_le : ∀ length < 25, 4 ≤ length → wordOffset length (NWORDS length) ≤ DICTSIZE := by
  decide +kernel

/-- The string a static dictionary reference copies (§8), or `none` if its length or transform is
invalid. -/
def dictionaryWord (length distance maxDistance : Nat) : Option (List Nat) :=
  if length < 4 ∨ 24 < length then none
  else
    let wordId := distance - (maxDistance + 1)
    let index := wordId % NWORDS length
    let baseWord := (List.range length).map fun k => DICT (wordOffset length index + k)
    let transformId := wordId >>> NDBITS.getD length 0
    transforms[transformId]?.map fun t => applyTransform t baseWord

/-- A static dictionary reference's copy length is 4 to 24 (§8). -/
theorem dictionaryWord_copyLength {length distance maxDistance : Nat} {word : List Nat}
    (h : dictionaryWord length distance maxDistance = some word) : 4 ≤ length ∧ length ≤ 24 := by
  unfold dictionaryWord at h
  split at h
  · simp at h
  · omega

/-- A transformed word and a terminating zero fit in 38 bytes (§8). -/
theorem dictionaryWord_length {length distance maxDistance : Nat} {word : List Nat}
    (h : dictionaryWord length distance maxDistance = some word) : word.length + 1 ≤ 38 := by
  unfold dictionaryWord at h
  split at h
  · simp at h
  · rename_i hlen
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    have := applyTransform_length.1 t (List.mem_of_getElem? ht)
      ((List.range length).map fun k =>
        DICT (wordOffset length ((distance - (maxDistance + 1)) % NWORDS length) + k))
    simp only [List.length_map, List.length_range] at this
    omega

end Brotli.Spec
