/-!
# Word transformations

RFC 7932 §8 and Appendix B.
-/

namespace Brotli.Spec

/-- `Ferment` (§8): the bytes it steps over, as changed, and the bytes after them. -/
def ferment : List Nat → List Nat × List Nat
  | [] => ([], [])
  | b :: rest =>
    if b < 192 then ([if 97 ≤ b ∧ b ≤ 122 then b ^^^ 32 else b], rest)
    else if b < 224 then
      match rest with
      | [] => ([b], [])
      | c :: rest => ([b, c ^^^ 32], rest)
    else
      match rest with
      | [] => ([b], [])
      | [c] => ([b, c], [])
      | c :: d :: rest => ([b, c, d ^^^ 5], rest)

/-- `FermentFirst` (§8). -/
def fermentFirst (word : List Nat) : List Nat :=
  (ferment word).1 ++ (ferment word).2

/-- The loop of `fermentAll`, with `out` the out-of-fuel result. -/
def fermentAllWith (out : List Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | 0, _ :: _ => out
  | fuel + 1, b :: word =>
    (ferment (b :: word)).1 ++ fermentAllWith out fuel (ferment (b :: word)).2

/-- `FermentAll` (§8). Fuel: the bytes left (`fermentAll_out`). -/
def fermentAll (word : List Nat) : List Nat :=
  fermentAllWith [] word.length word

/-- `ferment` keeps the number of bytes. -/
theorem ferment_length (word : List Nat) :
    (ferment word).1.length + (ferment word).2.length = word.length := by
  match word with
  | [] => rfl
  | b :: rest =>
    simp only [ferment]
    split
    · simp; omega
    · split
      · split <;> simp <;> omega
      · split <;> simp <;> omega

/-- `ferment` steps over at least one byte of a word that has one. -/
theorem ferment_pos (b : Nat) (rest : List Nat) : 1 ≤ (ferment (b :: rest)).1.length := by
  simp only [ferment]
  split
  · simp
  · split
    · split <;> simp
    · split <;> simp

/-- While the fuel covers the bytes left, the out-of-fuel result is never reached. -/
theorem fermentAllWith_out : ∀ (fuel : Nat) (word : List Nat), word.length ≤ fuel → ∀ out out',
    fermentAllWith out fuel word = fermentAllWith out' fuel word
  | _, [], _, _, _ => by simp [fermentAllWith]
  | 0, _ :: _, h, _, _ => by simp at h
  | fuel + 1, b :: word, h, out, out' => by
    have := ferment_length (b :: word)
    have := ferment_pos b word
    simp only [fermentAllWith]
    rw [fermentAllWith_out fuel _ (by simp at *; omega) out out']

/-- `fermentAll` never reaches its out-of-fuel result. -/
theorem fermentAll_out (word out : List Nat) :
    fermentAll word = fermentAllWith out word.length word :=
  fermentAllWith_out word.length word (Nat.le_refl _) [] out

private theorem fermentAllWith_length : ∀ (fuel : Nat) (word : List Nat), word.length ≤ fuel →
    (fermentAllWith [] fuel word).length = word.length
  | _, [], _ => by simp [fermentAllWith]
  | 0, _ :: _, h => by simp at h
  | fuel + 1, b :: word, h => by
    have h1 := ferment_length (b :: word)
    have := ferment_pos b word
    simp only [fermentAllWith, List.length_append]
    rw [fermentAllWith_length fuel _ (by simp at *; omega)]
    exact h1

/-- An elementary transform (§8). -/
inductive ElementaryTransform where
  | identity
  | fermentFirst
  | fermentAll
  | omitFirst (k : Nat)
  | omitLast (k : Nat)
  deriving DecidableEq

/-- The elementary transforms of the format (§8). -/
def elementaryTransforms : List ElementaryTransform :=
  [.identity, .fermentFirst, .fermentAll] ++
    (List.range 9).map (fun k => .omitFirst (k + 1)) ++
    (List.range 9).map (fun k => .omitLast (k + 1))

/-- What each elementary transform does (§8). -/
def applyElementary : ElementaryTransform → List Nat → List Nat
  | .identity, word => word
  | .fermentFirst, word => fermentFirst word
  | .fermentAll, word => fermentAll word
  | .omitFirst k, word => word.drop k
  | .omitLast k, word => word.take (word.length - k)

/-- A row of Appendix B: the prefix, the elementary transform and the suffix. -/
structure WordTransform where
  prefixString : String
  elementary : ElementaryTransform
  suffixString : String
  deriving DecidableEq

/-- The bytes of a string of the table: each character's number is a byte. -/
def bytes (s : String) : List Nat :=
  s.toList.map Char.toNat

/-- A word transformation: prefix, transformed word, suffix (§8). -/
def applyTransform (t : WordTransform) (word : List Nat) : List Nat :=
  bytes t.prefixString ++ applyElementary t.elementary word ++ bytes t.suffixString

/-- The word transformations by ID (Appendix B). -/
def transforms : List WordTransform :=
  [ ⟨"", .identity, ""⟩,
    ⟨"", .identity, " "⟩,
    ⟨" ", .identity, " "⟩,
    ⟨"", .omitFirst 1, ""⟩,
    ⟨"", .fermentFirst, " "⟩,
    ⟨"", .identity, " the "⟩,
    ⟨" ", .identity, ""⟩,
    ⟨"s ", .identity, " "⟩,
    ⟨"", .identity, " of "⟩,
    ⟨"", .fermentFirst, ""⟩,
    ⟨"", .identity, " and "⟩,
    ⟨"", .omitFirst 2, ""⟩,
    ⟨"", .omitLast 1, ""⟩,
    ⟨", ", .identity, " "⟩,
    ⟨"", .identity, ", "⟩,
    ⟨" ", .fermentFirst, " "⟩,
    ⟨"", .identity, " in "⟩,
    ⟨"", .identity, " to "⟩,
    ⟨"e ", .identity, " "⟩,
    ⟨"", .identity, "\""⟩,
    ⟨"", .identity, "."⟩,
    ⟨"", .identity, "\">"⟩,
    ⟨"", .identity, "\n"⟩,
    ⟨"", .omitLast 3, ""⟩,
    ⟨"", .identity, "]"⟩,
    ⟨"", .identity, " for "⟩,
    ⟨"", .omitFirst 3, ""⟩,
    ⟨"", .omitLast 2, ""⟩,
    ⟨"", .identity, " a "⟩,
    ⟨"", .identity, " that "⟩,
    ⟨" ", .fermentFirst, ""⟩,
    ⟨"", .identity, ". "⟩,
    ⟨".", .identity, ""⟩,
    ⟨" ", .identity, ", "⟩,
    ⟨"", .omitFirst 4, ""⟩,
    ⟨"", .identity, " with "⟩,
    ⟨"", .identity, "'"⟩,
    ⟨"", .identity, " from "⟩,
    ⟨"", .identity, " by "⟩,
    ⟨"", .omitFirst 5, ""⟩,
    ⟨"", .omitFirst 6, ""⟩,
    ⟨" the ", .identity, ""⟩,
    ⟨"", .omitLast 4, ""⟩,
    ⟨"", .identity, ". The "⟩,
    ⟨"", .fermentAll, ""⟩,
    ⟨"", .identity, " on "⟩,
    ⟨"", .identity, " as "⟩,
    ⟨"", .identity, " is "⟩,
    ⟨"", .omitLast 7, ""⟩,
    ⟨"", .omitLast 1, "ing "⟩,
    ⟨"", .identity, "\n\t"⟩,
    ⟨"", .identity, ":"⟩,
    ⟨" ", .identity, ". "⟩,
    ⟨"", .identity, "ed "⟩,
    ⟨"", .omitFirst 9, ""⟩,
    ⟨"", .omitFirst 7, ""⟩,
    ⟨"", .omitLast 6, ""⟩,
    ⟨"", .identity, "("⟩,
    ⟨"", .fermentFirst, ", "⟩,
    ⟨"", .omitLast 8, ""⟩,
    ⟨"", .identity, " at "⟩,
    ⟨"", .identity, "ly "⟩,
    ⟨" the ", .identity, " of "⟩,
    ⟨"", .omitLast 5, ""⟩,
    ⟨"", .omitLast 9, ""⟩,
    ⟨" ", .fermentFirst, ", "⟩,
    ⟨"", .fermentFirst, "\""⟩,
    ⟨".", .identity, "("⟩,
    ⟨"", .fermentAll, " "⟩,
    ⟨"", .fermentFirst, "\">"⟩,
    ⟨"", .identity, "=\""⟩,
    ⟨" ", .identity, "."⟩,
    ⟨".com/", .identity, ""⟩,
    ⟨" the ", .identity, " of the "⟩,
    ⟨"", .fermentFirst, "'"⟩,
    ⟨"", .identity, ". This "⟩,
    ⟨"", .identity, ","⟩,
    ⟨".", .identity, " "⟩,
    ⟨"", .fermentFirst, "("⟩,
    ⟨"", .fermentFirst, "."⟩,
    ⟨"", .identity, " not "⟩,
    ⟨" ", .identity, "=\""⟩,
    ⟨"", .identity, "er "⟩,
    ⟨" ", .fermentAll, " "⟩,
    ⟨"", .identity, "al "⟩,
    ⟨" ", .fermentAll, ""⟩,
    ⟨"", .identity, "='"⟩,
    ⟨"", .fermentAll, "\""⟩,
    ⟨"", .fermentFirst, ". "⟩,
    ⟨" ", .identity, "("⟩,
    ⟨"", .identity, "ful "⟩,
    ⟨" ", .fermentFirst, ". "⟩,
    ⟨"", .identity, "ive "⟩,
    ⟨"", .identity, "less "⟩,
    ⟨"", .fermentAll, "'"⟩,
    ⟨"", .identity, "est "⟩,
    ⟨" ", .fermentFirst, "."⟩,
    ⟨"", .fermentAll, "\">"⟩,
    ⟨" ", .identity, "='"⟩,
    ⟨"", .fermentFirst, ","⟩,
    ⟨"", .identity, "ize "⟩,
    ⟨"", .fermentAll, "."⟩,
    ⟨"\xc2\xa0", .identity, ""⟩,
    ⟨" ", .identity, ","⟩,
    ⟨"", .fermentFirst, "=\""⟩,
    ⟨"", .fermentAll, "=\""⟩,
    ⟨"", .identity, "ous "⟩,
    ⟨"", .fermentAll, ", "⟩,
    ⟨"", .fermentFirst, "='"⟩,
    ⟨" ", .fermentFirst, ","⟩,
    ⟨" ", .fermentAll, "=\""⟩,
    ⟨" ", .fermentAll, ", "⟩,
    ⟨"", .fermentAll, ","⟩,
    ⟨"", .fermentAll, "("⟩,
    ⟨"", .fermentAll, ". "⟩,
    ⟨" ", .fermentAll, "."⟩,
    ⟨"", .fermentAll, "='"⟩,
    ⟨" ", .fermentAll, ". "⟩,
    ⟨" ", .fermentFirst, "=\""⟩,
    ⟨" ", .fermentAll, "='"⟩,
    ⟨" ", .fermentFirst, "='"⟩ ]

theorem transforms_length : transforms.length = 121 := by
  decide +kernel

theorem transforms_elementary : ∀ t ∈ transforms, t.elementary ∈ elementaryTransforms := by
  decide +kernel

theorem elementaryTransforms_length : elementaryTransforms.length = 21 := by
  decide +kernel

theorem transforms_no_omitFirst8 : ∀ t ∈ transforms, t.elementary ≠ .omitFirst 8 := by
  decide +kernel

private theorem transforms_additional :
    ∀ t ∈ transforms, (bytes t.prefixString).length + (bytes t.suffixString).length ≤ 13 := by
  decide +kernel

private theorem applyElementary_length_le (e : ElementaryTransform) (word : List Nat) :
    (applyElementary e word).length ≤ word.length := by
  cases e with
  | identity => exact Nat.le_refl _
  | fermentFirst =>
    have := ferment_length word
    simp only [applyElementary, fermentFirst, List.length_append]
    omega
  | fermentAll =>
    exact Nat.le_of_eq (fermentAllWith_length word.length word (Nat.le_refl _))
  | omitFirst k => simp [applyElementary]
  | omitLast k => simp [applyElementary]

/-- A transform adds at most 13 bytes, and one adds exactly that (§8). -/
theorem applyTransform_length :
    (∀ t ∈ transforms, ∀ word, (applyTransform t word).length ≤ word.length + 13) ∧
      ∃ t ∈ transforms, ∀ word, (applyTransform t word).length = word.length + 13 := by
  refine ⟨fun t ht word => ?_, ⟨" the ", .identity, " of the "⟩, by decide +kernel, fun word => ?_⟩
  · have := transforms_additional t ht
    have := applyElementary_length_le t.elementary word
    simp only [applyTransform, List.length_append]
    omega
  · have h1 : (bytes " the ").length = 5 := by decide +kernel
    have h2 : (bytes " of the ").length = 8 := by decide +kernel
    simp only [applyTransform, applyElementary, List.length_append, h1, h2]
    omega

end Brotli.Spec
