import Brotli.Decoder.Hit

/-!
# Walking a code's symbols

The table builder visits each symbol that has a code, with its code word from counters rather than from the spec's
list operations. `foldCodes_ind` says what it visits: every symbol in order, each with the spec's `code`.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- How many times each length occurs, in a 16-entry array. -/
def lengthCounts (lens : List Nat) : Array Nat :=
  lens.foldl (fun cs l => cs.setIfInBounds l (cs.getD l 0 + 1)) (Array.replicate 16 0)

private theorem getD_set {cs : Array Nat} {l n v : Nat} (hl : l < cs.size) :
    (cs.setIfInBounds l v).getD n 0 = if n = l then v else cs.getD n 0 := by
  by_cases h : n = l
  · subst h
    simp [Array.getD_eq_getD_getElem?, hl]
  · simp [Array.getD_eq_getD_getElem?, h, Ne.symm h]

private theorem lengthCounts_aux (n : Nat) : ∀ (lens : List Nat) (cs : Array Nat), cs.size = 16 →
    (∀ l ∈ lens, l ≤ 15) →
    (lens.foldl (fun cs l => cs.setIfInBounds l (cs.getD l 0 + 1)) cs).size = 16 ∧
      (lens.foldl (fun cs l => cs.setIfInBounds l (cs.getD l 0 + 1)) cs).getD n 0 =
        cs.getD n 0 + (lens.filter (· == n)).length
  | [], cs, h, _ => by simp [h]
  | x :: xs, cs, h, hl => by
    have hx : x ≤ 15 := hl x (by simp)
    have hs : (cs.setIfInBounds x (cs.getD x 0 + 1)).size = 16 := by simpa using h
    obtain ⟨h1, h2⟩ := lengthCounts_aux n xs _ hs (fun l hm => hl l (by simp [hm]))
    refine ⟨by simpa using h1, ?_⟩
    simp only [List.foldl_cons]
    rw [h2, getD_set (by omega), List.filter_cons]
    by_cases hn : n = x
    · subst hn
      simp
      omega
    · have : (x == n) = false := by
        simp only [beq_eq_false_iff_ne]
        exact Ne.symm hn
      simp [hn, this]

/-- `lengthCounts` is the spec's `bl_count`, apart from length 0, which it counts too. -/
theorem lengthCounts_eq {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) {n : Nat} (h0 : n ≠ 0) :
    (lengthCounts lens).getD n 0 = blCount lens n := by
  have hs : (Array.replicate 16 0 : Array Nat).size = 16 := by simp
  have h := (lengthCounts_aux n lens _ hs hl).2
  simp only [lengthCounts, h, blCount, h0, ↓reduceIte]
  have : (Array.replicate 16 0 : Array Nat).getD n 0 = 0 := by
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  omega

/-- Appends the first code of each length from `b`, with `code` the first code of length `b`. -/
def nextCodesFrom (cs : Array Nat) : Nat → Nat → Nat → Array Nat → Array Nat
  | 0, _, _, acc => acc
  | n + 1, b, c, acc =>
    nextCodesFrom cs n (b + 1) ((c + if b = 0 then 0 else cs.getD b 0) <<< 1) (acc.push c)

private theorem nextCodesFrom_spec {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) : ∀ (n b : Nat) (acc : Array Nat),
    acc.size = b → (∀ i, i < b → acc.getD i 0 = nextCode lens i) →
    (nextCodesFrom (lengthCounts lens) n b (nextCode lens b) acc).size = b + n ∧
      ∀ i, i < b + n → (nextCodesFrom (lengthCounts lens) n b (nextCode lens b) acc).getD i 0 = nextCode lens i
  | 0, b, acc, hs, h => ⟨hs, h⟩
  | n + 1, b, acc, hs, h => by
    have hnext : (nextCode lens b + if b = 0 then 0 else (lengthCounts lens).getD b 0) <<< 1 =
        nextCode lens (b + 1) := by
      show _ = (nextCode lens b + blCount lens b) <<< 1
      congr 2
      by_cases hb : b = 0
      · simp [hb, blCount]
      · simp only [hb, ↓reduceIte]
        exact lengthCounts_eq hl hb
    simp only [nextCodesFrom, hnext]
    obtain ⟨h1, h2⟩ := nextCodesFrom_spec hl n (b + 1) (acc.push (nextCode lens b)) (by simp [hs]) (by
      intro i hi
      by_cases he : i = b
      · subst he
        subst hs
        simp [Array.getD_eq_getD_getElem?]
      · have hlt : i < b := by omega
        have := h i hlt
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
        simp [show i ≠ acc.size by omega, this])
    exact ⟨by omega, fun i hi => h2 i (by omega)⟩

/-- The first code of each length up to 15. -/
def nextCodes (lens : List Nat) : Array Nat :=
  nextCodesFrom (lengthCounts lens) 16 0 0 #[]

theorem nextCodes_spec {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) :
    (nextCodes lens).size = 16 ∧ ∀ i, i < 16 → (nextCodes lens).getD i 0 = nextCode lens i :=
  nextCodesFrom_spec hl 16 0 #[] rfl (by intro i hi; omega)

/-- Visits each symbol from `s` that has a code, with the code from the counters `nc`. -/
def foldCodes {β : Type} (f : β → Nat → Nat → Nat → β) : List Nat → Nat → Array Nat → β → β
  | [], _, _, acc => acc
  | l :: rest, s, nc, acc =>
    if l = 0 then foldCodes f rest (s + 1) nc acc
    else
      let c := nc.getD l 0
      foldCodes f rest (s + 1) (nc.setIfInBounds l (c + 1)) (f acc s l c)

/-- What `foldCodes` visits: a property kept by every symbol, with each symbol that has a code seen with the spec's
`code`, holds at the end. -/
theorem foldCodes_ind {β : Type} {f : β → Nat → Nat → Nat → β} {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15)
    (P : Nat → β → Prop) (hz : ∀ s acc, P s acc → lens[s]? = some 0 → P (s + 1) acc)
    (hs : ∀ s l acc, P s acc → lens[s]? = some l → l ≠ 0 → P (s + 1) (f acc s l (code lens s |>.getD 0)))
    {acc : β} (h0 : P 0 acc) : P lens.length (foldCodes f lens 0 (nextCodes lens) acc) := by
  have key : ∀ (rest : List Nat) (s : Nat) (nc : Array Nat) (acc : β), lens.drop s = rest → s + rest.length = lens.length →
      nc.size = 16 → (∀ l, l ≠ 0 → l < 16 → nc.getD l 0 = nextCode lens l + ((lens.take s).filter (· == l)).length) →
      P s acc → P lens.length (foldCodes f rest s nc acc) := by
    intro rest
    induction rest with
    | nil =>
      intro s nc acc _ hlen _ _ hp
      simpa [foldCodes, ← hlen] using hp
    | cons x xs ih =>
      intro s nc acc hd hlen hsz hnc hp
      have hget : lens[s]? = some x := by
        have : (lens.drop s)[0]? = some x := by rw [hd]; rfl
        simpa using this
      have hdrop : lens.drop (s + 1) = xs := by
        rw [← List.drop_drop, hd]
        rfl
      have hlen' : s + 1 + xs.length = lens.length := by
        simp only [List.length_cons] at hlen
        omega
      have htake : ∀ l, ((lens.take (s + 1)).filter (· == l)).length =
          ((lens.take s).filter (· == l)).length + (if x = l then 1 else 0) := by
        intro l
        rw [List.take_add_one, hget, List.filter_append, List.length_append]
        by_cases hx : x = l <;> simp [hx]
      simp only [foldCodes]
      split
      · rename_i h0
        subst h0
        refine ih (s + 1) nc acc hdrop hlen' hsz ?_ (hz s acc hp hget)
        intro l hl0 hl16
        rw [hnc l hl0 hl16, htake l]
        simp [Ne.symm hl0]
      · rename_i h0
        have hx15 : x ≤ 15 := hl x (List.mem_of_getElem? hget)
        have hc : nc.getD x 0 = (code lens s).getD 0 := by
          rw [hnc x h0 (by omega)]
          simp [code, hget, h0]
        refine ih (s + 1) _ _ hdrop hlen' (by simpa using hsz) ?_ ?_
        · intro l hl0 hl16
          rw [getD_set (by omega), htake l]
          by_cases hxl : l = x
          · subst hxl
            simp [hnc l hl0 hl16]
            omega
          · simp [hxl, Ne.symm hxl, hnc l hl0 hl16]
        · rw [hc]
          exact hs s x acc hp hget h0
  obtain ⟨h1, h2⟩ := nextCodes_spec hl
  refine key lens 0 _ acc (by simp) (by simp) h1 ?_ h0
  intro l hl0 hl16
  simp [h2 l hl16]

end Brotli.Decoder
