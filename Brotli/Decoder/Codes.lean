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

theorem getD_set {cs : Array Nat} {l n v : Nat} (hl : l < cs.size) :
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

/-! ### Visiting the symbols in canonical order -/

/-- The symbols of length `l`, in increasing order. -/
def symsOf (lens : List Nat) (l : Nat) : List Nat := (List.range lens.length).filter (fun s => lens[s]? == some l)

theorem mem_symsOf {lens : List Nat} {l s : Nat} : s ∈ symsOf lens l ↔ lens[s]? = some l := by
  unfold symsOf
  simp only [List.mem_filter, List.mem_range, beq_iff_eq]
  exact ⟨fun h => h.2, fun h => ⟨(List.getElem?_eq_some_iff.mp h).1, h⟩⟩

/-- In a filtered range, the `i`th element has `i` elements of the filter below it. -/
private theorem filter_range_idx (p : Nat → Bool) : ∀ (n i : Nat) (hi : i < ((List.range n).filter p).length),
    ((List.range ((List.range n).filter p)[i]).filter p).length = i := by
  intro n
  induction n with
  | zero => intro i hi; simp at hi
  | succ n ih =>
    intro i hi
    by_cases hp : p n = true
    · have e : (List.range (n + 1)).filter p = (List.range n).filter p ++ [n] := by
        rw [List.range_succ, List.filter_append]
        simp [hp]
      have hi' : i < ((List.range n).filter p).length + 1 := by
        rw [e] at hi
        simpa using hi
      by_cases hlt : i < ((List.range n).filter p).length
      · have g : ((List.range (n + 1)).filter p)[i] = ((List.range n).filter p)[i] := by
          simp only [e]
          exact List.getElem_append_left hlt
        rw [g]
        exact ih i hlt
      · have hie : i = ((List.range n).filter p).length := by omega
        have g : ((List.range (n + 1)).filter p)[i] = n := by
          simp only [e]
          rw [List.getElem_append_right (by omega)]
          simp [hie]
        rw [g, hie]
    · have e : (List.range (n + 1)).filter p = (List.range n).filter p := by
        rw [List.range_succ, List.filter_append]
        simp [hp]
      have hi' : i < ((List.range n).filter p).length := by
        rw [e] at hi
        exact hi
      have g : ((List.range (n + 1)).filter p)[i] = ((List.range n).filter p)[i] := by
        simp only [e]
      rw [g]
      exact ih i hi'

/-- Counting the lengths below `k` in the list or over the range. -/
private theorem filter_range_len (lens : List Nat) (l : Nat) : ∀ k, k ≤ lens.length →
    ((List.range k).filter (fun s => lens[s]? == some l)).length = ((lens.take k).filter (· == l)).length := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.filter_append, List.length_append, ih (by omega), List.take_add_one, List.filter_append,
      List.length_append]
    by_cases he : lens[k] = l <;> simp [he, List.getElem?_eq_getElem (show k < lens.length by omega)]

/-- The `k`th symbol of length `l` has the code `nextCode` plus `k`. -/
theorem code_symsOf {lens : List Nat} {l k : Nat} (hk : k < (symsOf lens l).length) (h0 : l ≠ 0) :
    lens[(symsOf lens l)[k]]? = some l ∧ code lens (symsOf lens l)[k] = some (nextCode lens l + k) := by
  have hmem : (symsOf lens l)[k] ∈ symsOf lens l := List.getElem_mem hk
  have hget := mem_symsOf.mp hmem
  have hlt : (symsOf lens l)[k] < lens.length := (List.getElem?_eq_some_iff.mp hget).1
  refine ⟨hget, ?_⟩
  have hidx := filter_range_idx (fun s => lens[s]? == some l) lens.length k hk
  have hle : ((List.range lens.length).filter (fun s => lens[s]? == some l))[k] ≤ lens.length := Nat.le_of_lt hlt
  rw [filter_range_len lens l _ hle] at hidx
  simp only [code, hget, h0, ↓reduceIte]
  exact congrArg (fun x => some (nextCode lens l + x)) hidx

/-- How many symbols have length `l`. -/
theorem length_symsOf {lens : List Nat} {l : Nat} (h0 : l ≠ 0) : (symsOf lens l).length = blCount lens l := by
  unfold symsOf blCount
  rw [filter_range_len lens l _ (Nat.le_refl _), List.take_length, ite_eq_right h0]

/-- Visits the symbols `ss`, each of length `l`, each with the code one below the last, from `e`. Gives the last code. -/
def walkSyms {β : Type} (f : β → Nat → Nat → Nat → β) (l : Nat) : List Nat → Nat → β → β × Nat
  | [], e, acc => (acc, e)
  | s :: ss, e, acc => walkSyms f l ss (e - 1) (f acc s l (e - 1))

/-- Visits the symbols of lengths `l` down to 1, longest first, from the code above the last of length `l`. -/
def walkFrom {β : Type} (f : β → Nat → Nat → Nat → β) (lens : List Nat) : Nat → Nat → β → β
  | 0, _, acc => acc
  | l + 1, e, acc =>
    let r := walkSyms f (l + 1) (symsOf lens (l + 1)).reverse e acc
    walkFrom f lens l (r.2 / 2) r.1

/-- Visits each symbol that has a code, longest codes first and in decreasing order within a length, each with its code
worked out downwards from the top of the code space. -/
def walkDown {β : Type} (f : β → Nat → Nat → Nat → β) (lens : List Nat) (acc : β) : β := walkFrom f lens 15 32768 acc

/-- A complete code's codes end at the top of the code space. -/
theorem top_code {lens : List Nat} (hC : Complete (.canonical lens)) :
    nextCode lens 15 + blCount lens 15 = 32768 := by
  have h1 := nextCode_sum lens 15 (by decide) (by decide)
  rw [sumUpTo_eq lens hC.1, hC.2] at h1
  simpa using h1

/-- Halving the code above a length's codes gives the code above the next shorter length's. -/
theorem nextCode_half (lens : List Nat) (l : Nat) : nextCode lens (l + 1) / 2 = nextCode lens l + blCount lens l := by
  show ((nextCode lens l + blCount lens l) <<< 1) / 2 = _
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_div_cancel _ (by decide)]

/-- What `walkDown` visits, for a complete code: a property kept by each symbol that has a code, seen with the spec's
`code` once every longer code has been seen, holds at the end, for a list of the symbols seen that has every symbol with
a code. -/
theorem walkDown_ind {β : Type} {f : β → Nat → Nat → Nat → β} {lens : List Nat}
    (hC : Complete (.canonical lens))
    (P : List Nat → β → Prop)
    (hs : ∀ done s l c acc, P done acc → lens[s]? = some l → l ≠ 0 → code lens s = some c →
      (∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) → P (s :: done) (f acc s l c))
    {acc : β} (h0 : P [] acc) :
    ∃ done, P done (walkDown f lens acc) ∧ ∀ s l, lens[s]? = some l → l ≠ 0 → s ∈ done := by
  -- One length: the symbols from the `k`th last, with every longer code seen.
  have hsyms : ∀ (l : Nat), l ≠ 0 → ∀ (N k : Nat) (done : List Nat) (acc : β), (symsOf lens l).length - k = N →
      k ≤ (symsOf lens l).length → P done acc → (∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) →
      ∃ done', P done' (walkSyms f l ((symsOf lens l).reverse.drop k) (nextCode lens l + ((symsOf lens l).length - k)) acc).1 ∧
        (walkSyms f l ((symsOf lens l).reverse.drop k) (nextCode lens l + ((symsOf lens l).length - k)) acc).2 =
          nextCode lens l ∧
        (∀ i (hi : i < (symsOf lens l).length), i + k < (symsOf lens l).length → (symsOf lens l)[i] ∈ done') ∧
        ∀ s ∈ done, s ∈ done' := by
    intro l hl0 N
    induction N with
    | zero =>
      intro k done acc hN hk hp _
      have hd : (symsOf lens l).reverse.drop k = [] := List.drop_eq_nil_of_le (by rw [List.length_reverse]; omega)
      rw [hd, hN, Nat.add_zero]
      exact ⟨done, hp, rfl, fun i hi hle => absurd hle (by omega), fun _ h => h⟩
    | succ N ih =>
      intro k done acc hN hk hp hlong
      have hlt : k < (symsOf lens l).length := by omega
      have hlt' : k < (symsOf lens l).reverse.length := by rw [List.length_reverse]; exact hlt
      have hj : (symsOf lens l).length - 1 - k < (symsOf lens l).length := by omega
      obtain ⟨hg, hc⟩ := code_symsOf hj hl0
      have hrev : (symsOf lens l).reverse[k] = (symsOf lens l)[(symsOf lens l).length - 1 - k] := List.getElem_reverse _
      rw [List.drop_eq_getElem_cons hlt', walkSyms, hrev]
      have he : nextCode lens l + ((symsOf lens l).length - k) - 1 = nextCode lens l + ((symsOf lens l).length - (k + 1)) := by
        omega
      rw [he]
      have hk1 : (symsOf lens l).length - 1 - k = (symsOf lens l).length - (k + 1) := by omega
      have hc' : code lens (symsOf lens l)[(symsOf lens l).length - 1 - k] =
          some (nextCode lens l + ((symsOf lens l).length - (k + 1))) := by
        rw [hc, hk1]
      have hp' := hs done _ l _ acc hp hg hl0 hc' hlong
      obtain ⟨done', h1, h2, h3, h4⟩ := ih (k + 1) _ _ (by omega) (by omega) hp'
        (fun s' l' hg' hl' => List.mem_cons_of_mem _ (hlong s' l' hg' hl'))
      refine ⟨done', h1, h2, fun i hi hle => ?_, fun s hs' => h4 s (List.mem_cons_of_mem _ hs')⟩
      by_cases hei : i = (symsOf lens l).length - 1 - k
      · subst hei
        exact h4 _ List.mem_cons_self
      · exact h3 i hi (by omega)
  -- The lengths, from `l` down.
  have hlens : ∀ (l : Nat) (done : List Nat) (acc : β), P done acc →
      (∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) →
      ∃ done', P done' (walkFrom f lens l (nextCode lens l + blCount lens l) acc) ∧
        (∀ s' l', lens[s']? = some l' → l' ≠ 0 → s' ∈ done') := by
    intro l
    induction l with
    | zero =>
      intro done acc hp hlong
      exact ⟨done, hp, fun s' l' hg h0 => hlong s' l' hg (by omega)⟩
    | succ l ih =>
      intro done acc hp hlong
      have hlen := length_symsOf (lens := lens) (l := l + 1) (by omega)
      obtain ⟨d1, p1, e1, c1, s1⟩ := hsyms (l + 1) (by omega) _ 0 done acc rfl (Nat.zero_le _) hp hlong
      rw [List.drop_zero, Nat.sub_zero, hlen] at p1 e1
      have hnext := nextCode_half lens l
      simp only [walkFrom]
      rw [e1, hnext]
      refine ih d1 _ p1 fun s' l' hg hl' => ?_
      by_cases he : l' = l + 1
      · subst he
        obtain ⟨i, hi, e⟩ := List.getElem_of_mem (mem_symsOf.mpr hg)
        exact e ▸ c1 i hi (by omega)
      · exact s1 s' (hlong s' l' hg (by omega))
  have htop := top_code hC
  obtain ⟨done, p, c⟩ := hlens 15 [] acc h0 fun s' l' hg hl' =>
    absurd hl' (by have := hC.1 l' (List.mem_of_getElem? hg); omega)
  unfold walkDown
  rw [← htop]
  exact ⟨done, p, c⟩

end Brotli.Decoder
