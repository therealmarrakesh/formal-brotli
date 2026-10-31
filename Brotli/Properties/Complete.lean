import Brotli.Spec.Stream

/-!
# Complete prefix codes

Every prefix code read from a stream fills its code space exactly, so `decodeSymbol` can only fail by running
out of bits. A stream is never rejected because its bits fall in a gap of a code.
-/

namespace Brotli.Properties

open Brotli.Spec

private theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => simp [bind] at h
  | some a => exact ⟨a, rfl, h⟩

/-- A single-symbol code, or a canonical code with lengths at most 15 that fill the code space exactly. -/
def Complete : PrefixCode → Prop
  | .single _ => True
  | .canonical lens => (∀ l ∈ lens, l ≤ 15) ∧ lengthSum lens = 32768

/-! ### Decoding with a complete code -/

/-- The sum of `2 ^ (15 - k)` over the codes of lengths `1, …, l`. -/
private def sumUpTo (lens : List Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => sumUpTo lens l + blCount lens (l + 1) * 2 ^ (15 - (l + 1))

private theorem blCount_cons (x : Nat) (xs : List Nat) (k : Nat) :
    blCount (x :: xs) k = blCount xs k + (if k ≠ 0 ∧ x = k then 1 else 0) := by
  unfold blCount
  by_cases hk : k = 0
  · simp [hk]
  · by_cases hx : x = k <;> simp [hk, hx]

private theorem sumUpTo_cons (x : Nat) (xs : List Nat) : ∀ l,
    sumUpTo (x :: xs) l = sumUpTo xs l + (if 1 ≤ x ∧ x ≤ l then 2 ^ (15 - x) else 0)
  | 0 => by simp [sumUpTo]; omega
  | l + 1 => by
    rw [sumUpTo, sumUpTo, sumUpTo_cons x xs l, blCount_cons, Nat.add_mul]
    by_cases hx1 : x = l + 1
    · subst hx1
      rw [ite_eq_right (show ¬(1 ≤ l + 1 ∧ l + 1 ≤ l) by omega),
        ite_eq_left (show l + 1 ≠ 0 ∧ l + 1 = l + 1 by omega),
        ite_eq_left (show 1 ≤ l + 1 ∧ l + 1 ≤ l + 1 by omega)]
      omega
    · rw [ite_eq_right (show ¬(l + 1 ≠ 0 ∧ x = l + 1) by omega)]
      by_cases hx2 : 1 ≤ x ∧ x ≤ l
      · rw [ite_eq_left hx2, ite_eq_left (show 1 ≤ x ∧ x ≤ l + 1 by omega)]
        omega
      · rw [ite_eq_right hx2, ite_eq_right (show ¬(1 ≤ x ∧ x ≤ l + 1) by omega)]
        omega

private theorem sumUpTo_nil : ∀ m, sumUpTo [] m = 0
  | 0 => rfl
  | m + 1 => by simp [sumUpTo, sumUpTo_nil m, blCount]

private theorem sumUpTo_eq : ∀ lens : List Nat, (∀ l ∈ lens, l ≤ 15) →
    sumUpTo lens 15 = lengthSum lens
  | [], _ => by simp [sumUpTo_nil, lengthSum]
  | x :: xs, h => by
    have hx : x ≤ 15 := h x (by simp)
    have ih := sumUpTo_eq xs fun l hl => h l (List.mem_cons_of_mem _ hl)
    rw [sumUpTo_cons, ih]
    simp only [lengthSum, List.map_cons, List.sum_cons]
    by_cases h0 : x = 0
    · simp [h0]
    · have hshift : 32768 >>> x = 2 ^ (15 - x) := by
        rw [Nat.shiftRight_eq_div_pow, show 32768 = 2 ^ 15 by rfl,
          Nat.pow_div (by omega) (by omega)]
      rw [ite_eq_left (show 1 ≤ x ∧ x ≤ 15 by omega), ite_eq_right h0, hshift]
      omega

private theorem nextCode_sum (lens : List Nat) : ∀ l, 1 ≤ l → l ≤ 15 →
    (nextCode lens l + blCount lens l) * 2 ^ (15 - l) = sumUpTo lens l
  | 0, h, _ => by omega
  | 1, _, _ => by simp [nextCode, sumUpTo, blCount]
  | l + 2, _, h => by
    have ih := nextCode_sum lens (l + 1) (by omega) (by omega)
    rw [show sumUpTo lens (l + 2) =
      sumUpTo lens (l + 1) + blCount lens (l + 2) * 2 ^ (15 - (l + 2)) from rfl, ← ih,
      show nextCode lens (l + 2) = (nextCode lens (l + 1) + blCount lens (l + 1)) <<< 1 from rfl,
      Nat.shiftLeft_eq, show 15 - (l + 1) = (15 - (l + 2)) + 1 by omega, Nat.pow_succ]
    grind

private theorem readCode_exists : ∀ (n : Nat) (bs : List Bool), n ≤ bs.length →
    ∃ v r, readCode n bs = some (v, r)
  | 0, bs, _ => ⟨0, bs, rfl⟩
  | _ + 1, [], h => by simp at h
  | n + 1, b :: bs, h => by
    obtain ⟨v, r, hv⟩ := readCode_exists n bs (by simpa using h)
    exact ⟨b.toNat * 2 ^ n + v, r, by simp [readCode, hv]⟩

private theorem decodeLengths_found (lens : List Nat)
    (hend : nextCode lens 15 + blCount lens 15 = 32768) (bs : List Bool) (hb : 15 ≤ bs.length) :
    ∀ (k l : Nat), 1 ≤ l → l ≤ 15 → l + k = 16 → ∀ (v : Nat) (r : List Bool),
    readCode l bs = some (v, r) → nextCode lens l ≤ v → ∃ s r', decodeLengths lens bs l k = some (s, r')
  | 0, _, _, _, hk, _, _, _, _ => by omega
  | k + 1, l, h1, h2, hk, v, r, hr, hle => by
    simp only [decodeLengths]
    rw [hr]
    dsimp only
    rw [ite_eq_left hle]
    have hlen := symbolsOfLength_length lens (len := l) (by omega)
    by_cases hin : v - nextCode lens l < blCount lens l
    · rw [List.getElem?_eq_getElem (by rw [hlen]; exact hin)]
      exact ⟨_, _, rfl⟩
    · rw [List.getElem?_eq_none (by rw [hlen]; omega)]
      dsimp only
      by_cases hk0 : k = 0
      · have hl : l = 15 := by omega
        subst hl
        have := readCode_lt 15 bs v r hr
        have h32 : (2 : Nat) ^ 15 = 32768 := by decide
        omega
      · obtain ⟨v', r', hv'⟩ := readCode_exists (l + 1) bs (by omega)
        have hsplit := readCode_add l 1 bs
        rw [hv', hr] at hsplit
        simp only [Option.bind_some] at hsplit
        cases hbit : readCode 1 r with
        | none => rw [hbit] at hsplit; simp at hsplit
        | some q =>
          obtain ⟨w, r2⟩ := q
          rw [hbit] at hsplit
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsplit
          have hnext : nextCode lens (l + 1) = (nextCode lens l + blCount lens l) * 2 := by
            show (nextCode lens l + blCount lens l) <<< 1 = _
            rw [Nat.shiftLeft_eq, Nat.pow_one]
          refine decodeLengths_found lens hend bs hb k (l + 1) (by omega) (by omega) (by omega) v' r' hv' ?_
          rw [hnext, hsplit.1, Nat.pow_one]
          omega

/-- With a complete code, any 15 or more bits decode to a symbol. -/
theorem decodeSymbol_complete {c : PrefixCode} (hc : Complete c) {bs : List Bool} (hb : 15 ≤ bs.length) :
    ∃ s r, decodeSymbol c bs = some (s, r) := by
  cases c with
  | single sym => exact ⟨sym, bs, rfl⟩
  | canonical lens =>
    have hend : nextCode lens 15 + blCount lens 15 = 32768 := by
      have h := nextCode_sum lens 15 (by decide) (by decide)
      rw [sumUpTo_eq lens hc.1, hc.2] at h
      simpa using h
    obtain ⟨v, r, hv⟩ := readCode_exists 1 bs (by omega)
    exact decodeLengths_found lens hend bs hb 15 1 (by decide) (by decide) (by decide) v r hv
      (by simp [nextCode, blCount])

/-! ### The sum of `lengthsOf` -/

private theorem sum_update_eq (t : Nat → Nat) (ht : t 0 = 0) (s v : Nat) (g : Nat → Nat) (hg : g s = 0) :
    ∀ xs : List Nat, xs.Nodup → s ∈ xs →
    (xs.map fun n => t (if n = s then v else g n)).sum = t v + (xs.map fun n => t (g n)).sum
  | [], _, h => by simp at h
  | x :: xs, hnd, hs => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = s
    · subst hx
      have : (xs.map fun n => t (if n = x then v else g n)) = xs.map fun n => t (g n) :=
        List.map_congr_left fun n hn => by
          rw [ite_eq_right (show ¬n = x from fun h => hnd.1 (h ▸ hn))]
      rw [ite_eq_left rfl, this, hg, ht]
      omega
    · rw [ite_eq_right hx]
      have hs' : s ∈ xs := by
        rcases List.mem_cons.mp hs with h | h
        · exact absurd h.symm hx
        · exact h
      have := sum_update_eq t ht s v g hg xs hnd.2 hs'
      omega

private theorem lengthsOf_cons (size s v : Nat) (rest : List (Nat × Nat)) :
    lengthsOf size ((s, v) :: rest) =
      (List.range size).map fun n => if n = s then v else ((rest.find? (·.1 == n)).map (·.2)).getD 0 := by
  unfold lengthsOf
  apply List.map_congr_left
  intro n _
  by_cases h : s = n
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- With distinct symbols inside the alphabet, `lengthsOf` keeps the sum of the lengths it is given. -/
theorem lengthSum_lengthsOf_eq (size : Nat) : ∀ assigned : List (Nat × Nat),
    (assigned.map (·.1)).Nodup → (∀ p ∈ assigned, p.1 < size) →
    lengthSum (lengthsOf size assigned) = lengthSum (assigned.map (·.2))
  | [], _, _ => by simp [lengthSum, lengthsOf, List.map_const', List.sum_replicate_nat]
  | (s, v) :: rest, hnd, hlt => by
    simp only [List.map_cons] at hnd
    rw [List.nodup_cons] at hnd
    have ih := lengthSum_lengthsOf_eq size rest hnd.2
      fun p hp => hlt p (List.mem_cons_of_mem _ hp)
    have hg : ((rest.find? (·.1 == s)).map (·.2)).getD 0 = 0 := by
      have : rest.find? (·.1 == s) = none := by
        rw [List.find?_eq_none]
        intro p hp
        have : p.1 ≠ s := fun h => hnd.1 (List.mem_map.mpr ⟨p, hp, h⟩)
        simpa using this
      simp [this]
    have hs : s < size := hlt (s, v) (by simp)
    rw [lengthsOf_cons]
    unfold lengthSum at ih ⊢
    rw [List.map_map]
    unfold lengthsOf at ih
    rw [List.map_map] at ih
    have := sum_update_eq (fun l => if l = 0 then 0 else 32768 >>> l) rfl s v
      (fun n => ((rest.find? (·.1 == n)).map (·.2)).getD 0) hg (List.range size) List.nodup_range
      (List.mem_range.mpr hs)
    simp only [Function.comp_def] at this ih ⊢
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ### Simple prefix codes -/

private theorem readSimpleSymbols_lt (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (bs : List Bool) (out : List Nat) (r : List Bool), (∀ x ∈ syms, x < size) →
    readSimpleSymbols size bits n syms bs = some (out, r) → ∀ x ∈ out, x < size
  | 0, _, _, out, _, hs, h => by
    simp only [readSimpleSymbols, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  | n + 1, syms, bs, out, r, hs, h => by
    simp only [readSimpleSymbols] at h
    obtain ⟨⟨v, bs1⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · simp at h
    · rename_i hnot
      have hv : v < size := Nat.lt_of_not_le fun hc => hnot (Or.inl hc)
      refine readSimpleSymbols_lt size bits n _ bs1 out r ?_ h
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hs x hx
      · rw [List.mem_singleton.mp hx]
        exact hv

private theorem readSimple_sum {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readSimple size bs = some (c, r)) :
    ∀ lens, c = .canonical lens → lengthSum lens = 32768 := by
  intro lens hc
  unfold readSimple at h
  obtain ⟨⟨nsym, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨syms, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have hnd := readSimpleSymbols_nodup _ _ _ _ _ _ _ List.nodup_nil h2
  have hlt := readSimpleSymbols_lt _ _ _ _ _ _ _ (by simp) h2
  match syms, h, hnd, hlt with
  | [], h, _, _ => simp at h
  | [_], h, _, _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hc
    simp at hc
  | [s1, s2], h, hnd, hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hc
    simp only [PrefixCode.canonical.injEq] at hc
    rw [← hc, lengthSum_lengthsOf_eq size [(s1, 1), (s2, 1)] hnd (by simpa using hlt)]
    simp [lengthSum]
  | [s1, s2, s3], h, hnd, hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hc
    simp only [PrefixCode.canonical.injEq] at hc
    rw [← hc, lengthSum_lengthsOf_eq size [(s1, 1), (s2, 2), (s3, 2)] hnd (by simpa using hlt)]
    simp [lengthSum]
  | [s1, s2, s3, s4], h, hnd, hlt =>
    dsimp only at h
    obtain ⟨⟨ts, bs3⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hc
      simp only [PrefixCode.canonical.injEq] at hc
      rw [← hc, lengthSum_lengthsOf_eq size [(s1, 2), (s2, 2), (s3, 2), (s4, 2)] hnd
        (by simpa using hlt)]
      simp [lengthSum]
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hc
      simp only [PrefixCode.canonical.injEq] at hc
      rw [← hc, lengthSum_lengthsOf_eq size [(s1, 1), (s2, 2), (s3, 3), (s4, 3)] hnd
        (by simpa using hlt)]
      simp [lengthSum]
  | _ :: _ :: _ :: _ :: _ :: _, h, _, _ => simp at h

/-- Every prefix code read from a stream is complete (§3). -/
theorem readPrefixCode_complete {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) : Complete c := by
  have hfit := readPrefixCode_fits h
  have hsum : ∀ lens, c = .canonical lens → lengthSum lens = 32768 := by
    intro lens hc
    unfold readPrefixCode at h
    obtain ⟨⟨hskip, bs1⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · exact readSimple_sum h lens hc
    · unfold readComplex at h
      obtain ⟨⟨pairs, bs2⟩, _, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨ls, bs3⟩, h3, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1] at hc
      simp only [PrefixCode.canonical.injEq] at hc
      rw [← hc]
      exact readSymbolLengths_sum _ _ _ _ _ _ _ h3
  cases c with
  | single _ => trivial
  | canonical lens => exact ⟨hfit.1, hsum lens rfl⟩

/-! ### The code length code -/

/-- The sum of `32 >> code length` over the non-zero code lengths of the pairs. -/
private def sum32 (pairs : List (Nat × Nat)) : Nat :=
  (pairs.map fun p => if p.2 = 0 then 0 else 32 >>> p.2).sum

private theorem sum32_scale : ∀ pairs : List (Nat × Nat), (∀ p ∈ pairs, p.2 ≤ 5) →
    lengthSum (pairs.map (·.2)) = 1024 * sum32 pairs
  | [], _ => by simp [lengthSum, sum32]
  | p :: pairs, h => by
    have ih := sum32_scale pairs fun q hq => h q (List.mem_cons_of_mem _ hq)
    have key : ∀ l, l < 6 → (if l = 0 then 0 else 32768 >>> l) = 1024 * (if l = 0 then 0 else 32 >>> l) := by
      decide
    have hp := key p.2 (by have := h p (by simp); omega)
    simp only [lengthSum, sum32, List.map_cons, List.sum_cons] at ih ⊢
    rw [hp, ih, Nat.mul_add]

private theorem readCodeLengthCodeLengths_spec : ∀ (order : List Nat) (acc : List (Nat × Nat))
    (sum : Nat) (bs : List Bool) (pairs : List (Nat × Nat)) (r : List Bool),
    order.Nodup → (∀ x ∈ order, x < 18) → (∀ p ∈ acc, p.1 < 18 ∧ p.1 ∉ order ∧ p.2 ≤ 5) →
    (acc.map (·.1)).Nodup → sum = sum32 acc →
    readCodeLengthCodeLengths order acc sum bs = some (pairs, r) →
    (pairs.filter (·.2 != 0)).length = 1 ∨
      (sum32 pairs = 32 ∧ (pairs.map (·.1)).Nodup ∧ ∀ p ∈ pairs, p.1 < 18 ∧ p.2 ≤ 5)
  | [], _, _, _, pairs, _, _, _, _, _, _, h => by
    simp only [readCodeLengthCodeLengths] at h
    split at h
    · rename_i hone
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact Or.inl hone
    · simp at h
  | sym :: order, acc, sum, bs, pairs, r, hnd, hlt, hacc, hkeys, hsum, h => by
    simp only [readCodeLengthCodeLengths] at h
    obtain ⟨⟨len, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    rw [List.nodup_cons] at hnd
    have hlen := (readCodeLengthCodeLength_width h1).1
    have hsym : sym < 18 := hlt sym (by simp)
    have hacc' : ∀ p ∈ acc ++ [(sym, len)], p.1 < 18 ∧ p.1 ∉ order ∧ p.2 ≤ 5 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨a, b, c⟩ := hacc p hp
        exact ⟨a, fun hm => b (List.mem_cons_of_mem _ hm), c⟩
      · rw [List.mem_singleton.mp hp]
        exact ⟨hsym, hnd.1, hlen⟩
    have hkeys' : ((acc ++ [(sym, len)]).map (·.1)).Nodup := by
      rw [List.map_append]
      refine List.pairwise_append.mpr ⟨hkeys, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      intro he
      exact (hacc p hp).2.1 (by rw [he]; simp)
    have hlt' : ∀ x ∈ order, x < 18 := fun x hx => hlt x (List.mem_cons_of_mem _ hx)
    split at h
    · rename_i h0
      refine readCodeLengthCodeLengths_spec order _ _ bs1 pairs r hnd.2 hlt' hacc' hkeys' ?_ h
      simp [sum32, hsum, h0]
    · rename_i h0
      have hsum' : sum + 32 >>> len = sum32 (acc ++ [(sym, len)]) := by
        simp [sum32, hsum, h0]
      split at h
      · rename_i hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact Or.inr ⟨by rw [← hsum', hs], hkeys', fun p hp => ⟨(hacc' p hp).1, (hacc' p hp).2.2⟩⟩
      · split at h
        · simp at h
        · exact readCodeLengthCodeLengths_spec order _ _ bs1 pairs r hnd.2 hlt' hacc' hkeys' hsum' h

private theorem codeLengthOrder_ok : codeLengthOrder.Nodup ∧ ∀ x ∈ codeLengthOrder, x < 18 := by
  decide +kernel

/-- Every code length code read from a stream is complete (§3.5). -/
theorem codeLengthCode_complete {hskip : Nat} {bs r : List Bool} {pairs : List (Nat × Nat)}
    (h : readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs = some (pairs, r)) :
    Complete (codeLengthCode pairs) := by
  have hfit := codeLengthCode_fits h
  have hspec := readCodeLengthCodeLengths_spec _ _ _ _ _ _
    (codeLengthOrder_ok.1.sublist (List.drop_sublist _ _))
    (fun x hx => codeLengthOrder_ok.2 x (List.mem_of_mem_drop hx))
    (by simp) (by simp) (by simp [sum32]) h
  unfold codeLengthCode at hfit ⊢
  split at hfit
  · trivial
  · rename_i hne
    refine ⟨hfit.1, ?_⟩
    rcases hspec with hone | ⟨hs, hk, hb⟩
    · obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
      obtain ⟨sym, l⟩ := x
      exact absurd hx (hne sym l)
    · rw [lengthSum_lengthsOf_eq 18 pairs hk (fun p hp => (hb p hp).1),
        sum32_scale pairs (fun p hp => (hb p hp).2), hs]

/-! ### Only running out of bits fails -/

/-- A prefix code read from a stream decodes a symbol from any 15 or more bits. -/
theorem readPrefixCode_decodes {size : Nat} {bs r b : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) (hb : 15 ≤ b.length) :
    ∃ s r', decodeSymbol c b = some (s, r') :=
  decodeSymbol_complete (readPrefixCode_complete h) hb

/-- Decoding with a prefix code read from a stream fails only with fewer than 15 bits left. -/
theorem decodeSymbol_none_short {size : Nat} {bs r b : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) (hn : decodeSymbol c b = none) : b.length < 15 := by
  refine Nat.lt_of_not_le fun hb => ?_
  obtain ⟨s, r', hs⟩ := readPrefixCode_decodes h hb
  rw [hs] at hn
  simp at hn

/-- Decoding with a code length code read from a stream fails only with fewer than 15 bits left. -/
theorem codeLengthCode_none_short {hskip : Nat} {bs r b : List Bool} {pairs : List (Nat × Nat)}
    (h : readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs = some (pairs, r))
    (hn : decodeSymbol (codeLengthCode pairs) b = none) : b.length < 15 := by
  refine Nat.lt_of_not_le fun hb => ?_
  obtain ⟨s, r', hs⟩ := decodeSymbol_complete (codeLengthCode_complete h) hb
  rw [hs] at hn
  simp at hn

end Brotli.Properties
