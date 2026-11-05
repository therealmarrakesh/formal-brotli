import Brotli.Decoder.TableSize
import Brotli.Decoder.Builder

/-!
# The decoder's work, loop by loop

The work model counts each round of each loop, and each `copySlice` by the bytes it moves: a copy within one array
copies the whole array (`docs/lean-facts.md`), so it counts that array's bytes too. A function here mirrors the loop of
the same name without its `W`, round by round, and the theorems after it bound it.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Zeros -/

/-- The work of `zeroExtend`: the bytes it copies, and a round for each piece of at most 65536. -/
def zeroExtendW (n : Nat) : Nat :=
  if _h : n ≤ 65536 then n + 1 else 65537 + zeroExtendW (n - 65536)
termination_by n
decreasing_by omega

theorem zeroExtendW_le : ∀ n : Nat, zeroExtendW n ≤ n + n / 65536 + 1 := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [zeroExtendW]
    by_cases h : n ≤ 65536
    · rw [dite_eq_left h]
      omega
    · rw [dite_eq_right h]
      have := ih (n - 65536) (by omega)
      omega

/-- The work of `zeroBytes`. -/
def zbW (k : Nat) : Nat := zeroExtendW k

theorem zbW_le (k : Nat) : zbW k ≤ k + k / 65536 + 1 := zeroExtendW_le k

/-! ### Sums over a code's symbols -/

/-- A symbol's term: `h s l c` for a symbol with a code of length `l` and code word `c`, nothing otherwise. -/
def termAt (L : List Nat) (h : Nat → Nat → Nat → Nat) (s : Nat) : Nat :=
  match L[s]? with
  | some l => if l = 0 then 0 else h s l ((code L s).getD 0)
  | none => 0

/-- What a walk over the code words adds up. -/
theorem foldCodes_sum {L : List Nat} (hl : ∀ l ∈ L, l ≤ 15) (h : Nat → Nat → Nat → Nat) (a : Nat) :
    foldCodes (fun acc s l c => acc + h s l c) L 0 (nextCodes L) a = a + ((List.range L.length).map (termAt L h)).sum := by
  have key := foldCodes_ind (f := fun acc s l c => acc + h s l c) hl
    (fun s acc => acc = a + ((List.range s).map (termAt L h)).sum)
    (by
      rintro s acc rfl hz
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [termAt, hz])
    (by
      rintro s l acc rfl hs h0
      rw [List.range_succ, List.map_append, List.sum_append]
      simp [termAt, hs, h0, Nat.add_assoc])
    (acc := a) (by simp)
  exact key

theorem sum_ite_const {α : Type} (P : α → Bool) (c : Nat) : ∀ (L : List α), (L.map fun a => if P a then c else 0).sum = L.countP P * c
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, sum_ite_const P c L, List.countP_cons]
    by_cases hp : P a = true
    · simp [hp, Nat.add_mul]
      omega
    · simp [hp]

theorem sum_sumR {α : Type} (f : α → Nat → Nat) (m : Nat) : ∀ (L : List α),
    (L.map fun a => sumR (f a) m).sum = sumR (fun j => (L.map fun a => f a j).sum) m
  | [] => by simp [sumR_zero]
  | a :: L => by
    rw [List.map_cons, List.sum_cons, sum_sumR f m L]
    simp only [List.map_cons, List.sum_cons]
    rw [sumR_add]

theorem sumR_shift (f : Nat → Nat) (a : Nat) : ∀ b, sumR f (a + b) = sumR f a + sumR (fun j => f (j + a)) b
  | 0 => by simp [sumR]
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by omega, sumR, sumR_shift f a b, sumR, Nat.add_comm b a]
    omega

/-- A symbol's term is the term of its length. -/
theorem termAt_split {L : List Nat} (hl : ∀ l ∈ L, l ≤ 15) (h : Nat → Nat → Nat → Nat) (s : Nat) :
    termAt L h s = sumR (fun j => if L[s]? = some (j + 1) then h s (j + 1) ((code L s).getD 0) else 0) 15 := by
  unfold termAt
  cases e : L[s]? with
  | none => simp [sumR_zero]
  | some l =>
    have hl15 : l ≤ 15 := hl l (List.mem_of_getElem? e)
    dsimp only
    by_cases h0 : l = 0
    · rw [ite_eq_left h0]
      symm
      have : (fun j => if some l = some (j + 1) then h s (j + 1) ((code L s).getD 0) else 0) = fun _ => 0 := by
        funext j
        simp only [Option.some.injEq]
        rw [ite_eq_right (by omega)]
      rw [this, sumR_zero]
    · rw [ite_eq_right h0]
      have : (fun j => if some l = some (j + 1) then h s (j + 1) ((code L s).getD 0) else 0) =
          fun j => if j = l - 1 then h s l ((code L s).getD 0) else 0 := by
        funext j
        simp only [Option.some.injEq]
        by_cases hj : j = l - 1
        · rw [ite_eq_left (by omega), ite_eq_left hj, show j + 1 = l by omega]
        · rw [ite_eq_right (by omega), ite_eq_right hj]
      rw [this, sumR_oneG, ite_eq_left (by omega)]

/-- The builder's slot writes, as the spec's code words give them: the short code words' and the long ones'. -/
theorem fillSum_split {L : List Nat} (hC : Complete (.canonical L)) :
    ((List.range L.length).map (termAt L fun _ l c => fillCnt L l (rootOf l c))).sum =
      sumR (fun j => blCount L (j + 1) * 2 ^ (8 - (j + 1))) 8 +
        sumR (fun r => sumR (fun j => cntL L (j + 9) r * fillCnt L (j + 9) r) 7) 256 := by
  have hl := hC.1
  rw [List.map_congr_left (fun s _ => termAt_split hl _ s), sum_sumR, show (15 : Nat) = 8 + 7 from rfl, sumR_shift]
  have hshort : sumR (fun j => ((List.range L.length).map fun s =>
      if L[s]? = some (j + 1) then fillCnt L (j + 1) (rootOf (j + 1) ((code L s).getD 0)) else 0).sum) 8 =
      sumR (fun j => blCount L (j + 1) * 2 ^ (8 - (j + 1))) 8 := by
    apply sumR_congr
    intro j hj
    have e : (fun s => if L[s]? = some (j + 1) then fillCnt L (j + 1) (rootOf (j + 1) ((code L s).getD 0)) else 0) =
        fun s => if (L[s]? == some (j + 1) && true) then 2 ^ (8 - (j + 1)) else 0 := by
      funext s
      simp only [fillCnt, beq_iff_eq, Bool.and_true]
      rw [ite_eq_left (show j + 1 ≤ 8 by omega)]
    rw [e, sum_ite_const, countP_idx L (j + 1) (fun _ => true) L.length (Nat.le_refl _), List.countP_true, List.length_range,
      idxOf_length L (by omega)]
  have hlong : sumR (fun j => ((List.range L.length).map fun s =>
      if L[s]? = some (j + 8 + 1) then fillCnt L (j + 8 + 1) (rootOf (j + 8 + 1) ((code L s).getD 0)) else 0).sum) 7 =
      sumR (fun r => sumR (fun j => cntL L (j + 9) r * fillCnt L (j + 9) r) 7) 256 := by
    rw [sumR_comm]
    apply sumR_congr
    intro j hj
    rw [show j + 8 + 1 = j + 9 by omega]
    have e : (fun s => if L[s]? = some (j + 9) then fillCnt L (j + 9) (rootOf (j + 9) ((code L s).getD 0)) else 0) =
        fun s => if (L[s]? == some (j + 9)) = true then fillCnt L (j + 9) (revBits 8 (posOf L s (j + 9) / 128)) else 0 := by
      funext s
      by_cases hs : L[s]? = some (j + 9)
      · rw [ite_eq_left hs, ite_eq_left (by simp [hs]), code_eq hs (by omega), Option.getD_some, rootOf_pos (by omega) (by omega)]
      · rw [ite_eq_right hs, ite_eq_right (by simp [hs])]
    rw [e, sum_split (fun s => L[s]? == some (j + 9)) (fun s => revBits 8 (posOf L s (j + 9) / 128)) (fillCnt L (j + 9)) 256
      _ (fun s _ _ => revBits_lt 8 _)]
    rfl
  rw [hshort, hlong]

/-- The builder's slot writes are at most the table-size bound. -/
theorem fillSum_le {L : List Nat} (hC : Complete (.canonical L)) :
    ((List.range L.length).map (termAt L fun _ l c => fillCnt L l (rootOf l c))).sum ≤ longCount L + 376 := by
  rw [fillSum_split hC]
  exact fill_le hC

/-- With no length longer than eight, the builder writes the root's 256 slots. -/
theorem fillSum_short {L : List Nat} (hC : Complete (.canonical L)) (h8 : ∀ l ∈ L, l ≤ 8) :
    ((List.range L.length).map (termAt L fun _ l c => fillCnt L l (rootOf l c))).sum ≤ 256 := by
  rw [fillSum_split hC]
  exact fill_short hC h8

theorem termAt_add (L : List Nat) (h1 h2 : Nat → Nat → Nat → Nat) (s : Nat) :
    termAt L (fun s l c => h1 s l c + h2 s l c) s = termAt L h1 s + termAt L h2 s := by
  unfold termAt
  cases L[s]? with
  | none => rfl
  | some l => by_cases h0 : l = 0 <;> simp [h0]

theorem termAt_le (L : List Nat) {k : Nat} (h : Nat → Nat → Nat → Nat) (hk : ∀ s l c, h s l c ≤ k) (s : Nat) : termAt L h s ≤ k := by
  unfold termAt
  cases L[s]? with
  | none => exact Nat.zero_le _
  | some l => by_cases h0 : l = 0 <;> simp [h0, hk]

theorem sum_le_mul {α : Type} (f : α → Nat) {k : Nat} (hk : ∀ a, f a ≤ k) : ∀ (L : List α), (L.map f).sum ≤ k * L.length
  | [] => by simp
  | a :: L => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := sum_le_mul f hk L
    have := hk a
    omega

theorem termAt_const (k : Nat) (L : List Nat) (s : Nat) : termAt L (fun _ _ _ => k) s = if L[s]?.getD 0 = 0 then 0 else k := by
  unfold termAt
  cases L[s]? <;> simp

/-- A constant for each non-zero length adds up to that constant for each of them. -/
theorem sum_const_term (k : Nat) : ∀ L : List Nat, ((List.range L.length).map (termAt L fun _ _ _ => k)).sum = k * L.countP (· != 0)
  | [] => by simp
  | a :: L => by
    have ih := sum_const_term k L
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons, List.countP_cons]
    have e : ∀ s, ((termAt (a :: L) fun _ _ _ => k) ∘ Nat.succ) s = (termAt L fun _ _ _ => k) s := by
      intro s
      simp only [Function.comp, termAt_const, List.getElem?_cons_succ]
    rw [List.map_congr_left (fun s _ => e s), ih, termAt_const]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    by_cases ha : a = 0
    · simp [ha]
    · simp [ha, Nat.mul_add]
      omega

theorem sum_add {α : Type} (f g : α → Nat) : ∀ (L : List α), (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons, sum_add f g L]
    omega

theorem lensOf_length {lens : ByteArray} {n : Nat} (hn : n ≤ lens.size) : (lensOf lens n).length = n := by
  unfold lensOf
  rw [List.length_map, List.length_take, ByteArray.size] at *
  simp only [Array.length_toList]
  omega

/-! ### The table builder -/

/-- The work of `fillRun`: a round for each slot, and the last test. -/
def fillRunW (count : Nat) : Nat := count + 1

/-- The work of a step of the walk, as `stepFast` does it on the table `t` from `base`: a short code word's root slots; a
long one's root slot read, then its sub-table opened (the zeros it adds, its root slot written and its slot) or its slots
in the sub-table. -/
def stepW (base : Nat) (t : ByteArray) (l c : Nat) : Nat :=
  if l ≤ 8 then fillRunW (2 ^ (8 - l))
  else if (slotAt t (base + rootOf l c)).1 = 0 then 1 + zeroExtendW (2 * 2 ^ (l - 8)) + 1 + fillRunW 1
  else 1 + fillRunW (2 ^ ((slotAt t (base + rootOf l c)).1 - l))

/-- The work of `walkFast`, round by round, from its length `l`, link `v` and code `e`, on the table it writes, for at most
`N` rounds. -/
def walkW (head next : ByteArray) (base : Nat) : Nat → ByteArray → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | N + 1, t, l, v, e =>
    if v = 0 then (if l ≤ 1 then 1 else 1 + walkW head next base N t (l - 1) (u16At head (l - 1)) (e / 2))
    else
      stepW base t l (e - 1) + 1 +
        walkW head next base N (downStep base t (v - 1) l (e - 1)) l (u16At next (v - 1)) (e - 1)

/-- The work of `buildFast`: the root's zeros, and the walk. -/
def buildFastW (t head next : ByteArray) : Nat :=
  zeroExtendW 512 + walkW head next (t.size / 2) 16384 (t ++ zeros 512) 15 (u16At head 15) 32768

/-- The work of `listsOf`: its two arrays' zeros, and a round for each length. -/
def listsW (n : Nat) : Nat := zbW 32 + zbW (2 * n) + (n + 1)

/-- The work of `buildLens`: the lists, then the builder. -/
def buildLensW (t lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (hs : LensSmall lens n) : Nat :=
  listsW n.toNat + buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2

/-- The work of `buildSingleFast`: 512 zeros, 256 slots written. -/
def buildSingleW : Nat := zeroExtendW 512 + fillRunW 256

/-! ### What the builder's work adds up to -/

/-- Whether symbol `s` is still to be written at the walk's place: its length is below `l`, or is `l` with `s` in the
symbols from the `k`th last on. -/
def pendB (L : List Nat) (l k s : Nat) : Bool :=
  match L[s]? with
  | some l' => l' != 0 && (decide (l' < l) || (l' == l && ((symsOf L l).reverse.drop k).contains s))
  | none => false

/-- A code word's work in the walk, past its root's sub-table: its slots, and three. -/
def wordW (L : List Nat) : Nat → Nat := termAt L fun _ l c => fillCnt L l (rootOf l c) + 3

/-- The work left for the code words still to write. -/
def remW (L : List Nat) (l k : Nat) : Nat :=
  ((List.range L.length).map fun s => if pendB L l k s then wordW L s else 0).sum

private theorem sum_congr_pt {f g : Nat → Nat} : ∀ (L : List Nat), (∀ s ∈ L, f s = g s) → (L.map f).sum = (L.map g).sum
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    rw [h a List.mem_cons_self, sum_congr_pt L fun s hs => h s (List.mem_cons_of_mem _ hs)]

/-- A sum over symbols below `n`, of those a test picks, gains `f s0` when the test picks `s0` too. -/
private theorem sum_pick {P P' : Nat → Bool} {f : Nat → Nat} {s0 : Nat} (hP : ∀ s, P s = (P' s || s == s0))
    (h0 : P' s0 = false) : ∀ n, s0 < n →
    ((List.range n).map fun s => if P s then f s else 0).sum = ((List.range n).map fun s => if P' s then f s else 0).sum + f s0
  | 0, h => absurd h (by omega)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    by_cases hn : n = s0
    · subst hn
      have e : ((List.range n).map fun s => if P s then f s else 0).sum =
          ((List.range n).map fun s => if P' s then f s else 0).sum := by
        apply sum_congr_pt
        intro s hs
        have := List.mem_range.mp hs
        rw [hP s, show (s == n) = false by simp; omega, Bool.or_false]
      rw [e, hP n, h0]
      simp
    · rw [sum_pick hP h0 n (by omega), hP n]
      have : (n == s0) = false := by simp [hn]
      rw [this, Bool.or_false]
      omega

private theorem symsOf_len_ne {L : List Nat} {l s : Nat} (hs : s ∈ symsOf L l) : L[s]? = some l := mem_symsOf.mp hs

/-- The symbols from the `k`th last on are below the `k`th last. -/
private theorem drop_lt {L : List Nat} {l k s : Nat} (hk : k < (symsOf L l).length)
    (hs : s ∈ (symsOf L l).reverse.drop (k + 1)) : s < (symsOf L l)[(symsOf L l).length - 1 - k] := by
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hs
  have hj' : k + 1 + j < (symsOf L l).reverse.length := by
    rw [List.length_drop] at hj
    omega
  rw [List.getElem_drop, List.getElem_reverse] at e
  rw [← e]
  exact symsOf_lt (by rw [List.length_reverse] at hj'; omega) (by omega)

/-- Writing the `k`th last symbol of length `l` takes its work off what is left. -/
theorem remW_step {L : List Nat} {l k : Nat} (hl : l ≠ 0) (hk : k < (symsOf L l).length) :
    remW L l k = remW L l (k + 1) + wordW L (symsOf L l)[(symsOf L l).length - 1 - k] := by
  have hd : (symsOf L l).reverse.drop k =
      (symsOf L l)[(symsOf L l).length - 1 - k] :: (symsOf L l).reverse.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [List.length_reverse]; exact hk), List.getElem_reverse]
  generalize hs0 : (symsOf L l)[(symsOf L l).length - 1 - k] = s0 at hd
  have hmem : s0 ∈ symsOf L l := by rw [← hs0]; exact List.getElem_mem _
  have hg := symsOf_len_ne hmem
  have hlt := (List.getElem?_eq_some_iff.mp hg).1
  unfold remW
  refine sum_pick (P' := fun s => pendB L l (k + 1) s) (fun s => ?_) ?_ _ hlt
  · unfold pendB
    rw [hd]
    cases e : L[s]? with
    | none =>
      have : (s == s0) = false := by
        simp only [beq_eq_false_iff_ne]
        intro h
        rw [h, hg] at e
        cases e
      rw [this]
      rfl
    | some l' =>
      simp only [List.contains_cons]
      by_cases hss : s = s0
      · subst hss
        rw [hg] at e
        cases e
        simp [hl]
      · have : (s == s0) = false := by simp [hss]
        rw [this]
        simp
  · unfold pendB
    rw [hg]
    have hnot : s0 ∉ (symsOf L l).reverse.drop (k + 1) := by
      intro hm
      have := drop_lt hk hm
      rw [hs0] at this
      omega
    simp [hnot]

/-- At the end of a length's symbols, what is left is the shorter lengths'. -/
theorem remW_down {L : List Nat} {l : Nat} (hl : 1 < l) : remW L l (symsOf L l).length = remW L (l - 1) 0 := by
  unfold remW
  apply sum_congr_pt
  intro s _
  have e : pendB L l (symsOf L l).length s = pendB L (l - 1) 0 s := by
    unfold pendB
    rw [List.drop_eq_nil_of_le (by rw [List.length_reverse]; exact Nat.le_refl _), List.drop_zero]
    cases h : L[s]? with
    | none => rfl
    | some l' =>
      dsimp only
      have hc : (symsOf L (l - 1)).reverse.contains s = (l' == l - 1) := by
        rw [Bool.eq_iff_iff, List.contains_iff_mem, List.mem_reverse, mem_symsOf, h, beq_iff_eq, Option.some.injEq]
      rw [hc, Bool.eq_iff_iff]
      simp only [List.contains_nil, Bool.and_false, Bool.or_false, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq]
      omega
  rw [e]

/-- After the last length, nothing is left. -/
theorem remW_end {L : List Nat} : remW L 1 (symsOf L 1).length = 0 := by
  unfold remW
  have hp : ∀ s, pendB L 1 (symsOf L 1).length s = false := by
    intro s
    unfold pendB
    rw [List.drop_eq_nil_of_le (by rw [List.length_reverse]; exact Nat.le_refl _)]
    cases h : L[s]? with
    | none => rfl
    | some l' =>
      dsimp only
      rw [Bool.eq_false_iff]
      simp only [ne_eq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, beq_iff_eq, List.contains_nil,
        Bool.false_eq_true, and_false, or_false]
      omega
  have : ∀ s ∈ List.range L.length, (if pendB L 1 (symsOf L 1).length s then wordW L s else 0) = 0 := by
    intro s _
    rw [hp s]
    rfl
  rw [sum_congr_pt _ this, List.map_const', List.sum_replicate_nat, Nat.mul_zero]

/-- At the walk's start, every code word is left. -/
theorem remW_start {L : List Nat} (hl : ∀ l ∈ L, l ≤ 15) :
    remW L 15 0 = ((List.range L.length).map (wordW L)).sum := by
  unfold remW
  apply sum_congr_pt
  intro s _
  unfold pendB wordW termAt
  cases h : L[s]? with
  | none => rfl
  | some l' =>
    have h15 : l' ≤ 15 := hl l' (List.mem_of_getElem? h)
    dsimp only
    by_cases h0 : l' = 0
    · simp [h0]
    · rw [List.drop_zero]
      have hp : (l' != 0 && (decide (l' < 15) || (l' == 15 && (symsOf L 15).reverse.contains s))) = true := by
        by_cases h15' : l' = 15
        · subst h15'
          have : (symsOf L 15).reverse.contains s = true := by
            rw [List.contains_iff_mem, List.mem_reverse, mem_symsOf]
            exact h
          rw [this]
          rfl
        · have : l' < 15 := by omega
          simp [h0, this]
      rw [ite_eq_left hp]

/-- The work of a step is its code word's work, less three, and three for each slot the table grows by at most. -/
theorem stepW_pay {L : List Nat} {t0 head next t : ByteArray} {base l v e k : Nat}
    (h : WalkAt L t0 head next base t l v e k) (hv : v ≠ 0) (F : Nat)
    (hF : 2 * (base + 256 + offSum (depths L) 256) = F) :
    stepW base t l (e - 1) + 3 * ((F - (downStep base t (v - 1) l (e - 1)).size) / 2) + 1 ≤
      wordW L (v - 1) + 3 * ((F - t.size) / 2) := by
  obtain ⟨hk, _, hvs, _, _⟩ := h.next_sym hv
  obtain ⟨done, ops, o, hinv, hlong, _⟩ := h.inv
  have hC := h.complete
  have hl0 : l ≠ 0 := by have := h.lrange; omega
  obtain ⟨hg, hc⟩ := code_symsOf (lens := L) (l := l) (k := (symsOf L l).length - 1 - k) (by omega) hl0
  have he : e - 1 = nextCode L l + ((symsOf L l).length - 1 - k) := by
    have := h.ecode
    omega
  have hs : v - 1 = (symsOf L l)[(symsOf L l).length - 1 - k] := by omega
  rw [he, hs]
  generalize (symsOf L l)[(symsOf L l).length - 1 - k] = s at hg hc
  generalize nextCode L l + ((symsOf L l).length - 1 - k) = c at hc
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hg)
  have hw : wordW L s = fillCnt L l (rootOf l c) + 3 := by
    unfold wordW termAt
    rw [hg]
    simp [hl0, hc]
  rw [hw]
  have hsize := hinv.size
  have hop := opSum_le ops (depths L) 256
  unfold stepW downStep fillCnt fillRunW
  by_cases hl8 : l ≤ 8
  · rw [ite_eq_left hl8, ite_eq_left hl8, ite_eq_left hl8, size_writeRange]
    omega
  · rw [ite_eq_right hl8, ite_eq_right hl8, ite_eq_right hl8]
    dsimp only
    have hdge := (depths_spec hC.1).2.2.2 s l c ⟨hg, by omega, hc⟩
    by_cases hz : (slotAt t (base + rootOf l c)).1 = 0
    · rw [ite_eq_left hz, ite_eq_left hz, size_writeRange]
      obtain ⟨hdeq, hinv'⟩ := hinv.openR hC h.small hg hc (by omega) hlong hz
      have hsz' := hinv'.size
      have hop' := opSum_le (rootOf l c :: ops) (depths L) 256
      have hsz1 : (openSub base t (rootOf l c) l).size = t.size + 2 * 2 ^ (l - 8) := by
        unfold openSub
        rw [size_writeSlot, ByteArray.size_append, size_zeros]
      have hz2 := zeroExtendW_le (2 * 2 ^ (l - 8))
      have hp1 : 2 ≤ 2 ^ (l - 8) := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ l - 8 by omega)
        simpa using this
      have hp7 : 2 ^ (l - 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have hdiv : 2 * 2 ^ (l - 8) / 65536 = 0 := Nat.div_eq_of_lt (by omega)
      rw [hsz1, hdeq, Nat.sub_self, Nat.pow_zero]
      omega
    · rw [ite_eq_right hz, ite_eq_right hz, size_writeRange]
      have hm : rootOf l c ∈ ops := Classical.byContradiction fun hn => hz (hinv.empty _ (rootOf_lt l c) hn (by omega))
      obtain ⟨_, _, h3, _⟩ := hinv.opsOk _ hm
      rw [h3]
      dsimp only
      rw [show 8 + (depths L).getD (rootOf l c) 0 - l = (depths L).getD (rootOf l c) 0 - (l - 8) by omega]
      omega

private theorem dec_down {l v N x : Nat} (hl : 1 < l) (hx : x ≤ 704) (hN : l * 1024 + v < N + 1) :
    (l - 1) * 1024 + x < N := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  rw [Nat.succ_mul] at hN
  generalize m * 1024 = A at hN ⊢
  omega

private theorem dec_next {l v N x : Nat} (hx : x < v) (hN : l * 1024 + v < N + 1) : l * 1024 + x < N := by omega

private theorem pay_down {W R R' P l : Nat} (hl : 1 < l) (hW : W ≤ R' + P + (l - 1)) (hR : R = R') :
    1 + W ≤ R + P + l := by omega

private theorem pay_next {S W R R1 w P P1 l : Nat} (hW : W ≤ R1 + P1 + l) (hpay : S + P1 + 1 ≤ w + P)
    (hR : R = R1 + w) : S + 1 + W ≤ R + P + l := by omega

/-- The walk's work, from its place, is at most the work left for its code words, three for each slot the table has still
to grow by, and a round for each length left. -/
theorem walkW_le {L : List Nat} {t0 head next : ByteArray} {base : Nat} (F : Nat)
    (hF : 2 * (base + 256 + offSum (depths L) 256) = F) : ∀ (N : Nat) (t : ByteArray) (l v e k : Nat),
    WalkAt L t0 head next base t l v e k → l * 1024 + v < N →
    walkW head next base N t l v e ≤ remW L l k + 3 * ((F - t.size) / 2) + l := by
  intro N
  induction N with
  | zero => intro _ _ _ _ _ _ hN; omega
  | succ N ih =>
    intro t l v e k hw hN
    unfold walkW
    by_cases hv : v = 0
    · rw [ite_eq_left hv]
      have hkk : k = (symsOf L l).length := by
        refine Nat.le_antisymm hw.kle (Nat.le_of_not_lt fun hlt => ?_)
        have hk' : k < (symsOf L l).reverse.length := by rw [List.length_reverse]; exact hlt
        have := hw.chain
        rw [List.drop_eq_getElem_cons hk'] at this
        have : v = _ := this.1
        omega
      by_cases hl : l ≤ 1
      · rw [ite_eq_left hl]
        have := hw.lrange
        omega
      · rw [ite_eq_right hl]
        have hl1 : 1 < l := Nat.lt_of_not_le hl
        have hd := hw.down hv hl1
        have hle := chain_le hd.small _ _ (fun s hs => mem_drop_rev hs) hd.chain
        have hW := ih _ _ _ _ _ hd (dec_down hl1 hle hN)
        rw [hkk]
        exact pay_down hl1 hW (remW_down hl1)
    · rw [ite_eq_right hv]
      obtain ⟨hk, _, hvs, _, _⟩ := hw.next_sym hv
      have hs' := hw.step hv
      obtain ⟨s, hvs', _, hlt⟩ := hw.link_lt hv
      have hlt' : u16At next (v - 1) < v := by
        rw [hvs', Nat.add_sub_cancel]
        rw [hvs'] at hlt
        exact hlt
      have hW := ih _ _ _ _ _ hs' (dec_next hlt' hN)
      have hpay := stepW_pay hw hv F hF
      have hl0 : l ≠ 0 := by have := hw.lrange; omega
      have hstep := remW_step (L := L) hl0 hk
      have hs : v - 1 = (symsOf L l)[(symsOf L l).length - 1 - k] := by
        rw [hvs, Nat.add_sub_cancel]
      rw [← hs] at hstep
      exact pay_next hW hpay hstep

/-- The builder's work: four rounds for each code word longer than 8 bits and three for each code word, from the code
words' slots and the sub-tables' zeros, and 1264 more. -/
theorem buildFastW_le {t head next : ByteArray} {L : List Nat} (ha : BuildArgs t head next L) :
    buildFastW t head next ≤ 3 * L.countP (· != 0) + 4 * longCount L + 1264 := by
  have hw := build_start ha
  rw [half_toNat ha.2.2.2.2.2.2] at hw
  obtain ⟨hC, _, _, _, _, h2, h32⟩ := ha
  have hle := chain_le hw.small _ _ (fun s hs => mem_drop_rev hs) hw.chain
  have hwk := walkW_le (L := L) (base := t.size / 2) _ rfl 16384 _ _ _ _ _ hw (by omega)
  rw [remW_start hC.1, zeroExtend_zeros] at hwk
  have hsum : ((List.range L.length).map (wordW L)).sum ≤ longCount L + 376 + 3 * L.countP (· != 0) := by
    unfold wordW
    rw [List.map_congr_left (fun s _ => termAt_add L (fun _ l c => fillCnt L l (rootOf l c)) (fun _ _ _ => 3) s), sum_add]
    have a := fillSum_le hC
    have b := sum_const_term 3 L
    omega
  have hoff := offSum_le hC
  have hz := zeroExtendW_le 512
  rw [ByteArray.size_append, size_zeros] at hwk
  unfold buildFastW
  generalize walkW head next (t.size / 2) 16384 (t ++ zeros 512) 15 (u16At head 15) 32768 = W at hwk ⊢
  generalize ((List.range L.length).map (wordW L)).sum = S at hwk hsum
  generalize offSum (depths L) 256 = O at hwk hoff
  generalize longCount L = Lc at hsum hoff ⊢
  omega

/-- The builder's work for a code with no code word longer than 8 bits: three rounds for each code word, the root's slots
and zeros, and its rounds. -/
theorem buildFastW_short {t head next : ByteArray} {L : List Nat} (ha : BuildArgs t head next L) (h8 : ∀ l ∈ L, l ≤ 8) :
    buildFastW t head next ≤ 3 * L.countP (· != 0) + 784 := by
  have hw := build_start ha
  rw [half_toNat ha.2.2.2.2.2.2] at hw
  obtain ⟨hC, _, _, _, _, h2, h32⟩ := ha
  have hle := chain_le hw.small _ _ (fun s hs => mem_drop_rev hs) hw.chain
  have hwk := walkW_le (L := L) (base := t.size / 2) _ rfl 16384 _ _ _ _ _ hw (by omega)
  rw [remW_start hC.1, zeroExtend_zeros] at hwk
  have hsum : ((List.range L.length).map (wordW L)).sum ≤ 256 + 3 * L.countP (· != 0) := by
    unfold wordW
    rw [List.map_congr_left (fun s _ => termAt_add L (fun _ l c => fillCnt L l (rootOf l c)) (fun _ _ _ => 3) s), sum_add]
    have a := fillSum_short hC h8
    have b := sum_const_term 3 L
    omega
  have hoff := offSum_short hC.1 h8
  have hz := zeroExtendW_le 512
  rw [ByteArray.size_append, size_zeros] at hwk
  unfold buildFastW
  generalize walkW head next (t.size / 2) 16384 (t ++ zeros 512) 15 (u16At head 15) 32768 = W at hwk ⊢
  generalize ((List.range L.length).map (wordW L)).sum = S at hwk hsum
  generalize offSum (depths L) 256 = O at hwk hoff
  omega

/-- The work of `buildLens`: six rounds for each symbol, four for each code word longer than 8 bits, and 1299 more. -/
theorem buildLensW_le {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} {hs : LensSmall lens n}
    (h : LensArgs t lens n) :
    buildLensW t lens n hn hs ≤ 6 * n.toNat + 4 * longCount (lensOf lens n.toNat) + 1299 := by
  have hb : buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 ≤
      3 * (lensOf lens n.toNat).countP (· != 0) + 4 * longCount (lensOf lens n.toNat) + 1264 := buildFastW_le (lens_build h)
  have hc := List.countP_le_length (p := (· != 0)) (l := lensOf lens n.toNat)
  generalize (lensOf lens n.toNat).countP (· != 0) = nz at hb hc
  have hlen : (lensOf lens n.toNat).length = n.toNat := length_lensOf hn
  have z1 := zbW_le 32
  have z2 := zbW_le (2 * n.toNat)
  have h704 : n.toNat ≤ 704 := h.2.1
  have hd : 2 * n.toNat / 65536 = 0 := Nat.div_eq_of_lt (by omega)
  show listsW n.toNat + buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 ≤ _
  generalize buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 = B at hb ⊢
  generalize longCount (lensOf lens n.toNat) = Lc at hb ⊢
  generalize (lensOf lens n.toNat).length = m at hc hlen
  unfold listsW
  generalize zbW 32 = a at z1 ⊢
  generalize zbW (2 * n.toNat) = b at z2 ⊢
  generalize n.toNat = k at *
  omega

/-- The work of `buildLens` for a code with no code word longer than 8 bits: six rounds for each symbol, and 819. -/
theorem buildLensW_short {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} {hs : LensSmall lens n}
    (h : LensArgs t lens n) (h8 : ∀ l ∈ lensOf lens n.toNat, l ≤ 8) : buildLensW t lens n hn hs ≤ 6 * n.toNat + 819 := by
  have hb : buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 ≤ 3 * (lensOf lens n.toNat).countP (· != 0) + 784 :=
    buildFastW_short (lens_build h) h8
  have hc := List.countP_le_length (p := (· != 0)) (l := lensOf lens n.toNat)
  generalize (lensOf lens n.toNat).countP (· != 0) = nz at hb hc
  have hlen : (lensOf lens n.toNat).length = n.toNat := length_lensOf hn
  have z1 := zbW_le 32
  have z2 := zbW_le (2 * n.toNat)
  have h704 : n.toNat ≤ 704 := h.2.1
  have hd : 2 * n.toNat / 65536 = 0 := Nat.div_eq_of_lt (by omega)
  show listsW n.toNat + buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 ≤ _
  generalize buildFastW t (listsOf lens n hn hs).1 (listsOf lens n hn hs).2 = B at hb ⊢
  generalize (lensOf lens n.toNat).length = m at hc hlen
  unfold listsW
  generalize zbW 32 = a at z1 ⊢
  generalize zbW (2 * n.toNat) = b at z2 ⊢
  generalize n.toNat = k at *
  omega

theorem buildSingleW_le : buildSingleW ≤ 770 := by
  have := zeroExtendW_le 512
  unfold buildSingleW fillRunW
  generalize zeroExtendW 512 = z at this ⊢
  omega

end Brotli.Decoder
