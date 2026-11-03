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

/-- The work of `growZeros`: each round copies the array onto its own end, which copies all of it and the new bytes. -/
def growZerosW (t : ByteArray) (k : Nat) : Nat :=
  if _h : t.size = 0 ∨ k ≤ t.size then 1
  else t.size + min t.size (k - t.size) + 1 + growZerosW (t.copySlice 0 t t.size (min t.size (k - t.size))) k
termination_by k - t.size
decreasing_by
  rw [copy_self_size t (Nat.min_le_left _ _)]
  omega

theorem growZerosW_le : ∀ (N : Nat) (t : ByteArray) (k : Nat), k - t.size = N → growZerosW t k ≤ 5 * k - 3 * t.size + 1 := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro t k hN
    rw [growZerosW]
    by_cases hc : t.size = 0 ∨ k ≤ t.size
    · rw [dite_eq_left hc]
      omega
    · rw [dite_eq_right hc]
      have hs := copy_self_size t (Nat.min_le_left t.size (k - t.size))
      by_cases hfin : k - t.size < t.size
      · -- The last round reaches `k`, and the next is done.
        have e : growZerosW (t.copySlice 0 t t.size (min t.size (k - t.size))) k = 1 := by
          rw [growZerosW, dite_eq_left (Or.inr (by rw [hs]; omega))]
        rw [e]
        omega
      · have := ih (k - (t.copySlice 0 t t.size (min t.size (k - t.size))).size) (by rw [hs]; omega)
          (t.copySlice 0 t t.size (min t.size (k - t.size))) k rfl
        rw [hs] at this
        omega

/-- The work of `zeroBytes`: 64 bytes pushed one at a time, then doubled. -/
def zbW (k : Nat) : Nat := min k 64 + 1 + growZerosW (pushZeros (ByteArray.emptyWithCapacity k) (USize.ofNat (min k 64))) k

theorem zbW_le (k : Nat) : zbW k ≤ 5 * k + 66 := by
  unfold zbW
  have := growZerosW_le _ (pushZeros (ByteArray.emptyWithCapacity k) (USize.ofNat (min k 64))) k rfl
  omega

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

theorem sumR_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i, i < n → f i = g i) → sumR f n = sumR g n
  | 0, _ => rfl
  | n + 1, h => by
    show sumR f n + f n = sumR g n + g n
    rw [sumR_congr (fun i hi => h i (by omega)), h n (by omega)]

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

/-- The builder's slot writes, as the spec's code words give them, are at most the table-size bound. -/
theorem fillSum_le {L : List Nat} (hC : Complete (.canonical L)) :
    ((List.range L.length).map (termAt L fun _ l c => fillCnt L l (rootOf l c))).sum ≤ longCount L + 1024 := by
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
  exact fill_le hC

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

theorem sum_add {α : Type} (f g : α → Nat) : ∀ (L : List α), (L.map fun a => f a + g a).sum = (L.map f).sum + (L.map g).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons, sum_add f g L]
    omega

private theorem u64sub {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

/-! ### The table builder -/

/-- The slots the running builder writes for a code word. -/
def fillCntD (D : ByteArray) (l c : UInt64) : Nat :=
  if l ≤ 8 then ((1 : UInt64) <<< (8 - l)).toNat
  else ((1 : UInt64) <<< ((getU D (revFast l c &&& 255).toUSize).toUInt64 - (l - 8))).toNat

theorem fillCntD_eq {L : List Nat} (hC : Complete (.canonical L)) {D : ByteArray} (hD : ByteMatch (depths L) D)
    {s l c : UInt64} (hs : L[s.toNat]? = some l.toNat) (h0 : l.toNat ≠ 0) (hc : code L s.toNat = some c.toNat) :
    fillCntD D l c = fillCnt L l.toNat (rootOf l.toNat c.toNat) := by
  have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hs)
  have hclt : c.toNat < 2 ^ l.toNat := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  unfold fillCntD fillCnt
  by_cases hl : l.toNat ≤ 8
  · rw [ite_eq_left (UInt64.le_iff_toNat_le.mpr hl), ite_eq_left hl]
    have h8 : (8 - l).toNat = 8 - l.toNat := u64sub (by rw [show (8 : UInt64).toNat = 8 from rfl]; exact hl)
    rw [one_shl (by rw [h8]; omega), h8]
  · have h8' : ¬ l ≤ 8 := fun h => hl (UInt64.le_iff_toNat_le.mp h)
    rw [ite_eq_right h8', ite_eq_right hl]
    have hr := rootIdx hl15 hclt
    have hrlt := rootOf_lt l.toNat c.toNat
    have hl8 : (l - 8).toNat = l.toNat - 8 := u64sub (by rw [show (8 : UInt64).toNat = 8 from rfl]; omega)
    have hd : (getU D (revFast l c &&& 255).toUSize).toUInt64.toNat = (depths L).getD (rootOf l.toNat c.toNat) 0 := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hr, hD.2.2 _ hrlt]
    have hdeep : l.toNat - 8 ≤ (depths L).getD (rootOf l.toNat c.toNat) 0 :=
      (depths_spec hC.1).2.2.2 s.toNat l.toNat c.toNat ⟨hs, by omega, hc⟩
    have hd7 := (depths_spec hC.1).2.1 (rootOf l.toNat c.toNat)
    have hdsub : ((getU D (revFast l c &&& 255).toUSize).toUInt64 - (l - 8)).toNat =
        (depths L).getD (rootOf l.toNat c.toNat) 0 - (l.toNat - 8) := by
      rw [u64sub (by rw [hd, hl8]; exact hdeep), hd, hl8]
    rw [one_shl (by rw [hdsub]; omega), hdsub]

/-- A walk over a code's lengths that adds `h` for each code word adds up what the spec's code words give. -/
theorem walk_sum {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (hC : Complete (.canonical (lensOf lens n.toNat)))
    {nc : ByteArray} (hnc : U16Match (nextCodes (lensOf lens n.toNat)) nc) (f : UInt64 → UInt64 → Nat) (g : Nat → Nat → Nat)
    (hfg : ∀ (s l c : UInt64), (lensOf lens n.toNat)[s.toNat]? = some l.toNat → l.toNat ≠ 0 →
      code (lensOf lens n.toNat) s.toNat = some c.toNat → f l c = g l.toNat c.toNat) :
    walkCodes (fun acc _ l c => acc + f l c) lens n hn 0 nc 0 =
      ((List.range (lensOf lens n.toNat).length).map (termAt (lensOf lens n.toNat) fun _ l c => g l c)).sum := by
  have := walkCodes_rel (g := fun acc _ l c => acc + g l c) (f := fun acc _ l c => acc + f l c) (hn := hn) hC (fun a b => a = b)
    (by
      rintro a b s l c rfl hs h0 hc
      rw [hfg s l c hs h0 hc]) hnc (a := 0) (b := 0) rfl
  rw [← this, foldCodes_sum hC.1, Nat.zero_add]

theorem lensOf_length {lens : ByteArray} {n : Nat} (hn : n ≤ lens.size) : (lensOf lens n).length = n := by
  unfold lensOf
  rw [List.length_map, List.length_take, ByteArray.size] at *
  simp only [Array.length_toList]
  omega

/-- The work of a walk over a code's lengths that does `w` more for each symbol with a code: a round for each symbol, and
that. -/
def walkW (w : UInt64 → UInt64 → Nat) (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (nc : ByteArray) : Nat :=
  n.toNat + 1 + walkCodes (fun acc _ l c => acc + w l c) lens n hn 0 nc 0

/-- The work of `planFast`: the first codes (32 zeros, a count, 16 rounds), the depths (a walk, 256 zeros), and the
offsets (256 rounds, 512 zeros). -/
def planFastW (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) : Nat :=
  zbW 32 + (n.toNat + 1) + 17 + walkW (fun _ _ => 1) lens n hn (firstCodesOf lens n hn) + zbW 256 + 257 + zbW 512

/-- The work of `fillFast`: the zeros it pushes, a walk writing each code word's slots, and 256 root slots. -/
def fillFastW (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (p : Plan) : Nat :=
  p.bytes.toUSize.toNat + 1 + walkW (fun l c => fillCntD p.D l c + 3) lens n hn p.nc + 3 * 256 + 1

/-- The work of `buildFast`. -/
def buildFastW (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) : Nat :=
  planFastW lens n hn + fillFastW lens n hn (planFast lens n hn)

/-- The work of `buildSingleFast`: 1024 zeros pushed, 256 slots written. -/
def buildSingleW : Nat := 1025 + 258

/-- The work of `fitsFast`: at most 256 rounds. -/
def fitsW : Nat := 258

/-- The depths a plan works out, and its first codes. -/
theorem planFast_parts {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) :
    U16Match (nextCodes (lensOf lens n.toNat)) (planFast lens n hn).nc ∧ ByteMatch (depths (lensOf lens n.toNat)) (planFast lens n hn).D := by
  have hfirst := firstCodesOf_spec (hn := hn) h64 hC
  refine ⟨hfirst, ?_⟩
  show ByteMatch _ (walkCodes depthStep lens n hn 0 (firstCodesOf lens n hn) (zeroBytes 256))
  exact walkCodes_rel (g := recordDepth) hC ByteMatch (by
      intro a b s l c hr hs h0 hc
      have hl15 : l.toNat ≤ 15 := hC.1 _ (List.mem_of_getElem? hs)
      exact depthStep_rel hr hl15 (code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc)) hfirst (by
      refine ⟨zeroBytes_size (by decide), by simp, ?_⟩
      intro r _
      rw [zeroBytes_get (by decide)]
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl)

/-- The builder's work: a few rounds for each symbol, five for each slot of its table, and 10400 more. -/
theorem buildFastW_le {lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) :
    buildFastW lens n hn ≤ 8 * n.toNat + 5 * longCount (lensOf lens n.toNat) + 11000 := by
  obtain ⟨hnc, hD⟩ := planFast_parts (hn := hn) h64 hC
  have hfirst := firstCodesOf_spec (hn := hn) h64 hC
  have hlen := lensOf_length hn
  have hL := hC.1
  -- The walk for the depths adds one for each code word.
  have w1 := walk_sum (hn := hn) hC hfirst (fun _ _ => 1) (fun _ _ => 1) (fun _ _ _ _ _ _ => rfl)
  have w1le := sum_le_mul (termAt (lensOf lens n.toNat) fun _ _ _ => 1) (k := 1) (termAt_le _ _ (fun _ _ _ => Nat.le_refl _))
    (List.range (lensOf lens n.toNat).length)
  -- The walk writing the slots adds each code word's slots, and three.
  have w2 := walk_sum (hn := hn) hC hnc (fun l c => fillCntD (planFast lens n hn).D l c + 3) (fun l c => fillCnt (lensOf lens n.toNat) l (rootOf l c) + 3)
    (fun s l c hs h0 hc => by rw [fillCntD_eq hC hD hs h0 hc])
  rw [List.map_congr_left (fun s _ => termAt_add (lensOf lens n.toNat) (fun _ l c => fillCnt (lensOf lens n.toNat) l (rootOf l c))
    (fun _ _ _ => 3) s), sum_add] at w2
  have w2a := fillSum_le hC
  have w2b := sum_le_mul (termAt (lensOf lens n.toNat) fun _ _ _ => 3) (k := 3) (termAt_le _ _ (fun _ _ _ => Nat.le_refl _))
    (List.range (lensOf lens n.toNat).length)
  -- The zeros the table adds.
  obtain ⟨hb, _⟩ := planFast_bytes (hn := hn) h64 hC
  have hoff := offSum_le hC
  have hbu : (planFast lens n hn).bytes.toUSize.toNat = (planFast lens n hn).bytes.toNat := word_toUSize (by omega)
  have z1 := zbW_le 32
  have z2 := zbW_le 256
  have z3 := zbW_le 512
  rw [List.length_range] at w1le w2b
  unfold buildFastW planFastW fillFastW walkW
  rw [w1, w2, hbu, hb]
  omega

end Brotli.Decoder
