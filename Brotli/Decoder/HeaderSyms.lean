import Brotli.Decoder.HeaderLens

/-!
# A prefix code's lengths

The place reading a complex prefix code's lengths, one code length symbol at a time.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- Writes `n` code lengths from `i`. -/
def fillLens (t : ByteArray) (i n : UInt64) (v : UInt8) : ByteArray :=
  if _hn : n = 0 then t else fillLens (setU t i.toUSize v) (i + 1) (n - 1) v
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem fillLens_spec (v : UInt8) : ∀ (N : Nat) (t : ByteArray) (i n : UInt64), n.toNat = N → i.toNat + N < 2 ^ 32 → i.toNat + N ≤ t.size →
    (fillLens t i n v).size = t.size ∧ ∀ j, (fillLens t i n v).data[j]?.getD 0 =
      if i.toNat ≤ j ∧ j < i.toNat + N then v else t.data[j]?.getD 0 := by
  intro N
  induction N with
  | zero =>
    intro t i n hn _ _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [fillLens, dite_eq_left hz]
    refine ⟨rfl, fun j => ?_⟩
    rw [ite_eq_right (by omega)]
  | succ N ih =>
    intro t i n hn h32 hle
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    rw [fillLens, dite_eq_right hz]
    have hsz := size_setU t i.toUSize v
    obtain ⟨h1, h2⟩ := ih (setU t i.toUSize v) (i + 1) (n - 1) hn1 (by rw [hi1]; omega) (by rw [hi1, hsz]; omega)
    refine ⟨by rw [h1, hsz], fun j => ?_⟩
    rw [h2 j, hi1]
    by_cases he : j = i.toNat
    · subst he
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have := setU_get_same (t := t) (i := i.toUSize) (v := v) (by rw [hus]; omega)
      rwa [hus] at this
    · have e : (setU t i.toUSize v).data[j]? = t.data[j]? := setU_get_ne (by rw [hus]; exact he)
      rw [e]
      by_cases hin : i.toNat + 1 ≤ j ∧ j < i.toNat + 1 + N
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

/-- The place reading a code's lengths. -/
def stepHSyms (st : Hd) (pos : USize) : Hd :=
  if st.symSum = 32768 then tableDone { st with pos := pos, status := .next } false 0
  else if st.ln = st.size then markH st pos .bad
  else
    let r := lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      let sym := r.a
      let ln := st.ln
      if sym < 16 then
        let sum := if sym = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> sym)
        if 32768 < sum then markH st pos .bad
        else
          let lens := st.lens
          let prev := if sym = 0 then st.prevLen else sym
          let st0 := clearLens st
          { st0 with
            word := r.word, count := r.count, pos := pos, status := .next, lens := setLen lens ln sym, ln := ln + 1, prevLen := prev
            repCount := 0, symSum := sum }
      else
        let len := if sym = 16 then st.prevLen else 0
        let mult : UInt64 := if sym = 16 then 4 else 8
        let old := if st.repCount ≠ 0 ∧ st.repSym = sym then st.repCount else 0
        let new := if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)
        let delta := new - old
        if st.size < ln + delta then markH st pos .bad
        else
          let sum := if len = 0 then st.symSum else st.symSum + delta * ((32768 : UInt64) >>> len)
          if 32768 < sum then markH st pos .bad
          else
            let lens := st.lens
            let st0 := clearLens st
            { st0 with
              word := r.word, count := r.count, pos := pos, status := .next, lens := fillLens lens ln delta len.toUInt8, ln := ln + delta
              repSym := sym, repCount := new, symSum := sum }

section
variable {α : Type} (K : MetaBlockHeader → List Bool → Option α)

/-- One more code length symbol. -/
theorem hrest_syms_step (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hlt : ls.lens.length < size) (h : lengthSum ls.lens ≠ 32768) :
    hrest K g (.syms o size clc ls) bs = lenSym clc bs >>= fun p =>
      if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else hrest K g (.syms o size clc (applyCodeLength ls p.1.1 p.1.2)) p.2 := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_step bs hlt h]
  cases lenSym clc bs with
  | none => rfl
  | some p =>
    show ((if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else symsFrom size clc (applyCodeLength ls p.1.1 p.1.2) p.2) >>= _) =
      (if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else hrest K g (.syms o size clc (applyCodeLength ls p.1.1 p.1.2)) p.2)
    by_cases h1 : size < (applyCodeLength ls p.1.1 p.1.2).lens.length
    · rw [ite_eq_left h1, ite_eq_left h1]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens
      · rw [ite_eq_left h2, ite_eq_left h2]
        rfl
      · rw [ite_eq_right h2, ite_eq_right h2]
        rfl

/-- The code lengths are done when their space is used up. -/
theorem hrest_syms_done (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hle : ls.lens.length ≤ size) (h : lengthSum ls.lens = 32768) :
    hrest K g (.syms o size clc ls) bs = ownerK K g o (.canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0)) bs := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_done bs hle h]
  rfl

/-- With all the lengths read and space left, the code is invalid. -/
theorem hrest_syms_full (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hlen : ls.lens.length = size) (h : lengthSum ls.lens ≠ 32768) : hrest K g (.syms o size clc ls) bs = none := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_full bs h hlen]
  rfl

end

private theorem lenSym_bounds {clc : PrefixCode} {bs r : List Bool} {s e : Nat} (hs : clc.Symbols 18)
    (h : lenSym clc bs = some ((s, e), r)) : s < 18 ∧ e < 8 := by
  unfold lenSym at h
  cases hd : decodeSymbol clc bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, b1⟩ := p
    rw [hd] at h
    change (readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b1 >>= _) = _ at h
    have hlt := decodeSymbol_lt hs hd
    cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b1 with
    | none => rw [hx] at h; cases h
    | some q =>
      obtain ⟨x, b2⟩ := q
      rw [hx] at h
      have h' : some ((sym, x), b2) = some ((s, e), r) := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      have hxl := readInt_lt _ _ _ _ hx
      obtain ⟨⟨e1, e2⟩, _⟩ := h'
      subst e1
      subst e2
      refine ⟨hlt, ?_⟩
      have hp : 2 ^ (if sym = 16 then 2 else if sym = 17 then 3 else 0) ≤ 2 ^ 3 := by
        refine Nat.pow_le_pow_right (by decide) ?_
        split
        · omega
        · split <;> omega
      have h8 : (2 : Nat) ^ 3 = 8 := rfl
      omega

/-- The sum of a run of one code length. -/
private theorem lengthSum_replicate (n l : Nat) : lengthSum (List.replicate n l) = n * (if l = 0 then 0 else 32768 >>> l) := by
  simp only [lengthSum, List.map_replicate, List.sum_replicate_nat]

/-- From a state's lengths to the list `tableDone` needs. -/
theorem lens_full {t : ByteArray} {A : List Nat} {size : Nat} (hs : t.size = size) (hle : A.length ≤ size)
    (h1 : ∀ i, i < A.length → A[i]? = some (t.data[i]?.getD 0).toNat) (h2 : ∀ i, A.length ≤ i → t.data[i]?.getD 0 = 0) :
    lensOf t size = A ++ List.replicate (size - A.length) 0 := by
  have hl : (lensOf t size).length = size := length_lensOf (by omega)
  apply List.ext_getElem?
  intro i
  by_cases hi : i < size
  · rw [lensOf_get hi (by omega)]
    by_cases hA : i < A.length
    · rw [List.getElem?_append_left hA, h1 i hA]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), h2 i (by omega)]
      rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by
      simp only [List.length_append, List.length_replicate]
      omega)]

section
variable {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray} {stop : USize}

theorem stepHSyms_ok {o : Owner} {size : Nat} {clc : PrefixCode} {ls : LengthState} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.syms o size clc ls)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.syms o size clc ls) st pos (stepHSyms st pos) := by
  obtain ⟨hw, hu, ht, hs, ho, hy⟩ := hrel
  have hrel : HRel st g (.syms o size clc ls) := ⟨hw, hu, ht, hs, ho, hy⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hs : SizeOk st size := ⟨hs1, hs2, hs3⟩
  have hlenLe := hy.le
  unfold stepHSyms
  by_cases h0 : st.symSum = 32768
  · rw [ite_eq_left h0]
    have hsum : lengthSum ls.lens = 32768 := by
      rw [← hy.sumOk, h0]
      rfl
    have hfullL := lens_full hy.sz hlenLe hy.at_ hy.zero
    have hC : Complete (.canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0)) := by
      refine ⟨?_, ?_⟩
      · intro l hl
        rcases List.mem_append.mp hl with h | h
        · exact hy.small l h
        · rw [(List.mem_replicate.mp h).2]
          omega
      · rw [lengthSum_append, lengthSum_replicate_zero, hsum]
    have hsy : (PrefixCode.canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0)).Symbols size := by
      show (ls.lens ++ List.replicate (size - ls.lens.length) 0).length = size
      simp
      omega
    have hdone := tableDone_ok K (st := { st with pos := pos, status := .next }) (c := .canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0))
      (single := false) (sym := 0) hw hu hs ho rfl (fun e => Bool.noConfusion e) (fun _ => by rw [← hfullL]) hy.sz hC hsy
    exact hdone.toStep rfl hp rfl (fun F => hrest_syms_done K g o size clc ls _ hlenLe hsum)
  rw [ite_eq_right h0]
  have hsumNe : lengthSum ls.lens ≠ 32768 := by
    rw [← hy.sumOk]
    exact fun e => h0 (UInt64.toNat_inj.mp e)
  by_cases h1 : st.ln = st.size
  · rw [ite_eq_left h1]
    have hlen : ls.lens.length = size := by
      rw [← hy.ln, h1, hs1]
    exact HStepOk.ofBad rfl (fun F => hrest_syms_full K g o size clc ls _ hlen hsumNe)
  rw [ite_eq_right h1]
  have hlenLt : ls.lens.length < size := by
    have : ls.lens.length ≠ size := by
      rw [← hy.ln, ← hs1]
      exact fun e => h1 (UInt64.toNat_inj.mp e)
    omega
  have R := lenSymFast_ok (t := st.clt.t) (base := USize.ofNat 0) (hfit := st.clt.fits) (h32 := st.clt.h32) hw hy.table hy.complete
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.syms o size clc ls)) (N := fun v b =>
    if size < (applyCodeLength ls v.1 v.2).lens.length then none
    else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then none
    else hrest K g (.syms o size clc (applyCodeLength ls v.1 v.2)) b) (fun bs => hrest_syms_step K g o size clc ls bs hlenLt hsumNe)
  have hval := R.ok
  dsimp only
  generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    exact HStepOk.ofShortRead (X := 18) hrel hfull (by omega) h3 h4
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨hs18, he8⟩ := lenSym_bounds hy.symbols ((hval hsr).2 [])
    have hsize32 : size < 2 ^ 32 := by omega
    have hln : st.ln.toNat = ls.lens.length := hy.ln
    by_cases hlow : r.a < 16
    · rw [ite_eq_left hlow]
      have hlow' : r.a.toNat < 16 := UInt64.lt_iff_toNat_lt.mp hlow
      have happly : applyCodeLength ls r.a.toNat r.b.toNat = ⟨ls.lens ++ [r.a.toNat], if r.a.toNat = 0 then ls.prev else r.a.toNat, none⟩ := by
        simp [applyCodeLength, hlow']
      have hsumP : lengthSum (ls.lens ++ [r.a.toNat]) = lengthSum ls.lens + (if r.a.toNat = 0 then 0 else 32768 >>> r.a.toNat) := by
        rw [lengthSum_append]
        simp [lengthSum]
      have hshLe : 32768 >>> r.a.toNat ≤ 32768 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_le_self _ _
      have hsumU : (if r.a = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> r.a)).toNat = lengthSum (ls.lens ++ [r.a.toNat]) := by
        rw [hsumP, ← hy.sumOk]
        by_cases hz : r.a = 0
        · have hz' : r.a.toNat = 0 := by rw [hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz']
          rfl
        · have hz' : ¬ r.a.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
          rw [ite_eq_right hz, ite_eq_right hz', UInt64.toNat_add, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega)]
          have hsl := hy.sumOk
          have hsl2 := hy.sumLe
          exact Nat.mod_eq_of_lt (by
            show st.symSum.toNat + 32768 >>> r.a.toNat < _
            omega)
      generalize (if r.a = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> r.a)) = sum at hsumU ⊢
      have hlt1 : ¬ size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
        rw [happly]
        simp
        omega
      by_cases hbig : 32768 < sum
      · rw [ite_eq_left hbig]
        have hbig' : 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly, ← hsumU]
          exact UInt64.lt_iff_toNat_lt.mp hbig
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hlt1, hbig', ↓reduceIte]
      · rw [ite_eq_right hbig]
        have hbig' : ¬ 32768 < lengthSum (ls.lens ++ [r.a.toNat]) := by
          rw [← hsumU]
          exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
        have hbig2 : ¬ 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          exact hbig'
        have hln1 : (st.ln + 1).toNat = ls.lens.length + 1 := by
          rw [UInt64.toNat_add, hln, show (1 : UInt64).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hus : st.ln.toUSize.toNat = ls.lens.length := by rw [word_toUSize (by omega), hln]
        have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
          rw [UInt64.toNat_toUInt8]
          omega
        have hnew : SymRel { clearLens st with
            word := r.word, count := r.count, pos := pos, status := .next, lens := setLen st.lens st.ln r.a, ln := st.ln + 1
            prevLen := if r.a = 0 then st.prevLen else r.a, repCount := 0, symSum := sum } size clc (applyCodeLength ls r.a.toNat r.b.toNat) := by
          rw [happly]
          exact {
            table := hy.table
            complete := hy.complete
            symbols := hy.symbols
            sz := by
              show (setU st.lens _ _).size = size
              rw [size_setU]
              exact hy.sz
            ln := by
              show (st.ln + 1).toNat = _
              rw [hln1]
              simp
            le := by
              simp
              omega
            at_ := by
              intro i hi
              simp only [List.length_append, List.length_singleton] at hi
              show _ = some ((setU st.lens st.ln.toUSize r.a.toUInt8).data[i]?.getD 0).toNat
              by_cases he : i = ls.lens.length
              · subst he
                have := setU_get_same (t := st.lens) (i := st.ln.toUSize) (v := r.a.toUInt8) (by rw [hus, hy.sz]; omega)
                rw [hus] at this
                rw [this, hbyte]
                simp
              · have hne : i < ls.lens.length := by omega
                rw [List.getElem?_append_left hne, hy.at_ i hne, setU_get_ne (by rw [hus]; exact he)]
            zero := by
              intro i hi
              simp only [List.length_append, List.length_singleton] at hi
              show ((setU st.lens st.ln.toUSize r.a.toUInt8).data[i]?.getD 0) = 0
              rw [setU_get_ne (by rw [hus]; omega)]
              exact hy.zero i (by omega)
            small := by
              intro l hl
              rcases List.mem_append.mp hl with h | h
              · exact hy.small l h
              · rw [List.mem_singleton.mp h]
                omega
            prev := by
              show (if r.a = 0 then st.prevLen else r.a).toNat = _
              by_cases hz : r.a = 0
              · have hz' : r.a.toNat = 0 := by rw [hz]; rfl
                rw [ite_eq_left hz, ite_eq_left hz']
                exact hy.prev
              · have hz' : ¬ r.a.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
                rw [ite_eq_right hz, ite_eq_right hz']
            prevOk := by
              have := hy.prevOk
              show 1 ≤ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ∧ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ≤ 15
              split <;> omega
            rep := rfl
            sumOk := hsumU
            sumLe := Nat.le_of_not_lt hbig' }
        have hgrow : size + 1 - (applyCodeLength ls r.a.toNat r.b.toNat).lens.length < size + 1 - ls.lens.length := by
          rw [happly]
          simp only [List.length_append, List.length_singleton]
          omega
        refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
          (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hgrow⟩⟩) rfl
          ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hlt1, hbig2, ↓reduceIte]
        rfl
    · rw [ite_eq_right hlow]
      have hhigh : ¬ r.a.toNat < 16 := fun h => hlow (UInt64.lt_iff_toNat_lt.mpr h)
      have hprevOk := hy.prevOk
      generalize hL : (if r.a.toNat = 16 then ls.prev else 0) = Ln
      generalize hM : (if r.a.toNat = 16 then 4 else 8) = Mn
      generalize hO : (match ls.rep with
        | some (s, count) => if s = r.a.toNat then count else 0
        | none => 0) = On
      have hLU : (if r.a = 16 then st.prevLen else 0).toNat = Ln := by
        rw [← hL]
        by_cases h16 : r.a = 16
        · rw [ite_eq_left h16, ite_eq_left (show r.a.toNat = 16 by rw [h16]; rfl)]
          exact hy.prev
        · rw [ite_eq_right h16, ite_eq_right (show ¬ r.a.toNat = 16 from fun e => h16 (UInt64.toNat_inj.mp e))]
          rfl
      have hMU : (if r.a = 16 then (4 : UInt64) else 8).toNat = Mn := by
        rw [← hM]
        by_cases h16 : r.a = 16
        · rw [ite_eq_left h16, ite_eq_left (show r.a.toNat = 16 by rw [h16]; rfl)]
          rfl
        · rw [ite_eq_right h16, ite_eq_right (show ¬ r.a.toNat = 16 from fun e => h16 (UInt64.toNat_inj.mp e))]
          rfl
      have hMc : Mn = 4 ∨ Mn = 8 := by
        rw [← hM]
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hLle : Ln ≤ 15 := by
        rw [← hL]
        split <;> omega
      have hOU : (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0).toNat = On ∧ On ≤ ls.lens.length ∧ (On = 0 ∨ 3 ≤ On) := by
        have hr := hy.rep
        rw [← hO]
        cases hrep : ls.rep with
        | none =>
          rw [hrep] at hr
          have hz : st.repCount = 0 := UInt64.toNat_inj.mp hr
          rw [ite_eq_right (fun h => h.1 hz)]
          exact ⟨rfl, Nat.zero_le _, Or.inl rfl⟩
        | some q =>
          obtain ⟨t, c⟩ := q
          rw [hrep] at hr
          obtain ⟨h1', h2', h3', h4'⟩ := hr
          show _ = (if t = r.a.toNat then c else 0) ∧ (if t = r.a.toNat then c else 0) ≤ _ ∧ ((if t = r.a.toNat then c else 0) = 0 ∨ 3 ≤ (if t = r.a.toNat then c else 0))
          by_cases he : t = r.a.toNat
          · have hne : st.repCount ≠ 0 := by
              intro e
              rw [e] at h2'
              have h00 : (0 : UInt64).toNat = 0 := rfl
              omega
            have hc1 : st.repCount ≠ 0 ∧ st.repSym = r.a := ⟨hne, UInt64.toNat_inj.mp (by rw [h1', he])⟩
            rw [ite_eq_left hc1, ite_eq_left he]
            exact ⟨h2', h4', Or.inr h3'⟩
          · have hc1 : ¬ (st.repCount ≠ 0 ∧ st.repSym = r.a) := fun h => he (by rw [← h1', h.2])
            rw [ite_eq_right hc1, ite_eq_right he]
            exact ⟨rfl, Nat.zero_le _, Or.inl rfl⟩
      obtain ⟨hOu, hOle, hO3⟩ := hOU
      generalize hNn : (if On = 0 then 3 + r.b.toNat else Mn * (On - 2) + (3 + r.b.toNat)) = Nn
      have hgrow : On < Nn ∧ Nn ≤ 8 * 704 + 10 ∧ 3 ≤ Nn := by
        rw [← hNn]
        rcases hO3 with h | h
        · rw [ite_eq_left h]
          omega
        · rw [ite_eq_right (by omega)]
          rcases hMc with hm | hm <;> rw [hm] <;> omega
      have happly : applyCodeLength ls r.a.toNat r.b.toNat = ⟨ls.lens ++ List.replicate (Nn - On) Ln, ls.prev, some (r.a.toNat, Nn)⟩ := by
        subst hL hM hO hNn
        simp only [applyCodeLength, hhigh, ↓reduceIte]
        rfl
      have hNU : (if (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = 0 then 3 + r.b
          else (if r.a = 16 then (4 : UInt64) else 8) * ((if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) - 2) + (3 + r.b)).toNat = Nn := by
        generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hOu
        generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hMU
        rw [← hNn]
        have h3b : (3 + r.b).toNat = 3 + r.b.toNat := by
          rw [UInt64.toNat_add, show (3 : UInt64).toNat = 3 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        by_cases hz : old = 0
        · have hz' : On = 0 := by rw [← hOu, hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz', h3b]
        · have hz' : ¬ On = 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [hOu, e]; rfl))
          have h3O : 3 ≤ On := by omega
          rw [ite_eq_right hz, ite_eq_right hz']
          have hsub : (old - 2).toNat = On - 2 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hOu, show (2 : UInt64).toNat = 2 from rfl]; omega)), hOu]
            rfl
          have hmul : (mult * (old - 2)).toNat = Mn * (On - 2) := by
            rw [UInt64.toNat_mul, hMU, hsub]
            refine Nat.mod_eq_of_lt ?_
            rcases hMc with hm | hm <;> rw [hm] <;> omega
          rw [UInt64.toNat_add, hmul, h3b]
          refine Nat.mod_eq_of_lt ?_
          rcases hMc with hm | hm <;> rw [hm] <;> omega
      generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hOu hNU ⊢
      generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hNU ⊢
      generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at hNU ⊢
      have hdU : (new - old).toNat = Nn - On := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hNU, hOu]
      have hln2 : (st.ln + (new - old)).toNat = ls.lens.length + (Nn - On) := by
        rw [UInt64.toNat_add, hln, hdU]
        exact Nat.mod_eq_of_lt (by omega)
      have hlen2 : (ls.lens ++ List.replicate (Nn - On) Ln).length = ls.lens.length + (Nn - On) := by simp
      by_cases hover : st.size < st.ln + (new - old)
      · rw [ite_eq_left hover]
        have hover' : size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
          rw [happly]
          show size < (ls.lens ++ List.replicate (Nn - On) Ln).length
          rw [hlen2, ← hln2, ← hs1]
          exact UInt64.lt_iff_toNat_lt.mp hover
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hover', ↓reduceIte]
      rw [ite_eq_right hover]
      have hover' : ¬ size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
        rw [happly]
        show ¬ size < (ls.lens ++ List.replicate (Nn - On) Ln).length
        rw [hlen2, ← hln2, ← hs1]
        exact fun e => hover (UInt64.lt_iff_toNat_lt.mpr e)
      have hroom : ls.lens.length + (Nn - On) ≤ size := by
        rw [happly] at hover'
        have : ¬ size < (ls.lens ++ List.replicate (Nn - On) Ln).length := hover'
        rw [hlen2] at this
        omega
      have hsumP : lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) = lengthSum ls.lens + (Nn - On) * (if Ln = 0 then 0 else 32768 >>> Ln) := by
        rw [lengthSum_append, lengthSum_replicate]
      have hsumU : (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
          else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))).toNat =
          lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) := by
        generalize (if r.a = 16 then st.prevLen else 0) = lenU at hLU
        rw [hsumP, ← hy.sumOk]
        by_cases hz : lenU = 0
        · have hz' : Ln = 0 := by rw [← hLU, hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz']
          simp
        · have hz' : ¬ Ln = 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [hLU, e]; rfl))
          rw [ite_eq_right hz, ite_eq_right hz']
          have hsh : ((32768 : UInt64) >>> lenU).toNat = 32768 >>> Ln := by
            rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show lenU.toNat < 64 by omega), hLU]
            rfl
          have hshLe : 32768 >>> Ln ≤ 32768 := by
            rw [Nat.shiftRight_eq_div_pow]
            exact Nat.div_le_self _ _
          have hprod : (Nn - On) * (32768 >>> Ln) ≤ 704 * 32768 := Nat.mul_le_mul (by omega) hshLe
          have hmul : ((new - old) * ((32768 : UInt64) >>> lenU)).toNat = (Nn - On) * (32768 >>> Ln) := by
            rw [UInt64.toNat_mul, hdU, hsh]
            exact Nat.mod_eq_of_lt (by omega)
          have hsl := hy.sumOk
          have hsl2 := hy.sumLe
          rw [UInt64.toNat_add, hmul]
          exact Nat.mod_eq_of_lt (by omega)
      generalize hlenU : (if r.a = 16 then st.prevLen else 0) = lenU at hLU hsumU ⊢
      generalize (if lenU = 0 then st.symSum else st.symSum + (new - old) * ((32768 : UInt64) >>> lenU)) = sum at hsumU ⊢
      by_cases hbig : 32768 < sum
      · rw [ite_eq_left hbig]
        have hbig' : 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          show 32768 < lengthSum (ls.lens ++ List.replicate (Nn - On) Ln)
          rw [← hsumU]
          exact UInt64.lt_iff_toNat_lt.mp hbig
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hover', hbig', ↓reduceIte]
      · rw [ite_eq_right hbig]
        have hbigN : ¬ 32768 < lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) := by
          rw [← hsumU]
          exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
        have hbig' : ¬ 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          exact hbigN
        obtain ⟨fz, fg⟩ := fillLens_spec lenU.toUInt8 (Nn - On) st.lens st.ln (new - old) hdU (by rw [hln]; omega) (by rw [hln, hy.sz]; exact hroom)
        have hbyte : lenU.toUInt8.toNat = Ln := by
          rw [UInt64.toNat_toUInt8, hLU]
          omega
        have hnew : SymRel { clearLens st with
            word := r.word, count := r.count, pos := pos, status := .next, lens := fillLens st.lens st.ln (new - old) lenU.toUInt8, ln := st.ln + (new - old)
            repSym := r.a, repCount := new, symSum := sum } size clc (applyCodeLength ls r.a.toNat r.b.toNat) := by
          rw [happly]
          exact {
            table := hy.table
            complete := hy.complete
            symbols := hy.symbols
            sz := by
              show (fillLens st.lens st.ln (new - old) lenU.toUInt8).size = size
              rw [fz]
              exact hy.sz
            ln := by
              show (st.ln + (new - old)).toNat = _
              rw [hln2, hlen2]
            le := by
              show (ls.lens ++ List.replicate (Nn - On) Ln).length ≤ size
              rw [hlen2]
              exact hroom
            at_ := by
              intro i hi
              show (ls.lens ++ List.replicate (Nn - On) Ln)[i]? = some ((fillLens st.lens st.ln (new - old) lenU.toUInt8).data[i]?.getD 0).toNat
              have hi' : i < ls.lens.length + (Nn - On) := by
                have h : i < (ls.lens ++ List.replicate (Nn - On) Ln).length := hi
                rwa [hlen2] at h
              rw [fg i, hln]
              by_cases hA : i < ls.lens.length
              · rw [List.getElem?_append_left hA, ite_eq_right (by omega), hy.at_ i hA]
              · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), ite_eq_left (by omega), hbyte]
            zero := by
              intro i hi
              have hi' : ls.lens.length + (Nn - On) ≤ i := by
                have h : (ls.lens ++ List.replicate (Nn - On) Ln).length ≤ i := hi
                rwa [hlen2] at h
              show (fillLens st.lens st.ln (new - old) lenU.toUInt8).data[i]?.getD 0 = 0
              rw [fg i, hln, ite_eq_right (by omega)]
              exact hy.zero i (by omega)
            small := by
              intro l hl
              rcases List.mem_append.mp hl with h | h
              · exact hy.small l h
              · rw [(List.mem_replicate.mp h).2]
                exact hLle
            prev := hy.prev
            prevOk := hy.prevOk
            rep := ⟨rfl, hNU, hgrow.2.2, by
              show Nn ≤ (ls.lens ++ List.replicate (Nn - On) Ln).length
              rw [hlen2]
              omega⟩
            sumOk := hsumU
            sumLe := Nat.le_of_not_lt hbigN }
        have hshorter : size + 1 - (applyCodeLength ls r.a.toNat r.b.toNat).lens.length < size + 1 - ls.lens.length := by
          rw [happly]
          simp only [List.length_append, List.length_replicate]
          omega
        refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
          (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hshorter⟩⟩) rfl
          ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hover', hbig', ↓reduceIte]
        rfl

end

end Brotli.Decoder
