import Brotli.Decoder.HeaderSyms

/-!
# A context map's values

The place reading a context map's values, and the place at its last bit, with the inverse move-to-front transform and the
check that every tree occurs.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

section
variable {α : Type} (K : MetaBlockHeader → List Bool → Option α)

/-- With no values left, the last bit is next. -/
theorem hrest_vals_zero (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (bs : List Bool) :
    hrest K g (.vals isL ntrees rlemax code done 0) bs = hrest K g (.imtf isL ntrees done) bs := by
  show (valsFrom rlemax code 0 bs >>= _) = _
  rw [valsFrom_zero]
  show afterVals K g isL ntrees (done ++ []) bs = _
  rw [List.append_nil]
  rfl

/-- One more symbol of the values. -/
theorem hrest_vals_step (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (left : Nat) (bs : List Bool)
    (h0 : left ≠ 0) : hrest K g (.vals isL ntrees rlemax code done left) bs = mapSym rlemax code bs >>= fun p =>
      if left < p.1.2 then none
      else hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate p.1.2 p.1.1) (left - p.1.2)) p.2 := by
  show (valsFrom rlemax code left bs >>= _) = _
  rw [valsFrom_step bs h0]
  cases mapSym rlemax code bs with
  | none => rfl
  | some p =>
    show ((if left < p.1.2 then none else (valsFrom rlemax code (left - p.1.2) p.2 >>= fun q => some (List.replicate p.1.2 p.1.1 ++ q.1, q.2))) >>= _) =
      (if left < p.1.2 then none else valsFrom rlemax code (left - p.1.2) p.2 >>= _)
    by_cases h1 : left < p.1.2
    · rw [ite_eq_left h1, ite_eq_left h1]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      cases valsFrom rlemax code (left - p.1.2) p.2 with
      | none => rfl
      | some q =>
        show afterVals K g isL ntrees (done ++ (List.replicate p.1.2 p.1.1 ++ q.1)) q.2 =
          afterVals K g isL ntrees (done ++ List.replicate p.1.2 p.1.1 ++ q.1) q.2
        rw [List.append_assoc]

end

private theorem mapSym_bounds {rlemax ntrees : Nat} {code : PrefixCode} {bs r : List Bool} {v run : Nat}
    (hn : 0 < ntrees) (hr : rlemax ≤ 16) (hs : code.Symbols (contextMapAlphabetSize ntrees rlemax))
    (h : mapSym rlemax code bs = some ((v, run), r)) : v < ntrees ∧ 1 ≤ run ∧ (v ≠ 0 → run = 1) ∧ run < 2 ^ 18 := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, b1⟩ := p
    rw [hd] at h
    have hlt : sym < ntrees + rlemax := decodeSymbol_lt hs hd
    change (match contextMapValue rlemax sym with
      | some v => some ((v, 1), b1)
      | none => readInt sym b1 >>= fun q => some ((0, (1 <<< sym) + q.1), q.2)) = _ at h
    cases hv : contextMapValue rlemax sym with
    | some x =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, _⟩ := h
      refine ⟨?_, by omega, fun _ => rfl, by decide⟩
      unfold contextMapValue at hv
      split at hv
      · simp only [Option.some.injEq] at hv
        omega
      · split at hv
        · cases hv
        · simp only [Option.some.injEq] at hv
          omega
    | none =>
      rw [hv] at h
      cases hx : readInt sym b1 with
      | none => rw [hx] at h; cases h
      | some q =>
        obtain ⟨e, b2⟩ := q
        rw [hx] at h
        have h' : some ((0, (1 <<< sym) + e), b2) = some ((v, run), r) := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨⟨rfl, rfl⟩, _⟩ := h'
        have hsym : sym ≤ 16 := by
          unfold contextMapValue at hv
          split at hv
          · cases hv
          · split at hv
            · omega
            · cases hv
        have he := readInt_lt _ _ _ _ hx
        have hp : 2 ^ sym ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hsym
        have h216 : (2 : Nat) ^ 16 = 65536 := rfl
        have hpos : 0 < 2 ^ sym := Nat.two_pow_pos _
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        refine ⟨hn, by omega, fun e => absurd rfl e, by have : (2 : Nat) ^ 18 = 262144 := rfl; omega⟩

/-- The place reading a context map's values. -/
def stepHVals (st : Hd) (pos : USize) : Hd :=
  let left := st.left
  if left = 0 then { st with pos := pos, status := .next, tag := .imtf }
  else
    let r := mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      let v := r.a
      let run := r.b
      let idx := st.idx
      if left < run then markH st pos .bad
      else if v = 0 then { st with word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run }
      else
        let fill := st.fill
        let st0 := clearFill st
        { st0 with
          word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
          fill := setU fill idx.toUSize v.toUInt8 }

section
variable {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray} {stop : USize}

theorem stepHVals_ok {isL : Bool} {ntrees rlemax : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.vals isL ntrees rlemax code done left)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.vals isL ntrees rlemax code done left) st pos (stepHVals st pos) := by
  obtain ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero⟩ := hrel
  have hrel : HRel st g (.vals isL ntrees rlemax code done left) := ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero⟩
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  unfold stepHVals
  dsimp only
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    have hl0 : left = 0 := by
      rw [← hleft, h0]
      rfl
    subst hl0
    refine HStepOk.ofNext (g' := g) (p' := .imtf isL ntrees done) rfl ⟨hw, hu, rfl, hi, hn, h2, h256, ⟨hsz, by omega, fun i hi' => hat i (by omega), hlt⟩⟩
      (Nat.le_refl _) hp (fun F => hrest_vals_zero K g isL ntrees rlemax code done _)
  rw [ite_eq_right h0]
  have hl0 : left ≠ 0 := by
    rw [← hleft]
    exact fun e => h0 (UInt64.toNat_inj.mp e)
  have R := mapSymFast_ok (t := st.mapT.t) (base := USize.ofNat 0) (hfit := st.mapT.fits) (h32 := st.mapT.h32) (rlemax := st.rlemax) hw hok hC (by omega)
  rw [hr] at R
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.vals isL ntrees rlemax code done left)) (N := fun v b =>
    if left < v.2 then none else hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate v.2 v.1) (left - v.2)) b)
    (fun bs => hrest_vals_step K g isL ntrees rlemax code done left bs hl0)
  have hval := R.ok
  generalize mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    exact HStepOk.ofShortRead (X := 31) hrel hfull (by omega) h3 h4
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨hv, hr1, hv1, hrlt⟩ := mapSym_bounds (by omega) h16 hsy ((hval hsr).2 [])
    by_cases hbig : st.left < r.b
    · rw [ite_eq_left hbig]
      have hbig' : left < r.b.toNat := by
        rw [← hleft]
        exact UInt64.lt_iff_toNat_lt.mp hbig
      refine HStepOk.ofBad rfl (fun F => ?_)
      rw [avail_mk, hN]
      simp only [hbig', ↓reduceIte]
    rw [ite_eq_right hbig]
    have hbig' : ¬ left < r.b.toNat := by
      rw [← hleft]
      exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
    have hidx2 : (st.idx + r.b).toNat = done.length + r.b.toNat := by
      rw [UInt64.toNat_add, hidx]
      exact Nat.mod_eq_of_lt (by omega)
    have hleft2 : (st.left - r.b).toNat = left - r.b.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hleft]; omega)), hleft]
    have hlen2 : (done ++ List.replicate r.b.toNat r.a.toNat).length = done.length + r.b.toNat := by simp
    by_cases hz : r.a = 0
    · rw [ite_eq_left hz]
      have hz' : r.a.toNat = 0 := by rw [hz]; rfl
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat)) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, hsz, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_)
      · show (st.idx + r.b).toNat = _
        rw [hidx2, hlen2]
      · rw [hlen2]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hlt x h
        · rw [(List.mem_replicate.mp h).2]
          exact hv
      · intro i hi'
        rw [hlen2] at hi'
        by_cases hA : i < done.length
        · rw [List.getElem?_append_left hA, hat i hA]
        · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), hzero i (by omega), hz']
          rfl
      · intro i hi'
        rw [hlen2] at hi'
        exact hzero i (by omega)
      · rw [avail_mk, hN]
        simp only [hbig', ↓reduceIte]
        rfl
    · rw [ite_eq_right hz]
      have hz' : r.a.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp e)
      have hrun1 := hv1 hz'
      have hus : st.idx.toUSize.toNat = done.length := by rw [word_toUSize (by omega), hidx]
      have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
        rw [UInt64.toNat_toUInt8]
        omega
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat)) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, ?_, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_)
      · show (st.idx + r.b).toNat = _
        rw [hidx2, hlen2]
      · rw [hlen2]
        omega
      · show (setU st.fill st.idx.toUSize r.a.toUInt8).size = _
        rw [size_setU]
        exact hsz
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hlt x h
        · rw [(List.mem_replicate.mp h).2]
          exact hv
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show _ = some ((setU st.fill st.idx.toUSize r.a.toUInt8).data[i]?.getD 0).toNat
        by_cases hA : i < done.length
        · rw [List.getElem?_append_left hA, hat i hA, setU_get_ne (by rw [hus]; omega)]
        · have he : i = done.length := by omega
          subst he
          have := setU_get_same (t := st.fill) (i := st.idx.toUSize) (v := r.a.toUInt8) (by rw [hus, hsz]; omega)
          rw [hus] at this
          rw [this, hbyte, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_replicate, ite_eq_left (by omega)]
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show (setU st.fill st.idx.toUSize r.a.toUInt8).data[i]?.getD 0 = 0
        rw [setU_get_ne (by rw [hus]; omega)]
        exact hzero i (by omega)
      · rw [avail_mk, hN]
        simp only [hbig', ↓reduceIte]
        rfl

end

/-! ### The inverse move-to-front transform -/

/-- The transform's first list. -/
def mtfInitLut : ByteArray := ((List.range 256).map Nat.toUInt8).toByteArray

/-- A move-to-front list in an array. -/
structure MtfIs (m : ByteArray) (L : List Nat) : Prop where
  sz : m.size = 256
  length : L.length = 256
  at_ : ∀ k, k < 256 → L.getD k 0 = (m.data[k]?.getD 0).toNat

private theorem mtfInit_values : ∀ k, k < 256 → (List.range 256).getD k 0 = (((List.range 256).map Nat.toUInt8)[k]?.getD 0).toNat := by
  decide +kernel

theorem mtfInit_is : MtfIs mtfInitLut (List.range 256) := by
  refine ⟨by simp [mtfInitLut, List.size_toByteArray], by simp, fun k hk => ?_⟩
  rw [mtfInit_values k hk]
  simp only [mtfInitLut, List.data_toByteArray, List.getElem?_toArray]

/-- Moves the first `j` values up one place. -/
def shiftUp (m : ByteArray) (j : UInt64) : ByteArray :=
  if _hj : j = 0 then m else shiftUp (setU m j.toUSize (getU m (j - 1).toUSize)) (j - 1)
termination_by j.toNat
decreasing_by
  have hne : j.toNat ≠ 0 := fun e => _hj (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (j - 1).toNat = j.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem shiftUp_spec : ∀ (N : Nat) (m : ByteArray) (j : UInt64), j.toNat = N → N < 256 → m.size = 256 →
    (shiftUp m j).size = 256 ∧ ∀ k, k < 256 → (shiftUp m j).data[k]?.getD 0 =
      if 1 ≤ k ∧ k ≤ N then m.data[k - 1]?.getD 0 else m.data[k]?.getD 0 := by
  intro N
  induction N with
  | zero =>
    intro m j hj _ hs
    have hz : j = 0 := UInt64.toNat_inj.mp (by rw [hj]; rfl)
    rw [shiftUp, dite_eq_left hz]
    refine ⟨hs, fun k _ => ?_⟩
    rw [ite_eq_right (by omega)]
  | succ N ih =>
    intro m j hj hN hs
    have hz : j ≠ 0 := fun e => by rw [e] at hj; exact Nat.succ_ne_zero _ hj.symm
    have h1 : (j - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hj]
      rfl
    have hus : j.toUSize.toNat = N + 1 := by rw [word_toUSize (by omega), hj]
    have hus1 : (j - 1).toUSize.toNat = N := by rw [word_toUSize (by omega), h1]
    rw [shiftUp, dite_eq_right hz]
    generalize hv : getU m (j - 1).toUSize = v
    have hvb : v = m.data[N]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, hus1]
    obtain ⟨i1, i2⟩ := ih (setU m j.toUSize v) (j - 1) h1 (by omega) (by rw [size_setU]; exact hs)
    refine ⟨i1, fun k hk => ?_⟩
    rw [i2 k hk]
    by_cases he : k = N + 1
    · subst he
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have := setU_get_same (t := m) (i := j.toUSize) (v := v) (by rw [hus, hs]; omega)
      rw [hus] at this
      rw [this, hvb]
      rfl
    · by_cases hin : 1 ≤ k ∧ k ≤ N
      · rw [ite_eq_left hin, ite_eq_left (by omega), setU_get_ne (by rw [hus]; omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega), setU_get_ne (by rw [hus]; exact he)]

/-- The transform's loop: each index's value moves to the front. -/
def imtfLoop (m out : ByteArray) (i n : UInt64) : ByteArray :=
  if _hn : n = 0 then out
  else
    let index := (getU out i.toUSize).toUInt64
    let value := getU m index.toUSize
    imtfLoop (setU (shiftUp m index) (USize.ofNat 0) value) (setU out i.toUSize value) (i + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

private theorem mtf_step {m : ByteArray} {L : List Nat} (h : MtfIs m L) {index : UInt64} (hi : index.toNat < 256) :
    MtfIs (setU (shiftUp m index) (USize.ofNat 0) (getU m index.toUSize)) (L.getD index.toNat 0 :: L.eraseIdx index.toNat) ∧
      (getU m index.toUSize).toNat = L.getD index.toNat 0 := by
  obtain ⟨s1, s2⟩ := shiftUp_spec _ m index rfl hi h.sz
  have hus : index.toUSize.toNat = index.toNat := word_toUSize (by omega)
  have hv : (getU m index.toUSize).toNat = L.getD index.toNat 0 := by
    rw [getU_toNat, hus, h.at_ _ hi]
  have hz := usize_zero'
  refine ⟨⟨by rw [size_setU]; exact s1, ?_, fun k hk => ?_⟩, hv⟩
  · simp [List.length_eraseIdx, h.length, hi]
  · cases k with
    | zero =>
      have := setU_get_same (t := shiftUp m index) (i := USize.ofNat 0) (v := getU m index.toUSize) (by rw [hz, s1]; omega)
      rw [hz] at this
      rw [this, hv]
      rfl
    | succ q =>
      rw [setU_get_ne (by rw [hz]; omega), s2 _ hk]
      simp only [List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
      by_cases hq : q < index.toNat
      · rw [ite_eq_left hq, ite_eq_left (by omega), ← List.getD_eq_getElem?_getD, h.at_ q (by omega)]
        rfl
      · rw [ite_eq_right hq, ite_eq_right (by omega), ← List.getD_eq_getElem?_getD, h.at_ (q + 1) hk]

theorem imtfLoop_spec : ∀ (N : Nat) (i n : UInt64) (m out : ByteArray) (L vs pre : List Nat), vs.length = N → n.toNat = N → i.toNat = pre.length →
    pre.length + N < 2 ^ 32 → out.size = pre.length + N → MtfIs m L → (∀ j, j < pre.length → pre[j]? = some (out.data[j]?.getD 0).toNat) →
    (∀ j, j < N → vs[j]? = some (out.data[pre.length + j]?.getD 0).toNat) →
    (imtfLoop m out i n).size = pre.length + N ∧ ∀ j, j < pre.length + N →
      (pre ++ inverseMoveToFrontFrom L vs)[j]? = some ((imtfLoop m out i n).data[j]?.getD 0).toNat := by
  intro N
  induction N with
  | zero =>
    intro i n m out L vs pre hv hn _ _ hs _ hp _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    have hnil : vs = [] := List.length_eq_zero_iff.mp hv
    subst hnil
    rw [imtfLoop, dite_eq_left hz]
    refine ⟨hs, fun j hj => ?_⟩
    simp only [inverseMoveToFrontFrom, List.append_nil]
    exact hp j (by omega)
  | succ N ih =>
    intro i n m out L vs pre hv hn hi h32 hs hm hp hq
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    cases vs with
    | nil => simp at hv
    | cons idx rest =>
      simp only [List.length_cons] at hv
      have hn1 : (n - 1).toNat = N := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
        rfl
      have hi1 : (i + 1).toNat = pre.length + 1 := by
        rw [UInt64.toNat_add, hi, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      have hus : i.toUSize.toNat = pre.length := by rw [word_toUSize (by omega), hi]
      have hidx : (getU out i.toUSize).toUInt64.toNat = idx := by
        have := hq 0 (by omega)
        rw [Nat.add_zero] at this
        simp only [List.getElem?_cons_zero, Option.some.injEq] at this
        rw [UInt8.toNat_toUInt64, getU_toNat, hus, this]
      have hidxLt : idx < 256 := by
        rw [← hidx]
        exact (getU out i.toUSize).toNat_lt
      rw [imtfLoop, dite_eq_right hz]
      dsimp only
      generalize hindex : (getU out i.toUSize).toUInt64 = index at hidx
      obtain ⟨ms, mv⟩ := mtf_step hm (index := index) (by omega)
      rw [hidx] at ms mv
      generalize hval : getU m index.toUSize = value at ms mv
      have hbyte : value.toNat = L.getD idx 0 := mv
      have hsz := size_setU out i.toUSize value
      have hget : (setU out i.toUSize value).data[pre.length]?.getD 0 = value := by
        have := setU_get_same (t := out) (i := i.toUSize) (v := value) (by rw [hus, hs]; omega)
        rwa [hus] at this
      have hlen' : (pre ++ [L.getD idx 0]).length = pre.length + 1 := by simp
      obtain ⟨r1, r2⟩ := ih (i + 1) (n - 1) _ (setU out i.toUSize value) _ rest (pre ++ [L.getD idx 0]) (by omega) hn1 (by rw [hi1, hlen']) (by rw [hlen']; omega)
        (by rw [hsz, hlen', hs]; omega) ms
        (by
          intro j hj
          rw [hlen'] at hj
          by_cases he : j = pre.length
          · subst he
            rw [hget, hbyte]
            simp
          · have hlt : j < pre.length := by omega
            rw [List.getElem?_append_left hlt, hp j hlt, setU_get_ne (by rw [hus]; exact he)])
        (by
          intro j hj
          rw [hlen', setU_get_ne (by rw [hus]; omega)]
          have := hq (j + 1) (by omega)
          rw [List.getElem?_cons_succ] at this
          rwa [show pre.length + (j + 1) = pre.length + 1 + j by omega] at this)
      rw [hlen'] at r1 r2
      refine ⟨by omega, fun j hj => ?_⟩
      have := r2 j (by omega)
      rw [List.append_assoc] at this
      exact this

/-! ### Every tree occurs -/

/-- Marks the values of `n` bytes from `i`. -/
def markAll (map flags : ByteArray) (i n : UInt64) : ByteArray :=
  if _hn : n = 0 then flags else markAll map (setU flags (getU map i.toUSize).toUInt64.toUSize 1) (i + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem markAll_spec (map : ByteArray) : ∀ (N : Nat) (flags : ByteArray) (i n : UInt64), n.toNat = N → i.toNat + N < 2 ^ 32 → flags.size = 256 →
    (markAll map flags i n).size = 256 ∧ ∀ t, t < 256 → ((markAll map flags i n).data[t]?.getD 0 ≠ 0 ↔
      (flags.data[t]?.getD 0 ≠ 0 ∨ ∃ j, i.toNat ≤ j ∧ j < i.toNat + N ∧ (map.data[j]?.getD 0).toNat = t)) := by
  intro N
  induction N with
  | zero =>
    intro flags i n hn _ hs
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [markAll, dite_eq_left hz]
    refine ⟨hs, fun t _ => ⟨Or.inl, ?_⟩⟩
    rintro (h | ⟨j, h1, h2, _⟩)
    · exact h
    · omega
  | succ N ih =>
    intro flags i n hn h32 hs
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    have hv : (getU map i.toUSize).toUInt64.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hus]
    have hvLt : (map.data[i.toNat]?.getD 0).toNat < 256 := (map.data[i.toNat]?.getD 0).toNat_lt
    have hvU : (getU map i.toUSize).toUInt64.toUSize.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [word_toUSize (by omega), hv]
    rw [markAll, dite_eq_right hz]
    generalize hf : setU flags (getU map i.toUSize).toUInt64.toUSize 1 = flags1
    have hs1 : flags1.size = 256 := by rw [← hf, size_setU]; exact hs
    obtain ⟨r1, r2⟩ := ih flags1 (i + 1) (n - 1) hn1 (by rw [hi1]; omega) hs1
    refine ⟨r1, fun t ht => ?_⟩
    rw [r2 t ht, hi1]
    have hflag : flags1.data[t]?.getD 0 ≠ 0 ↔ (flags.data[t]?.getD 0 ≠ 0 ∨ (map.data[i.toNat]?.getD 0).toNat = t) := by
      by_cases he : t = (map.data[i.toNat]?.getD 0).toNat
      · subst he
        have := setU_get_same (t := flags) (i := (getU map i.toUSize).toUInt64.toUSize) (v := 1) (by rw [hvU, hs]; exact hvLt)
        rw [hvU] at this
        rw [← hf, this]
        exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
      · rw [← hf, setU_get_ne (by rw [hvU]; exact he)]
        exact ⟨Or.inl, fun h => h.elim id (fun e => absurd e.symm he)⟩
    rw [hflag]
    constructor
    · rintro ((h | h) | ⟨j, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i.toNat, Nat.le_refl _, by omega, h⟩
      · exact Or.inr ⟨j, by omega, by omega, h3⟩
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact Or.inl (Or.inl h)
      · by_cases he : j = i.toNat
        · subst he
          exact Or.inl (Or.inr h3)
        · exact Or.inr ⟨j, by omega, by omega, h3⟩

/-- Checks `n` flags from `t`. -/
def allMarked (flags : ByteArray) (t n : UInt64) : Bool :=
  if _hn : n = 0 then true
  else if getU flags t.toUSize = 0 then false else allMarked flags (t + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem allMarked_iff (flags : ByteArray) : ∀ (N : Nat) (t n : UInt64), n.toNat = N → t.toNat + N < 2 ^ 32 →
    (allMarked flags t n = true ↔ ∀ k, t.toNat ≤ k → k < t.toNat + N → flags.data[k]?.getD 0 ≠ 0) := by
  intro N
  induction N with
  | zero =>
    intro t n hn _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [allMarked, dite_eq_left hz]
    exact ⟨fun _ k h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro t n hn h32
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (t + 1).toNat = t.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : t.toUSize.toNat = t.toNat := word_toUSize (by omega)
    have hget : getU flags t.toUSize = flags.data[t.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [getU_toNat, hus]
    rw [allMarked, dite_eq_right hz, hget]
    by_cases hc : flags.data[t.toNat]?.getD 0 = 0
    · rw [ite_eq_left hc]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd hc (h t.toNat (Nat.le_refl _) (by omega))⟩
    · rw [ite_eq_right hc, ih (t + 1) (n - 1) hn1 (by rw [hi1]; omega), hi1]
      constructor
      · intro h k h1 h2
        by_cases he : k = t.toNat
        · rw [he]
          exact hc
        · exact h k (by omega) (by omega)
      · intro h k h1 h2
        exact h k (by omega) (by omega)

/-- Checks that every value below `n` occurs in a map of `size` bytes. -/
def allOccur (map : ByteArray) (size n : UInt64) : Bool :=
  allMarked (markAll map (zeroBytes 256) 0 size) 0 n

theorem allOccur_iff {map : ByteArray} {l : List Nat} {size n : UInt64} (hs : size.toNat < 2 ^ 31) (hn : n.toNat ≤ 256)
    (hl : l.length = size.toNat) (hat : ∀ i, i < size.toNat → l[i]? = some (map.data[i]?.getD 0).toNat) :
    allOccur map size n = true ↔ (List.range n.toNat).all l.contains = true := by
  have hz : (0 : UInt64).toNat = 0 := rfl
  obtain ⟨_, m2⟩ := markAll_spec map _ (zeroBytes 256) 0 size rfl (by rw [hz]; omega) (zeroBytes_size (by decide))
  unfold allOccur
  rw [allMarked_iff _ _ 0 n rfl (by rw [hz]; omega), hz]
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem, Nat.zero_add]
  constructor
  · intro h t ht
    have := (m2 t (by omega)).mp (h t (Nat.zero_le _) ht)
    rcases this with h1 | ⟨j, _, h3, h4⟩
    · rw [zeroBytes_get (by decide)] at h1
      exact absurd rfl h1
    · have e := hat j (by omega)
      rw [h4] at e
      exact List.mem_of_getElem? e
  · intro h t _ ht
    refine (m2 t (by omega)).mpr (Or.inr ?_)
    obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp (h t ht)
    have e2 := hat j (by omega)
    rw [List.getElem?_eq_getElem hj, e] at e2
    exact ⟨j, by rw [hz]; omega, by rw [hz]; omega, (Option.some.inj e2).symm⟩

/-! ### A context map's last bit -/

/-- The place at a context map's last bit. -/
def stepHImtf (st : Hd) (pos : USize) : Hd :=
  if 1 ≤ st.count then
    let b : BitBuffer := ⟨st.word, st.count⟩
    let b1 := b.drop 1
    let n := st.ntrees
    let fill := st.fill
    let size := UInt64.ofNat fill.size
    let st0 := clearFill st
    let final := if b.peek 1 = 0 then fill else imtfLoop mtfInitLut fill 0 size
    if allOccur final size n then mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n final
    else { st0 with pos := pos, status := .bad }
  else markH st pos .needsInput

private theorem not_le_lt3 {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

section
variable {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray} {stop : USize}

theorem stepHImtf_ok {isL : Bool} {ntrees : Nat} {vals : List Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.imtf isL ntrees vals)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.imtf isL ntrees vals) st pos (stepHImtf st pos) := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩ := hrel
  have hrel : HRel st g (.imtf isL ntrees vals) := ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  unfold stepHImtf
  dsimp only
  by_cases h1 : 1 ≤ st.count
  · rw [ite_eq_left h1]
    have hread := fun f => read_int (b := ⟨st.word, st.count⟩) (k := 1) f (by decide) h1
    have hw1 := drop_wf' hw (k := 1) (by decide) h1
    generalize (BitBuffer.mk st.word st.count).drop 1 = b1 at hread hw1
    generalize hpk : (BitBuffer.mk st.word st.count).peek 1 = im at hread
    have hspec : ∀ f, hrest K g (.imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
        if (List.range ntrees).all (if im.toNat = 0 then vals else inverseMoveToFront vals).contains then
          afterMap K g isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals) (b1.held ++ f)
        else none := by
      intro f
      show (readInt 1 _ >>= _) = _
      rw [show readInt 1 ((BitBuffer.mk st.word st.count).held ++ f) = _ from hread f]
      rfl
    have hsz : (UInt64.ofNat st.fill.size).toNat = mapSize g isL := by
      rw [hm.sz]
      exact u64_lit (by omega)
    have hfinal : MapOk (if im = 0 then st.fill else imtfLoop mtfInitLut st.fill 0 (UInt64.ofNat st.fill.size))
        (if im.toNat = 0 then vals else inverseMoveToFront vals) (mapSize g isL) ntrees := by
      by_cases hz : im = 0
      · rw [ite_eq_left hz, ite_eq_left (show im.toNat = 0 by rw [hz]; rfl)]
        exact hm
      · rw [ite_eq_right hz, ite_eq_right (show ¬ im.toNat = 0 from fun e => hz (UInt64.toNat_inj.mp e))]
        obtain ⟨r1, r2⟩ := imtfLoop_spec _ 0 (UInt64.ofNat st.fill.size) mtfInitLut st.fill (List.range 256) vals [] hm.length hsz rfl
          (by simp; omega) (by simpa using hm.sz) mtfInit_is (fun j hj => absurd hj (by simp)) (fun j hj => by
            simpa using hm.at_ j hj)
        simp only [List.length_nil, Nat.zero_add, List.nil_append] at r1 r2
        exact ⟨r1, by rw [inverseMoveToFront, inverseMoveToFrontFrom_length]; exact hm.length, r2, inverseMoveToFront_lt hm.lt⟩
    generalize (if im = 0 then st.fill else imtfLoop mtfInitLut st.fill 0 (UInt64.ofNat st.fill.size)) = final at hfinal ⊢
    generalize (if im.toNat = 0 then vals else inverseMoveToFront vals) = cmap at hfinal hspec
    have hocc := allOccur_iff (map := final) (l := cmap) (size := UInt64.ofNat st.fill.size) (n := st.ntrees)
      (by rw [hsz]; omega) (by omega) (by rw [hsz]; exact hfinal.length) (by rw [hsz]; exact hfinal.at_)
    rw [hn] at hocc
    by_cases hc : allOccur final (UInt64.ofNat st.fill.size) st.ntrees = true
    · rw [ite_eq_left hc]
      have hrel2 := mapFinish_rel (st := { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next })
        (cmap := cmap) (ntrees := ntrees) (n := st.ntrees) (map := final) hw1 hi hu hfinal hn (by omega) h256
      obtain ⟨c1, c2, c3, c4⟩ := mapFinish_spec { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final
      generalize mapFinish { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final = r2 at hrel2 c1 c2 c3 c4 ⊢
      refine HStepOk.ofNext c4 hrel2 (by rw [c3]; exact Nat.le_refl _) (by rw [c3]; exact hp) (fun F => ?_)
      rw [avail_mk, hspec, ite_eq_left (hocc.mp hc), afterMap_eq, avail_mk, c1, c2, c3]
    · rw [ite_eq_right hc]
      have hc' : ¬ (List.range ntrees).all cmap.contains = true := fun e => hc (hocc.mpr e)
      refine HStepOk.ofBad rfl (fun F => ?_)
      rw [avail_mk, hspec, ite_eq_right hc']
  · rw [ite_eq_right h1]
    have hc : st.count.toNat < 1 := not_le_lt3 h1
    have hnone : hrest K g (.imtf isL ntrees vals) (BitBuffer.mk st.word st.count).held = none := by
      show (readInt 1 _ >>= _) = none
      rw [readInt_short (b := ⟨st.word, st.count⟩) hc]
      rfl
    exact HStepOk.ofShortRead (X := 1) hrel hfull (by omega) hc hnone

end

end Brotli.Decoder
