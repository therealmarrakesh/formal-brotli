import Brotli.Decoder.HeaderSyms

/-!
# A context map's values

The place reading a context map's values, and the place at its last bit, with the inverse move-to-front transform and the
check that every tree occurs.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

section
variable {α : Type} (K : HK α)

/-- With no values left, the last bit is next. -/
theorem hrest_vals_zero (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (bs : List Bool) :
    hrest K g (.vals isL ntrees rlemax code done 0) bs = hrest K g (.imtf isL ntrees done) bs := by
  show (valsFrom rlemax code 0 bs >>= _) = _
  rw [valsFrom_zero]
  show afterVals K g isL ntrees (done ++ []) bs = _
  rw [List.append_nil]
  rfl

/-- With a code that gives a value without reading, every value left is that one. -/
theorem hrest_vals_run (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (left : Nat) {v : Nat}
    (hr : runOf rlemax code = some v) (bs : List Bool) :
    hrest K g (.vals isL ntrees rlemax code done left) bs = hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate left v) 0) bs := by
  show (valsFrom rlemax code left bs >>= _) = (valsFrom rlemax code 0 bs >>= _)
  rw [valsFrom_run hr, valsFrom_zero]
  show afterVals K g isL ntrees (done ++ List.replicate left v) bs = afterVals K g isL ntrees ((done ++ List.replicate left v) ++ []) bs
  rw [List.append_nil]

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
      else if r.count = st.count then
        -- A code that gives a value without reading gives it for every value left.
        if v = 0 then { st with pos := pos, status := .next, idx := idx + left, left := 0 }
        else
          let fill := st.fill
          let st0 := clearFill st
          { st0 with pos := pos, status := .next, idx := idx + left, left := 0, fill := fillLens fill idx left v.toUInt8 }
      else if v = 0 then { st with word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run }
      else
        let fill := st.fill
        let st0 := clearFill st
        { st0 with
          word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
          fill := setU fill idx.toUSize v.toUInt8 }

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

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
      (Nat.le_refl _) hp (fun F => hrest_vals_zero K g isL ntrees rlemax code done _) (fun F => hStep_vals_zero _)
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
  have hsh0 := R.short
  have hnb : (mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩).status ≠ .bad := by
    unfold mapSymFast
    dsimp only
    split
    · split
      · exact fun e => ReadStatus.noConfusion e
      · split
        · split <;> exact fun e => ReadStatus.noConfusion e
        · exact fun e => ReadStatus.noConfusion e
    · exact fun e => ReadStatus.noConfusion e
  generalize mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval hsh0 hnb
  -- A code that gives a value without reading is the case where the read takes no bits.
  have hnone : ∀ v, runOf rlemax code = some v → r.status = .ok ∧ r.count = st.count ∧ r.a.toNat = v ∧ r.b.toNat = 1 := by
    intro v hv
    have hm := mapSym_of_run hv
    cases hsr : r.status with
    | short =>
      obtain ⟨_, _, _, h5⟩ := hsh0 hsr
      rw [hm] at h5
      cases h5
    | bad => exact absurd hsr hnb
    | ok =>
      have e := (hval hsr).2 []
      rw [List.append_nil, List.append_nil, hm] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨e1, e2⟩, e3⟩ := e
      have hl := congrArg List.length e3
      rw [held_len, held_len] at hl
      exact ⟨rfl, UInt64.toNat_inj.mp hl.symm, e1.symm, e2.symm⟩
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    have hno : runOf rlemax code = none := by
      cases e : runOf rlemax code with
      | none => rfl
      | some v => exact absurd ((hnone v e).1.symm.trans hsr) (by decide)
    exact HStepOk.ofShortRead (X := 31) hrel hfull (by omega) h3 h4
      (by rw [hStep_vals_step _ hl0 hno]; exact readIn_short h5 (by rw [held_len]; exact h3))
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
    by_cases hc : r.count = st.count
    · rw [ite_eq_left hc]
      -- The read took no bits: the code gives its value for every value left.
      have hro : runOf rlemax code = some r.a.toNat := by
        have e := (hval hsr).2 []
        rw [List.append_nil, List.append_nil] at e
        refine (mapSym_noRead e ?_).1
        show r.buf.held.length = _
        rw [held_len, held_len]
        exact congrArg UInt64.toNat hc
      have hidx3 : (st.idx + st.left).toNat = done.length + left := by
        rw [UInt64.toNat_add, hidx, hleft]
        exact Nat.mod_eq_of_lt (by omega)
      have hlen3 : (done ++ List.replicate left r.a.toNat).length = done.length + left := by simp
      have hz0 : (0 : UInt64).toNat = 0 := rfl
      by_cases hz : r.a = 0
      · rw [ite_eq_left hz]
        have hz' : r.a.toNat = 0 := by rw [hz]; rfl
        refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate left r.a.toNat) 0)
          (hd := Or.inl (Or.inr ⟨rfl, show 0 < left by omega⟩)) rfl
          ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hz0, ?_, hsz, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
        · show (st.idx + st.left).toNat = _
          rw [hidx3, hlen3]
        · rw [hlen3]
          omega
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          by_cases hA : i < done.length
          · rw [List.getElem?_append_left hA, hat i hA]
          · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), hzero i (by omega), hz']
            rfl
        · intro i hi'
          rw [hlen3] at hi'
          exact hzero i (by omega)
        · rw [hrest_vals_run K g isL ntrees rlemax code done left hro]
        · rw [hStep_vals_run _ hl0 hro]
      · rw [ite_eq_right hz]
        have hz' : r.a.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp e)
        have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
          rw [UInt64.toNat_toUInt8]
          omega
        obtain ⟨hfs, hfg⟩ := fillLens_spec r.a.toUInt8 left st.fill st.idx st.left hleft (by rw [hidx]; omega) (by rw [hidx, hsz]; omega)
        refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate left r.a.toNat) 0)
          (hd := Or.inl (Or.inr ⟨rfl, show 0 < left by omega⟩))
          (hm := ⟨rfl, rfl, fun h => ⟨by show (fillLens st.fill st.idx st.left r.a.toUInt8).size ≤ _; rw [hfs]; exact h.fill,
            h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
            by simp only [capH, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩) rfl
          ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hz0, ?_, ?_, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
        · show (st.idx + st.left).toNat = _
          rw [hidx3, hlen3]
        · rw [hlen3]
          omega
        · show (fillLens st.fill st.idx st.left r.a.toUInt8).size = _
          rw [hfs]
          exact hsz
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          show _ = some ((fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0).toNat
          rw [hfg i, hidx]
          by_cases hA : i < done.length
          · rw [ite_eq_right (by omega), List.getElem?_append_left hA, hat i hA]
          · rw [ite_eq_left (by omega), hbyte, List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega)]
        · intro i hi'
          rw [hlen3] at hi'
          show (fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0 = 0
          rw [hfg i, hidx, ite_eq_right (by omega)]
          exact hzero i (by omega)
        · rw [hrest_vals_run K g isL ntrees rlemax code done left hro]
          rfl
        · rw [hStep_vals_run _ hl0 hro]
          rfl
    rw [ite_eq_right hc]
    have hno : runOf rlemax code = none := by
      cases e : runOf rlemax code with
      | none => rfl
      | some v => exact absurd (hnone v e).2.1 hc
    have hidx2 : (st.idx + r.b).toNat = done.length + r.b.toNat := by
      rw [UInt64.toNat_add, hidx]
      exact Nat.mod_eq_of_lt (by omega)
    have hleft2 : (st.left - r.b).toNat = left - r.b.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hleft]; omega)), hleft]
    have hlen2 : (done ++ List.replicate r.b.toNat r.a.toNat).length = done.length + r.b.toNat := by simp
    by_cases hz : r.a = 0
    · rw [ite_eq_left hz]
      have hz' : r.a.toNat = 0 := by rw [hz]; rfl
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat))
        (hd := Or.inl (Or.inr ⟨rfl, show left - r.b.toNat < left by omega⟩)) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, hsz, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
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
      · rw [avail_mk, hStep_vals_step _ hl0 hno, readIn_some ((hval hsr).2 _)]
        simp only [hbig', ↓reduceIte]
        rfl
    · rw [ite_eq_right hz]
      have hz' : r.a.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp e)
      have hrun1 := hv1 hz'
      have hus : st.idx.toUSize.toNat = done.length := by rw [word_toUSize (by omega), hidx]
      have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
        rw [UInt64.toNat_toUInt8]
        omega
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat))
        (hd := Or.inl (Or.inr ⟨rfl, show left - r.b.toNat < left by omega⟩))
        (hm := ⟨rfl, rfl, fun h => ⟨by show (setU st.fill st.idx.toUSize r.a.toUInt8).size ≤ _; rw [size_setU]; exact h.fill,
          h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
          by simp only [capH, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, ?_, ?_, ?_, ?_⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
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
      · rw [avail_mk, hStep_vals_step _ hl0 hno, readIn_some ((hval hsr).2 _)]
        simp only [hbig', ↓reduceIte]
        rfl

end

/-! ### The inverse move-to-front transform -/

/-- The move-to-front list after some indices. -/
def mtfAfter : List Nat → List Nat → List Nat
  | L, [] => L
  | L, idx :: v => mtfAfter (L.getD idx 0 :: L.eraseIdx idx) v

theorem imtf_append : ∀ (L vs ws : List Nat),
    inverseMoveToFrontFrom L (vs ++ ws) = inverseMoveToFrontFrom L vs ++ inverseMoveToFrontFrom (mtfAfter L vs) ws
  | _, [], _ => rfl
  | L, idx :: v, ws => by
    show L.getD idx 0 :: inverseMoveToFrontFrom (L.getD idx 0 :: L.eraseIdx idx) (v ++ ws) =
      (L.getD idx 0 :: inverseMoveToFrontFrom (L.getD idx 0 :: L.eraseIdx idx) v) ++ _
    rw [imtf_append]
    rfl

theorem mtfAfter_append : ∀ (L vs ws : List Nat), mtfAfter L (vs ++ ws) = mtfAfter (mtfAfter L vs) ws
  | _, [], _ => rfl
  | _, _ :: v, ws => mtfAfter_append _ v ws

/-- The same index again and again turns the list's first places round, one place each time. -/
theorem mtfAfter_rot (L : List Nat) (s : Nat) (hs : s < L.length) : ∀ k, k ≤ s + 1 →
    mtfAfter L (List.replicate k s) = (L.take (s + 1)).drop (s + 1 - k) ++ (L.take (s + 1)).take (s + 1 - k) ++ L.drop (s + 1)
  | 0, _ => by
    simp only [List.replicate_zero, mtfAfter, Nat.sub_zero]
    rw [List.drop_eq_nil_of_le (by rw [List.length_take]; omega), List.take_take, Nat.min_self, List.nil_append, List.take_append_drop]
  | k + 1, hk => by
    rw [List.replicate_succ', mtfAfter_append, mtfAfter_rot L s hs k (by omega)]
    have hP : (L.take (s + 1)).length = s + 1 := by rw [List.length_take]; omega
    generalize L.take (s + 1) = P at hP ⊢
    generalize L.drop (s + 1) = C
    have hA : (P.drop (s + 1 - k)).length = k := by rw [List.length_drop]; omega
    have hB : (P.take (s + 1 - k)).length = s + 1 - k := by rw [List.length_take]; omega
    show (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 :: (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).eraseIdx s = _
    have hg : (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 = P.getD (s - k) 0 := by
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by rw [hA]; omega), hA,
        List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show s - k < s + 1 - k by omega),
        ← List.getD_eq_getElem?_getD]
    have e1 : (P.take (s + 1 - k)).eraseIdx (s - k) = P.take (s - k) := by
      rw [List.eraseIdx_eq_take_drop_succ, List.take_take, List.drop_eq_nil_of_le (by rw [hB]; omega), List.append_nil,
        Nat.min_eq_left (by omega)]
    have he : (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).eraseIdx s = P.drop (s + 1 - k) ++ P.take (s - k) ++ C := by
      rw [List.append_assoc, List.eraseIdx_append_of_length_le (by rw [hA]; omega), hA,
        List.eraseIdx_append_of_lt_length (by rw [hB]; omega), e1, ← List.append_assoc]
    rw [hg, he, show s + 1 - (k + 1) = s - k by omega, List.drop_eq_getElem_cons (show s - k < P.length by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s - k < P.length by omega), Option.getD_some,
      show s + 1 - k = s - k + 1 by omega]
    rfl

/-- The same index as many times as the places it turns round leaves the list as it was. -/
theorem mtfAfter_period (L : List Nat) (s : Nat) (hs : s < L.length) : mtfAfter L (List.replicate (s + 1) s) = L := by
  rw [mtfAfter_rot L s hs (s + 1) (Nat.le_refl _), Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil, List.take_append_drop]

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

/-- The transform's loop, one index at a time: each index's value moves to the front. -/
def imtfPlain (m out : ByteArray) (i n : UInt64) : ByteArray × ByteArray :=
  if _hn : n = 0 then (m, out)
  else
    let index := (getU out i.toUSize).toUInt64
    let value := getU m index.toUSize
    imtfPlain (setU (shiftUp m index) (USize.ofNat 0) value) (setU out i.toUSize value) (i + 1) (n - 1)
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

/-- What the one-at-a-time loop does: the values of `N` indices from `i`, the list after them, and the rest of the array as it
was. -/
theorem imtfPlain_spec : ∀ (N : Nat) (i n : UInt64) (m out : ByteArray) (L vs pre : List Nat), vs.length = N → n.toNat = N → i.toNat = pre.length →
    pre.length + N < 2 ^ 32 → pre.length + N ≤ out.size → MtfIs m L → (∀ j, j < pre.length → pre[j]? = some (out.data[j]?.getD 0).toNat) →
    (∀ j, j < N → vs[j]? = some (out.data[pre.length + j]?.getD 0).toNat) →
    (imtfPlain m out i n).2.size = out.size ∧ (∀ j, j < pre.length + N →
      (pre ++ inverseMoveToFrontFrom L vs)[j]? = some ((imtfPlain m out i n).2.data[j]?.getD 0).toNat) ∧
    (∀ q, pre.length + N ≤ q → (imtfPlain m out i n).2.data[q]? = out.data[q]?) ∧ MtfIs (imtfPlain m out i n).1 (mtfAfter L vs) := by
  intro N
  induction N with
  | zero =>
    intro i n m out L vs pre hv hn _ _ hs hm hp _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    have hnil : vs = [] := List.length_eq_zero_iff.mp hv
    subst hnil
    rw [imtfPlain, dite_eq_left hz]
    refine ⟨rfl, fun j hj => ?_, fun _ _ => rfl, hm⟩
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
      rw [imtfPlain, dite_eq_right hz]
      dsimp only
      generalize hindex : (getU out i.toUSize).toUInt64 = index at hidx
      obtain ⟨ms, mv⟩ := mtf_step hm (index := index) (by omega)
      rw [hidx] at ms mv
      generalize hval : getU m index.toUSize = value at ms mv
      have hbyte : value.toNat = L.getD idx 0 := mv
      have hsz := size_setU out i.toUSize value
      have hget : (setU out i.toUSize value).data[pre.length]?.getD 0 = value := by
        have := setU_get_same (t := out) (i := i.toUSize) (v := value) (by rw [hus]; omega)
        rwa [hus] at this
      have hlen' : (pre ++ [L.getD idx 0]).length = pre.length + 1 := by simp
      obtain ⟨r1, r2, r3, r4⟩ := ih (i + 1) (n - 1) _ (setU out i.toUSize value) _ rest (pre ++ [L.getD idx 0]) (by omega) hn1 (by rw [hi1, hlen']) (by rw [hlen']; omega)
        (by rw [hsz, hlen']; omega) ms
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
      rw [hlen'] at r2 r3
      refine ⟨by rw [r1, hsz], fun j hj => ?_, fun q hq' => ?_, r4⟩
      · have := r2 j (by omega)
        rw [List.append_assoc] at this
        exact this
      · rw [r3 q (by omega), setU_get_ne (by rw [hus]; omega)]

/-! ### Runs of the same index -/

/-- After the same index again and again, the list depends only on how many times it came, modulo the places it turns
round. -/
theorem mtfAfter_mod (L : List Nat) (s : Nat) (hs : s < L.length) :
    ∀ k, mtfAfter L (List.replicate k s) = mtfAfter L (List.replicate (k % (s + 1)) s) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < s + 1
    · rw [Nat.mod_eq_of_lt hk]
    · have e : List.replicate k s = List.replicate (s + 1) s ++ List.replicate (k - (s + 1)) s := by
        rw [List.replicate_append_replicate]
        congr 1
        omega
      rw [e, mtfAfter_append, mtfAfter_period L s hs, ih (k - (s + 1)) (by omega)]
      congr 2
      exact (Nat.mod_eq_sub_mod (by omega)).symm

theorem take_of_run {vs : List Nat} {r a : Nat} (h : ∀ j, j < r → vs[j]? = some a) :
    ∀ k, k ≤ r → vs.take k = List.replicate k a := by
  intro k hk
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_replicate]
  by_cases hj : j < k
  · rw [ite_eq_left hj, ite_eq_left hj, h j (by omega)]
  · rw [ite_eq_right hj, ite_eq_right hj]

theorem imtf_prefix (L vs ws : List Nat) {j : Nat} (hj : j < vs.length) :
    (inverseMoveToFrontFrom L (vs ++ ws))[j]? = (inverseMoveToFrontFrom L vs)[j]? := by
  rw [imtf_append, List.getElem?_append_left (by rw [inverseMoveToFrontFrom_length]; exact hj)]

theorem imtf_periodic (L : List Nat) (s : Nat) (hs : s < L.length) {k j : Nat} (hj : j + (s + 1) < k) :
    (inverseMoveToFrontFrom L (List.replicate k s))[j + (s + 1)]? = (inverseMoveToFrontFrom L (List.replicate k s))[j]? := by
  have e1 : List.replicate k s = List.replicate (s + 1) s ++ List.replicate (k - (s + 1)) s := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  have e2 : List.replicate k s = List.replicate (k - (s + 1)) s ++ List.replicate (s + 1) s := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  conv => lhs; rw [e1, imtf_append, mtfAfter_period L s hs]
  rw [List.getElem?_append_right (by rw [inverseMoveToFrontFrom_length, List.length_replicate]; omega),
    inverseMoveToFrontFrom_length, List.length_replicate, Nat.add_sub_cancel, e2, imtf_prefix _ _ _ (by rw [List.length_replicate]; omega)]

/-- How many more of the `k` bytes after the first `c` from `i` hold `s`, counted on from `c`. -/
def runCount (out : ByteArray) (i : UInt64) (s : UInt8) (c k : UInt64) : UInt64 :=
  if _hk : k = 0 then c
  else if getU out (i + c).toUSize = s then runCount out i s (c + 1) (k - 1) else c
termination_by k.toNat
decreasing_by
  have hne : k.toNat ≠ 0 := fun e => _hk (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (k - 1).toNat = k.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem runCount_spec (out : ByteArray) (i : UInt64) (s : UInt8) : ∀ (K : Nat) (c k : UInt64), k.toNat = K → c.toNat + K < 2 ^ 64 →
    c.toNat ≤ (runCount out i s c k).toNat ∧ (runCount out i s c k).toNat ≤ c.toNat + K ∧
    (i.toNat + c.toNat + K < 2 ^ 32 → ∀ j, c.toNat ≤ j → j < (runCount out i s c k).toNat → out.data[i.toNat + j]?.getD 0 = s) := by
  intro K
  induction K with
  | zero =>
    intro c k hk _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [runCount, dite_eq_left hz]
    exact ⟨Nat.le_refl _, by omega, fun _ j h1 h2 => absurd h2 (by omega)⟩
  | succ K ih =>
    intro c k hk hc
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hc1 : (c + 1).toNat = c.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    rw [runCount, dite_eq_right hz]
    by_cases he : getU out (i + c).toUSize = s
    · rw [ite_eq_left he]
      obtain ⟨a1, a2, a3⟩ := ih (c + 1) (k - 1) hk1 (by omega)
      refine ⟨by omega, by omega, fun h32 j h1 h2 => ?_⟩
      by_cases hj : j = c.toNat
      · subst hj
        have hic : (i + c).toNat = i.toNat + c.toNat := by
          rw [UInt64.toNat_add]
          exact Nat.mod_eq_of_lt (by omega)
        have := getU_toNat out (i + c).toUSize
        rw [he, word_toUSize (by omega), hic] at this
        exact (UInt8.toNat_inj.mp this).symm
      · exact a3 (by omega) j (by omega) h2
    · rw [ite_eq_right he]
      exact ⟨Nat.le_refl _, by omega, fun _ j h1 h2 => absurd h2 (by omega)⟩

/-- The value at the turning point of a list whose first `s + 1` places are turned round `k` places. -/
theorem rot_getD (P C : List Nat) {s k : Nat} (hP : P.length = s + 1) (hk : k ≤ s) :
    (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 = P.getD (s - k) 0 := by
  have hA : (P.drop (s + 1 - k)).length = k := by rw [List.length_drop]; omega
  have hB : (P.take (s + 1 - k)).length = s + 1 - k := by rw [List.length_take]; omega
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by rw [hA]; omega), hA,
    List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show s - k < s + 1 - k by omega),
    ← List.getD_eq_getElem?_getD]

/-- A round of the same index gives the list's first places backwards. -/
theorem imtf_rot_get (L : List Nat) (s : Nat) (hs : s < L.length) {t : Nat} (ht : t ≤ s) :
    (inverseMoveToFrontFrom L (List.replicate (s + 1) s))[t]? = some (L.getD (s - t) 0) := by
  have e : List.replicate (s + 1) s = List.replicate t s ++ (s :: List.replicate (s - t) s) := by
    rw [← List.replicate_succ, List.replicate_append_replicate]
    congr 1
    omega
  rw [e, imtf_append, List.getElem?_append_right (by rw [inverseMoveToFrontFrom_length, List.length_replicate]; exact Nat.le_refl _),
    inverseMoveToFrontFrom_length, List.length_replicate, Nat.sub_self]
  rw [show inverseMoveToFrontFrom (mtfAfter L (List.replicate t s)) (s :: List.replicate (s - t) s) =
    (mtfAfter L (List.replicate t s)).getD s 0 :: inverseMoveToFrontFrom ((mtfAfter L (List.replicate t s)).getD s 0 ::
      (mtfAfter L (List.replicate t s)).eraseIdx s) (List.replicate (s - t) s) from rfl]
  rw [List.getElem?_cons_zero, mtfAfter_rot L s hs t (by omega), rot_getD _ _ (by rw [List.length_take]; omega) ht,
    List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (show s - t < s + 1 by omega), ← List.getD_eq_getElem?_getD]

/-- A run's first round of values: the `n` outputs from `j`, each the list's value `j` places before `s`. -/
def revOut (m out : ByteArray) (i s j n : UInt64) : ByteArray :=
  if _hn : n = 0 then out else revOut m (setU out (i + j).toUSize (getU m (s - j).toUSize)) i s (j + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem revOut_spec (m : ByteArray) (i s : UInt64) : ∀ (N : Nat) (j n : UInt64) (out : ByteArray), n.toNat = N →
    j.toNat + N ≤ s.toNat + 1 → s.toNat < 256 → i.toNat + j.toNat + N < 2 ^ 32 → i.toNat + j.toNat + N ≤ out.size →
    (revOut m out i s j n).size = out.size ∧ (∀ q, q < i.toNat + j.toNat → (revOut m out i s j n).data[q]? = out.data[q]?) ∧
    (∀ q, i.toNat + j.toNat + N ≤ q → (revOut m out i s j n).data[q]? = out.data[q]?) ∧
    (∀ t, j.toNat ≤ t → t < j.toNat + N → (revOut m out i s j n).data[i.toNat + t]?.getD 0 = m.data[s.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro j n out hn _ _ _ _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [revOut, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun t h1 h2 => absurd h2 (by omega)⟩
  | succ N ih =>
    intro j n out hn hjs hs h32 hsz
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hij : (i + j).toNat = i.toNat + j.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : (i + j).toUSize.toNat = i.toNat + j.toNat := by rw [word_toUSize (by omega), hij]
    have hsj : (s - j).toUSize.toNat = s.toNat - j.toNat := by
      rw [word_toUSize (by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega),
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    rw [revOut, dite_eq_right hz]
    generalize hv : getU m (s - j).toUSize = v
    have hvb : v = m.data[s.toNat - j.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, hsj]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (n - 1) (setU out (i + j).toUSize v) hn1 (by omega) hs (by omega)
      (by rw [size_setU]; omega)
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_setU], fun q hq => ?_, fun q hq => ?_, fun t h1 h2 => ?_⟩
    · rw [b2 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · rw [b3 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases ht : t = j.toNat
      · subst ht
        rw [b2 _ (by omega)]
        have := setU_get_same (t := out) (i := (i + j).toUSize) (v := v) (by rw [hus]; omega)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 t (by omega) (by omega)

/-- Rewrites `n` places of the list from `x`, each from the outputs, going back from `a`. -/
def rotFrom (out m : ByteArray) (i x a n : UInt64) : ByteArray :=
  if _hn : n = 0 then m else rotFrom out (setU m x.toUSize (getU out (i + a).toUSize)) i (x + 1) (a - 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem rotFrom_spec (out : ByteArray) (i : UInt64) : ∀ (N : Nat) (x a n : UInt64) (m : ByteArray), n.toNat = N →
    (0 < N → N ≤ a.toNat + 1 ∧ i.toNat + a.toNat < 2 ^ 32) → x.toNat + N ≤ 256 → m.size = 256 →
    (rotFrom out m i x a n).size = 256 ∧ (∀ y, y < x.toNat ∨ x.toNat + N ≤ y → (rotFrom out m i x a n).data[y]? = m.data[y]?) ∧
    (∀ t, t < N → (rotFrom out m i x a n).data[x.toNat + t]?.getD 0 = out.data[i.toNat + a.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro x a n m hn _ _ hs
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [rotFrom, dite_eq_left hz]
    exact ⟨hs, fun _ _ => rfl, fun t h => absurd h (by omega)⟩
  | succ N ih =>
    intro x a n m hn ha hx hs
    obtain ⟨ha1, ha2⟩ := ha (by omega)
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hx1 : (x + 1).toNat = x.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hia : (i + a).toNat = i.toNat + a.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : x.toUSize.toNat = x.toNat := word_toUSize (by omega)
    have husa : (i + a).toUSize.toNat = i.toNat + a.toNat := by rw [word_toUSize (by omega), hia]
    rw [rotFrom, dite_eq_right hz]
    generalize hv : getU out (i + a).toUSize = v
    have hvb : v = out.data[i.toNat + a.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, husa]
    obtain ⟨b1, b2, b3⟩ := ih (x + 1) (a - 1) (n - 1) (setU m x.toUSize v) hn1
      (fun h => by
        have ha1' : (a - 1).toNat = a.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
        rw [ha1']
        omega)
      (by rw [hx1]; omega) (by rw [size_setU]; exact hs)
    rw [hx1] at b2 b3
    refine ⟨b1, fun y hy => ?_, fun t ht => ?_⟩
    · rw [b2 y (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases ht0 : t = 0
      · subst ht0
        rw [Nat.add_zero, b2 _ (by omega)]
        have := setU_get_same (t := m) (i := x.toUSize) (v := v) (by rw [hus, hs]; omega)
        rw [hus] at this
        rw [this, hvb, Nat.sub_zero]
      · have ha1' : (a - 1).toNat = a.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
        have := b3 (t - 1) (by omega)
        rw [ha1', show x.toNat + 1 + (t - 1) = x.toNat + t by omega, show i.toNat + (a.toNat - 1) - (t - 1) = i.toNat + a.toNat - t by omega]
          at this
        exact this

/-- Copies `k` bytes from `p` places back, one at a time, so that from `j` on the bytes repeat with period `p`. -/
def copyPeriod (out : ByteArray) (j k p : UInt64) : ByteArray :=
  if _hk : k = 0 then out else copyPeriod (setU out j.toUSize (getU out (j - p).toUSize)) (j + 1) (k - 1) p
termination_by k.toNat
decreasing_by
  have hne : k.toNat ≠ 0 := fun e => _hk (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (k - 1).toNat = k.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem copyPeriod_spec (p : UInt64) (hp : 1 ≤ p.toNat) : ∀ (K : Nat) (j k : UInt64) (out : ByteArray), k.toNat = K → p.toNat ≤ j.toNat →
    j.toNat + K < 2 ^ 32 → j.toNat + K ≤ out.size →
    (copyPeriod out j k p).size = out.size ∧ (∀ q, q < j.toNat → (copyPeriod out j k p).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat + K ≤ q → (copyPeriod out j k p).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat ≤ q → q < j.toNat + K → (copyPeriod out j k p).data[q]?.getD 0 = (copyPeriod out j k p).data[q - p.toNat]?.getD 0) := by
  intro K
  induction K with
  | zero =>
    intro j k out hk _ _ _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [copyPeriod, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun q h1 h2 => absurd h2 (by omega)⟩
  | succ K ih =>
    intro j k out hk hpj h32 hs
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hjp : (j - p).toNat = j.toNat - p.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hpj)
    have hus : j.toUSize.toNat = j.toNat := word_toUSize (by omega)
    have husp : (j - p).toUSize.toNat = j.toNat - p.toNat := by rw [word_toUSize (by omega), hjp]
    rw [copyPeriod, dite_eq_right hz]
    generalize hv : getU out (j - p).toUSize = v
    have hvb : v = out.data[j.toNat - p.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, husp]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (k - 1) (setU out j.toUSize v) hk1 (by omega) (by omega) (by rw [size_setU]; omega)
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_setU], fun q hq => ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩
    · rw [b2 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · rw [b3 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases hq : q = j.toNat
      · subst hq
        rw [b2 _ (by omega), b2 _ (by omega), setU_get_ne (show j.toNat - p.toNat ≠ j.toUSize.toNat by rw [hus]; omega)]
        have := setU_get_same (t := out) (i := j.toUSize) (v := v) (by rw [hus]; omega)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 q (by omega) (by omega)

/-- The transform's loop: each index's value moves to the front. A run of the same index longer than the places it turns
round gives that round's values, the list's first places backwards, and the rest of its values repeat them; the list is
then those places turned round as far as the run's length goes past whole rounds, rewritten from the values. -/
def imtfGo (m out : ByteArray) (i n : UInt64) : ByteArray × ByteArray :=
  if _hn : n = 0 then (m, out)
  else
    let index := (getU out i.toUSize).toUInt64
    let r := runCount out i (getU out i.toUSize) 1 (n - 1)
    if _hr : r ≤ index + 1 then
      match imtfPlain m out i 1 with
      | (m1, out1) => imtfGo m1 out1 (i + 1) (n - 1)
    else
      let p := index + 1
      let out2 := copyPeriod (revOut m out i index 0 p) (i + p) (r - p) p
      let k := (r - p) % p
      imtfGo (rotFrom out2 (rotFrom out2 m i 0 (k - 1) k) i k index (p - k)) out2 (i + r) (n - r)
termination_by n.toNat
decreasing_by
  · have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (1 : UInt64).toNat = 1 from rfl]
      omega))
    omega
  · have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (1 : UInt64).toNat = 1 from rfl]
      omega))
    have hn64 : n.toNat < 2 ^ 64 := n.toNat_lt
    obtain ⟨c1, c2, _⟩ := runCount_spec out i (getU out i.toUSize) _ 1 (n - 1) rfl
      (by rw [h1, show (1 : UInt64).toNat = 1 from rfl]; omega)
    rw [show (1 : UInt64).toNat = 1 from rfl] at c1 c2
    rw [h1] at c2
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega

/-- What the loop does, as the one-at-a-time loop does it: the values of `N` indices from `i`, the list after them, and the
rest of the array as it was. -/
theorem imtfGo_spec : ∀ (N : Nat) (i n : UInt64) (m out : ByteArray) (L vs pre : List Nat), vs.length = N → n.toNat = N → i.toNat = pre.length →
    pre.length + N < 2 ^ 32 → pre.length + N ≤ out.size → MtfIs m L → (∀ j, j < pre.length → pre[j]? = some (out.data[j]?.getD 0).toNat) →
    (∀ j, j < N → vs[j]? = some (out.data[pre.length + j]?.getD 0).toNat) →
    (imtfGo m out i n).2.size = out.size ∧ (∀ j, j < pre.length + N →
      (pre ++ inverseMoveToFrontFrom L vs)[j]? = some ((imtfGo m out i n).2.data[j]?.getD 0).toNat) ∧
    (∀ q, pre.length + N ≤ q → (imtfGo m out i n).2.data[q]? = out.data[q]?) ∧ MtfIs (imtfGo m out i n).1 (mtfAfter L vs) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro i n m out L vs pre hv hn hi h32 hs hm hp hq
  by_cases hN : N = 0
  · subst hN
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    have hnil : vs = [] := List.length_eq_zero_iff.mp hv
    subst hnil
    rw [imtfGo, dite_eq_left hz]
    refine ⟨rfl, fun j hj => ?_, fun _ _ => rfl, hm⟩
    simp only [inverseMoveToFrontFrom, List.append_nil]
    exact hp j (by omega)
  have hz : n ≠ 0 := fun e => hN (by rw [← hn, e]; rfl)
  -- Once the first `k` indices are done, the rest is the loop again.
  have cont : ∀ (k : Nat) (m2 out2 : ByteArray), 1 ≤ k → k ≤ N → out2.size = out.size →
      (∀ j, j < pre.length + k → (pre ++ inverseMoveToFrontFrom L (vs.take k))[j]? = some (out2.data[j]?.getD 0).toNat) →
      (∀ q, pre.length + k ≤ q → out2.data[q]? = out.data[q]?) → MtfIs m2 (mtfAfter L (vs.take k)) →
      ∀ (i2 n2 : UInt64), i2.toNat = pre.length + k → n2.toNat = N - k →
      (imtfGo m2 out2 i2 n2).2.size = out.size ∧ (∀ j, j < pre.length + N →
        (pre ++ inverseMoveToFrontFrom L vs)[j]? = some ((imtfGo m2 out2 i2 n2).2.data[j]?.getD 0).toNat) ∧
      (∀ q, pre.length + N ≤ q → (imtfGo m2 out2 i2 n2).2.data[q]? = out.data[q]?) ∧ MtfIs (imtfGo m2 out2 i2 n2).1 (mtfAfter L vs) := by
    intro k m2 out2 hk1 hkN hsz2 hout2 hfr2 hm2 i2 n2 hi2 hn2
    have lenP : (pre ++ inverseMoveToFrontFrom L (vs.take k)).length = pre.length + k := by
      rw [List.length_append, inverseMoveToFrontFrom_length, List.length_take]
      omega
    obtain ⟨e1, e2, e3, e4⟩ := ih (N - k) (by omega) i2 n2 m2 out2 _ (vs.drop k) (pre ++ inverseMoveToFrontFrom L (vs.take k))
      (by rw [List.length_drop]; omega) hn2 (by rw [lenP]; exact hi2) (by rw [lenP]; omega) (by rw [lenP, hsz2]; omega) hm2
      (fun j hj => hout2 j (by rw [lenP] at hj; exact hj))
      (fun j hj => by
        rw [lenP, List.getElem?_drop, hfr2 _ (by omega), hq (k + j) (by omega), Nat.add_assoc])
    rw [lenP] at e2 e3
    refine ⟨e1.trans hsz2, fun j hj => ?_, fun q hq' => ?_, ?_⟩
    · rw [← List.take_append_drop k vs, imtf_append, ← List.append_assoc]
      exact e2 j (by omega)
    · rw [e3 q (by omega), hfr2 q (by omega)]
    · rw [← List.take_append_drop k vs, mtfAfter_append]
      exact e4
  have hus : i.toUSize.toNat = pre.length := by rw [word_toUSize (by omega), hi]
  have hbyte : (getU out i.toUSize).toNat = (out.data[pre.length]?.getD 0).toNat := by rw [getU_toNat, hus]
  have hn1 : (n - 1).toNat = N - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
    rfl
  have hi1 : (i + 1).toNat = pre.length + 1 := by
    rw [UInt64.toNat_add, hi, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨c1, c2, c3⟩ := runCount_spec out i (getU out i.toUSize) (N - 1) 1 (n - 1) hn1
    (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
  rw [show (1 : UInt64).toNat = 1 from rfl] at c1 c2 c3
  rw [imtfGo, dite_eq_right hz]
  dsimp only
  generalize hb : getU out i.toUSize = byte at hbyte c1 c2 c3 ⊢
  generalize hr : runCount out i byte 1 (n - 1) = r at c1 c2 c3 ⊢
  have hsb : byte.toNat < 256 := byte.toNat_lt
  have hb64 : byte.toUInt64.toNat = byte.toNat := UInt8.toNat_toUInt64 byte
  have hsL : byte.toNat < L.length := by rw [hm.length]; exact hsb
  have hrun : ∀ j, j < r.toNat → vs[j]? = some byte.toNat := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [hq 0 (by omega), Nat.add_zero, hbyte]
    · rw [hq j (by omega), ← hi, c3 (by omega) j (by omega) hj]
  have htk := take_of_run hrun
  have hpre1 : ∀ j, j < 1 → (vs.take 1)[j]? = some (out.data[pre.length + j]?.getD 0).toNat := fun j hj => by
    rw [List.getElem?_take, ite_eq_left hj]
    exact hq j (by omega)
  by_cases hle : r ≤ byte.toUInt64 + 1
  · rw [dite_eq_left hle]
    obtain ⟨p1, p2, p3, p4⟩ := imtfPlain_spec 1 i 1 m out L (vs.take 1) pre (by rw [List.length_take]; omega) rfl hi
      (by omega) (by omega) hm hp hpre1
    generalize imtfPlain m out i 1 = pl at p1 p2 p3 p4 ⊢
    obtain ⟨m1, out1⟩ := pl
    dsimp only at p1 p2 p3 p4 ⊢
    exact cont 1 m1 out1 (Nat.le_refl _) (by omega) p1 p2 p3 p4 (i + 1) (n - 1) hi1 hn1
  · rw [dite_eq_right hle]
    have hp1 : (byte.toUInt64 + 1).toNat = byte.toNat + 1 := by
      rw [UInt64.toNat_add, hb64, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hrp : byte.toNat + 1 < r.toNat := Nat.lt_of_not_le fun e => hle (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; exact e))
    have hz0 : (0 : UInt64).toNat = 0 := rfl
    obtain ⟨o1, o2, o3, o4⟩ := revOut_spec m i byte.toUInt64 (byte.toNat + 1) 0 (byte.toUInt64 + 1) out hp1
      (by rw [hz0, hb64]; omega) (by rw [hb64]; exact hsb) (by rw [hz0, hi]; omega) (by rw [hz0, hi]; omega)
    rw [hz0, Nat.add_zero, hi] at o2 o3
    rw [hz0, hb64, hi] at o4
    generalize revOut m out i byte.toUInt64 0 (byte.toUInt64 + 1) = out1 at o1 o2 o3 o4 ⊢
    have hip : (i + (byte.toUInt64 + 1)).toNat = pre.length + (byte.toNat + 1) := by
      rw [UInt64.toNat_add, hi, hp1]
      exact Nat.mod_eq_of_lt (by omega)
    have hrs : (r - (byte.toUInt64 + 1)).toNat = r.toNat - (byte.toNat + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨q1, q2, q3, q4⟩ := copyPeriod_spec (byte.toUInt64 + 1) (by rw [hp1]; omega) (r.toNat - (byte.toNat + 1))
      (i + (byte.toUInt64 + 1)) (r - (byte.toUInt64 + 1)) out1 hrs (by rw [hip, hp1]; omega) (by rw [hip]; omega)
      (by rw [hip, o1]; omega)
    rw [hip] at q2 q3 q4
    rw [hp1] at q4
    generalize copyPeriod out1 (i + (byte.toUInt64 + 1)) (r - (byte.toUInt64 + 1)) (byte.toUInt64 + 1) = out2 at q1 q2 q3 q4 ⊢
    -- The round's values, in the outputs, are the list's first places backwards.
    have hfirst : ∀ t, t ≤ byte.toNat → (out2.data[pre.length + t]?.getD 0).toNat = L.getD (byte.toNat - t) 0 := by
      intro t ht
      rw [q2 _ (by omega), o4 t (Nat.zero_le _) (by omega), hm.at_ _ (by omega)]
    -- The list after the run: its first places turned round as far as the run goes past whole rounds.
    have hK : (r.toNat - (byte.toNat + 1)) % (byte.toNat + 1) < byte.toNat + 1 := Nat.mod_lt _ (by omega)
    generalize hKd : (r.toNat - (byte.toNat + 1)) % (byte.toNat + 1) = K at hK
    have hk : ((r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1)).toNat = K := by rw [UInt64.toNat_mod, hrs, hp1, hKd]
    generalize (r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1) = k at hk ⊢
    have hir32 : i.toNat + byte.toNat < 2 ^ 32 := by rw [hi]; omega
    obtain ⟨a1, a2, a3⟩ := rotFrom_spec out2 i K 0 (k - 1) k m hk
      (fun h => by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk, show (1 : UInt64).toNat = 1 from rfl]; omega)), hk,
          show (1 : UInt64).toNat = 1 from rfl]
        omega)
      (by rw [hz0]; omega) hm.sz
    have hpk : (byte.toUInt64 + 1 - k).toNat = byte.toNat + 1 - K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk, hp1]; omega)), hk, hp1]
    obtain ⟨c1, c2, c3⟩ := rotFrom_spec out2 i (byte.toNat + 1 - K) k byte.toUInt64 (byte.toUInt64 + 1 - k)
      (rotFrom out2 m i 0 (k - 1) k) hpk (fun _ => by rw [hb64]; omega) (by rw [hk]; omega) a1
    rw [hz0] at a2 a3
    rw [hk] at c2 c3
    rw [hb64] at c3
    have hms : MtfIs (rotFrom out2 (rotFrom out2 m i 0 (k - 1) k) i k byte.toUInt64 (byte.toUInt64 + 1 - k))
        (mtfAfter L (List.replicate r.toNat byte.toNat)) := by
      rw [mtfAfter_mod L _ hsL, Nat.mod_eq_sub_mod (by omega), hKd, mtfAfter_rot L _ hsL K (by omega)]
      have hP : (L.take (byte.toNat + 1)).length = byte.toNat + 1 := by rw [List.length_take]; omega
      have hA : ((L.take (byte.toNat + 1)).drop (byte.toNat + 1 - K)).length = K := by rw [List.length_drop]; omega
      have hB : ((L.take (byte.toNat + 1)).take (byte.toNat + 1 - K)).length = byte.toNat + 1 - K := by
        rw [List.length_take]; omega
      have hL := hm.length
      refine ⟨c1, by simp only [List.length_append, hA, hB, List.length_drop]; omega, fun x hx => ?_⟩
      rw [List.getD_eq_getElem?_getD, List.append_assoc]
      by_cases h1 : x < K
      · rw [List.getElem?_append_left (by rw [hA]; exact h1), List.getElem?_drop, List.getElem?_take,
          ite_eq_left (show byte.toNat + 1 - K + x < byte.toNat + 1 by omega), ← List.getD_eq_getElem?_getD,
          c2 x (Or.inl h1)]
        have := a3 x h1
        have hk1 : (k - 1).toNat = K - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hk, show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
          rfl
        rw [show 0 + x = x by omega, hk1] at this
        rw [this, show i.toNat + (K - 1) - x = pre.length + (K - 1 - x) by rw [hi]; omega, hfirst _ (by omega)]
        congr 1
        omega
      · rw [List.getElem?_append_right (by rw [hA]; omega), hA]
        by_cases h2 : x ≤ byte.toNat
        · rw [List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show x - K < byte.toNat + 1 - K by omega),
            List.getElem?_take, ite_eq_left (show x - K < byte.toNat + 1 by omega), ← List.getD_eq_getElem?_getD]
          have := c3 (x - K) (by omega)
          rw [show K + (x - K) = x by omega] at this
          rw [this, show i.toNat + byte.toNat - (x - K) = pre.length + (byte.toNat - (x - K)) by rw [hi]; omega,
            hfirst _ (by omega)]
          congr 1
          omega
        · rw [List.getElem?_append_right (by rw [hB]; omega), hB, List.getElem?_drop,
            show byte.toNat + 1 + (x - K - (byte.toNat + 1 - K)) = x by omega, ← List.getD_eq_getElem?_getD,
            c2 x (Or.inr (by omega)), a2 x (Or.inr (by omega)), hm.at_ x hx]
    have hsplit : List.replicate r.toNat byte.toNat =
        List.replicate (byte.toNat + 1) byte.toNat ++ List.replicate (r.toNat - (byte.toNat + 1)) byte.toNat := by
      rw [List.replicate_append_replicate]
      congr 1
      omega
    have hlen1 : (pre ++ inverseMoveToFrontFrom L (List.replicate (byte.toNat + 1) byte.toNat)).length = pre.length + (byte.toNat + 1) := by
      rw [List.length_append, inverseMoveToFrontFrom_length, List.length_replicate]
    have hpre : ∀ j, j < pre.length + (byte.toNat + 1) →
        (pre ++ inverseMoveToFrontFrom L (List.replicate r.toNat byte.toNat))[j]? =
          (pre ++ inverseMoveToFrontFrom L (List.replicate (byte.toNat + 1) byte.toNat))[j]? := by
      intro j hj
      rw [hsplit, imtf_append, ← List.append_assoc, List.getElem?_append_left (by rw [hlen1]; exact hj)]
    have hout : ∀ j, j < pre.length + r.toNat →
        (pre ++ inverseMoveToFrontFrom L (List.replicate r.toNat byte.toNat))[j]? = some (out2.data[j]?.getD 0).toNat := by
      intro j
      induction j using Nat.strongRecOn with
      | _ j ihj =>
        intro hj
        by_cases hlo : j < pre.length + (byte.toNat + 1)
        · rw [hpre j hlo]
          by_cases hlp : j < pre.length
          · rw [List.getElem?_append_left hlp, hp j hlp, q2 j hlo, o2 j hlp]
          · rw [List.getElem?_append_right (by omega), imtf_rot_get L _ hsL (by omega),
              show j = pre.length + (j - pre.length) by omega, hfirst _ (by omega)]
            congr 3
            omega
        · rw [q4 j (by omega) (by omega), ← ihj (j - (byte.toNat + 1)) (by omega) (by omega),
            List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
            show j - pre.length = j - (byte.toNat + 1) - pre.length + (byte.toNat + 1) by omega,
            imtf_periodic L _ hsL (by omega), show j - (byte.toNat + 1) - pre.length = j - pre.length - (byte.toNat + 1) by omega]
    have hir : (i + r).toNat = pre.length + r.toNat := by
      rw [UInt64.toNat_add, hi]
      exact Nat.mod_eq_of_lt (by omega)
    have hnr : (n - r).toNat = N - r.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hn]
    exact cont r.toNat _ out2 (by omega) (by omega) (q1.trans o1) (by rw [htk _ (Nat.le_refl _)]; exact hout)
      (fun q hq' => by rw [q3 q (by omega), o3 q (by omega)]) (by rw [htk _ (Nat.le_refl _)]; exact hms) (i + r) (n - r) hir hnr

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
    let final := if b.peek 1 = 0 then fill else (imtfGo mtfInitLut fill 0 size).2
    if allOccur final size n then mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n final
    else { st0 with pos := pos, status := .bad }
  else markH st pos .needsInput

private theorem not_le_lt3 {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

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
    have hjspec : ∀ f, hStepP (g, .imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
        if (List.range ntrees).all (if im.toNat = 0 then vals else inverseMoveToFront vals).contains then
          .next (g.setMap isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals),
            mapNextPhase (g.setMap isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals)) isL) (b1.held ++ f)
        else .bad := by
      intro f
      show readIn 1 (readInt 1) _ _ = _
      rw [readIn_some (show readInt 1 ((BitBuffer.mk st.word st.count).held ++ f) = _ from hread f)]
    have hsz : (UInt64.ofNat st.fill.size).toNat = mapSize g isL := by
      rw [hm.sz]
      exact u64_lit (by omega)
    have hfinal : MapOk (if im = 0 then st.fill else (imtfGo mtfInitLut st.fill 0 (UInt64.ofNat st.fill.size)).2)
        (if im.toNat = 0 then vals else inverseMoveToFront vals) (mapSize g isL) ntrees := by
      by_cases hz : im = 0
      · rw [ite_eq_left hz, ite_eq_left (show im.toNat = 0 by rw [hz]; rfl)]
        exact hm
      · rw [ite_eq_right hz, ite_eq_right (show ¬ im.toNat = 0 from fun e => hz (UInt64.toNat_inj.mp e))]
        obtain ⟨r1, r2, _, _⟩ := imtfGo_spec _ 0 (UInt64.ofNat st.fill.size) mtfInitLut st.fill (List.range 256) vals [] hm.length hsz rfl
          (by simp; omega) (by rw [List.length_nil, Nat.zero_add, hm.sz]; exact Nat.le_refl _) mtfInit_is
          (fun j hj => absurd hj (by simp)) (fun j hj => by simpa using hm.at_ j hj)
        simp only [List.length_nil, Nat.zero_add, List.nil_append] at r1 r2
        exact ⟨r1.trans hm.sz, by rw [inverseMoveToFront, inverseMoveToFrontFrom_length]; exact hm.length, r2, inverseMoveToFront_lt hm.lt⟩
    generalize (if im = 0 then st.fill else (imtfGo mtfInitLut st.fill 0 (UInt64.ofNat st.fill.size)).2) = final at hfinal ⊢
    generalize (if im.toNat = 0 then vals else inverseMoveToFront vals) = cmap at hfinal hspec hjspec
    have hocc := allOccur_iff (map := final) (l := cmap) (size := UInt64.ofNat st.fill.size) (n := st.ntrees)
      (by rw [hsz]; omega) (by omega) (by rw [hsz]; exact hfinal.length) (by rw [hsz]; exact hfinal.at_)
    rw [hn] at hocc
    by_cases hc : allOccur final (UInt64.ofNat st.fill.size) st.ntrees = true
    · rw [ite_eq_left hc]
      have hrel2 := mapFinish_rel (st := { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next })
        (cmap := cmap) (ntrees := ntrees) (n := st.ntrees) (map := final) hw1 hi hu hfinal hn (by omega) h256
      obtain ⟨c1, c2, c3, c4⟩ := mapFinish_spec { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final
      have hmv := mapFinish_move (st0 := st) (st := { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next }) (g := g) (p := .imtf isL ntrees vals)
        (n := st.ntrees) (ntrees := ntrees) (cmap := cmap) (map := final) hi hu hfinal.sz ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun _ => Nat.zero_le _) (Nat.le_refl _)
      generalize mapFinish { clearFill st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final = r2 at hrel2 c1 c2 c3 c4 hmv ⊢
      refine HStepOk.ofNext (hd := imtfNext_down _ _ _ _) (hm := hmv) c4 hrel2 (by rw [c3]; exact Nat.le_refl _) (by rw [c3]; exact hp)
        (fun F => ?_) (fun F => ?_)
      · rw [avail_mk, hspec, ite_eq_left (hocc.mp hc), afterMap_eq, avail_mk, c1, c2, c3]
      · rw [avail_mk, hjspec, ite_eq_left (hocc.mp hc), avail_mk, c1, c2, c3]
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
      (by show readIn 1 (readInt 1) _ _ = _; exact readIn_short (readInt_short (b := ⟨st.word, st.count⟩) hc) (by rw [held_len]; exact hc))

end

end Brotli.Decoder
