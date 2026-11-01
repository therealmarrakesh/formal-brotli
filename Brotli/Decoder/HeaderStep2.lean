import Brotli.Decoder.HeaderStep

/-!
# More of the header's steps

The places that read a field or move between stages: a category's first block count, NPOSTFIX and NDIRECT, the context
modes, a context map's number of trees and RLEMAX, and the start and end of a group of codes.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

/-! ### A category's first block count -/

/-- Checks a table in the arena, once a place is about to use it. -/
@[inline] def tableCheck (t : ByteArray) (base : USize) : Bool := fitsFast t base.toUInt64

theorem tableCheck_iff {t : ByteArray} {base : USize} : tableCheck t base = true ↔ t.size < 2 ^ 32 ∧ TableFits t base.toNat := by
  unfold tableCheck
  rw [fitsFast_iff, USize.toNat_toUInt64]

/-- The place at a category's first block count. -/
def stepHFirst (st : Hd) (pos : USize) : Hd :=
  let i := st.cat
  let base := st.d.baseCOf i
  if h : tableCheck st.d.arena base = true then
    let r := blockCountFast st.d.arena base (tableCheck_iff.mp h).2 (tableCheck_iff.mp h).1 ⟨st.word, st.count⟩
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      catMoveOn { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := st.d.setCount i r.a }
  else markH st pos .bad

private theorem setCount_nOf' (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).nOf j = d.nOf j := by
  cases i <;> cases j <;> rfl

private theorem setCount_countOf' (d : Done) (i : Cat) (v : UInt64) : (d.setCount i v).countOf i = v := by cases i <;> rfl

private theorem setCount_baseT' (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).baseTOf j = d.baseTOf j := by
  cases i <;> cases j <;> rfl

private theorem setCount_baseC' (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).baseCOf j = d.baseCOf j := by
  cases i <;> cases j <;> rfl

private theorem setCount_arena' (d : Done) (i : Cat) (v : UInt64) :
    (d.setCount i v).arena = d.arena ∧ (d.setCount i v).arenaMax = d.arenaMax := by
  cases i <;> exact ⟨rfl, rfl⟩

private theorem setCount_countOf_ne (d : Done) (i j : Cat) (v : UInt64) (hj : j ≠ i) : (d.setCount i v).countOf j = d.countOf j := by
  cases i <;> cases j <;> first | exact absurd rfl hj | rfl

theorem stepHFirst_ok {i : Cat} {n : Nat} {tc cc : PrefixCode} {st : Hd} {g : Gh} {pos : USize} (hrel : HRel st g (.first i n tc cc))
    (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.first i n tc cc) st pos (stepHFirst st pos) := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256, okT, cT, sT, okC, cC, sC⟩ := hrel
  have hrel : HRel st g (.first i n tc cc) := ⟨hw, hu, ht, hi, hn, h2, h256, okT, cT, sT, okC, cC, sC⟩
  subst hi
  have hsize : st.d.arena.size < 2 ^ 32 := by
    have := hu.le
    have := hu.max
    omega
  have hcheck : tableCheck st.d.arena (st.d.baseCOf st.cat) = true := tableCheck_iff.mpr ⟨hsize, okC.toTableFits⟩
  unfold stepHFirst
  dsimp only
  rw [dite_eq_left hcheck]
  have R := blockCountFast_ok (hfit := (tableCheck_iff.mp hcheck).2) (h32 := (tableCheck_iff.mp hcheck).1) hw okC cC sC
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.first st.cat n tc cc)) (N := fun v b =>
    afterCat K g st.cat ⟨n, tc, cc, v⟩ b) (fun bs => rfl)
  generalize blockCountFast st.d.arena (st.d.baseCOf st.cat) (tableCheck_iff.mp hcheck).2 (tableCheck_iff.mp hcheck).1
    ⟨st.word, st.count⟩ = r at Rok Rshort Rbad
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    exact HStepOk.ofShortRead (X := 39) hrel hfull (by omega) h3 h4
  | bad =>
    exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hd := setCount_arena' st.d st.cat r.a
    generalize hc : (⟨n, tc, cc, r.a.toNat⟩ : BlockCategory) = c at hN
    have hcat : CatOk (st.d.setCount st.cat r.a) st.cat c := by
      subst hc
      have hSize : blockTypeAlphabetSize n = n + 2 := rfl
      refine ⟨?_, ?_, ?_, ?_, cT, cC⟩
      · rw [setCount_nOf']
        exact hn
      · rw [setCount_countOf']
      · rw [hd.1, setCount_baseT', setCount_baseC']
        exact ⟨fun _ => ⟨okT, cT, sT⟩, fun _ => ⟨okC, cC, sC⟩⟩
      · exact ⟨by simp only; omega, h256, fun _ => sT⟩
    have hup : Upto (st.d.setCount st.cat r.a) (g.setCat st.cat c) (stageOf (catNextPhase st.cat)) :=
      hu.catDone hd.1 hd.2 (fun j hj => ⟨setCount_nOf' _ _ _ _, setCount_countOf_ne _ _ _ _ hj, setCount_baseT' _ _ _ _,
        setCount_baseC' _ _ _ _⟩) hcat
    have hrel2 := catMoveOn_rel (st := { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := st.d.setCount st.cat r.a }) hw2 rfl hup
    obtain ⟨b1, b2, b3, b4, _⟩ := catMoveOn_spec { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := st.d.setCount st.cat r.a }
    have ha : Arr (catMoveOn { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := st.d.setCount st.cat r.a }) st := (catMoveOn_arr _).trans ⟨setCount_arrays _ _ _, rfl, rfl, rfl, rfl, rfl⟩
    generalize catMoveOn { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := st.d.setCount st.cat r.a } = r2 at hrel2 b1 b2 b3 b4 ha ⊢
    refine HStepOk.ofNext (hd := firstNext_down _ _ _ _) (hm := HMove.ofArr ha (firstNext_cap _ _ _ _)) b4 hrel2 (by rw [b3]; exact Nat.le_refl _) (by rw [b3]; exact hp) (fun F => ?_)
    have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
    rw [avail_mk, e, afterCat_eq, avail_mk, b1, b2, b3]
    rfl

/-! ### NPOSTFIX and NDIRECT -/

/-- Reads NPOSTFIX into `a` and the four bits of NDIRECT into `b`. -/
def npFast (b0 : BitBuffer) : Rd :=
  if 2 ≤ b0.count then
    let b1 := b0.drop 2
    if 4 ≤ b1.count then Rd.ok (b1.drop 4) (b0.peek 2) (b1.peek 4) 0 0 0 else Rd.short b0
  else Rd.short b0

private theorem not_le_lt' {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

theorem npFast_ok {b0 : BitBuffer} (hw : b0.Wf) :
    ROk (fun bs => readInt 2 bs >>= fun p => readInt 4 p.2 >>= fun q => some ((p.1, q.1), q.2)) b0 b0 6 (npFast b0)
      ((npFast b0).a.toNat, (npFast b0).b.toNat) := by
  unfold npFast
  by_cases h2 : 2 ≤ b0.count
  · rw [ite_eq_left h2]
    refine ROk.intOk (k := 2) (by decide) h2 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    generalize b0.drop 2 = b1 at hw1 ⊢
    by_cases h4 : 4 ≤ b1.count
    · rw [ite_eq_left h4]
      refine ROk.intOk (k := 4) (by decide) h4 ?_
      exact ROk.done (drop_wf' hw1 (by decide) h4) (fun f => rfl) _ _ _ _ _
    · rw [ite_eq_right h4]
      exact ROk.intShort (not_le_lt' h4) (by decide)
  · rw [ite_eq_right h2]
    exact ROk.intShort (not_le_lt' h2) (by decide)

/-- The place at NPOSTFIX and NDIRECT. -/
def stepHNp (st : Hd) (pos : USize) : Hd :=
  let r := npFast ⟨st.word, st.count⟩
  match r.status with
  | .short => markH st pos .needsInput
  | .bad => markH st pos .bad
  | .ok =>
    { st with
      word := r.word, count := r.count, pos := pos, status := .next, tag := .modes, idx := 0, left := st.d.nL
      fill := zeroBytes st.d.nL.toNat
      d := { st.d with npostfix := r.a, ndirect := r.b <<< r.a } }

/-- NPOSTFIX and NDIRECT settled move the stage on. -/
theorem Upto.npDone {d : Done} {g : Gh} (h : Upto d g 3) {x y : UInt64} {u v : Nat} (hx : x.toNat = u) (hy : y.toNat = v) (hu : u ≤ 3)
    (hv : v ≤ 120) : Upto { d with npostfix := x, ndirect := y } { g with m := { g.m with npostfix := u, ndirect := v } } 4 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := ⟨hx, hy, hu, hv⟩
  modes h := absurd h (by omega)
  lmap h := absurd h (by omega)
  dmap h := absurd h (by omega)
  codes _ h := absurd h (by omega)

theorem stepHNp_ok {st : Hd} {g : Gh} {pos : USize} (hrel : HRel st g .np) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) : HStepOk K a stop g .np st pos (stepHNp st pos) := by
  obtain ⟨hw, hu, ht⟩ := hrel
  have hrel : HRel st g .np := ⟨hw, hu, ht⟩
  have R := npFast_ok hw
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g .np) (N := fun v b =>
    hrest K { g with m := { g.m with npostfix := v.1, ndirect := v.2 <<< v.1 } } (.modes [] g.m.literal.n) b) (fun bs => by
      rw [hrest_np]
      cases readInt 2 bs with
      | none => rfl
      | some p =>
        show (readInt 4 p.2 >>= _) = (readInt 4 p.2 >>= _) >>= _
        cases readInt 4 p.2 with
        | none => rfl
        | some q => rfl)
  have hval := R.ok
  unfold stepHNp
  dsimp only
  generalize npFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    exact HStepOk.ofShortRead (X := 6) hrel hfull (by omega) h3 h4
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hnil := (hval hs).2 []
    have hv : r.a.toNat < 4 ∧ r.b.toNat < 16 := by
      cases hr : readInt 2 ((BitBuffer.mk st.word st.count).held ++ []) with
      | none =>
        rw [hr] at hnil
        cases hnil
      | some p =>
        rw [hr] at hnil
        have h1 : p.1 < 2 ^ 2 := readInt_lt 2 _ p.1 p.2 hr
        cases hr2 : readInt 4 p.2 with
        | none =>
          have : (some p >>= fun p => readInt 4 p.2 >>= fun q => some ((p.1, q.1), q.2)) = none := by
            show (readInt 4 p.2 >>= _) = none
            rw [hr2]
            rfl
          rw [this] at hnil
          cases hnil
        | some q =>
          have h2 : q.1 < 2 ^ 4 := readInt_lt 4 _ q.1 q.2 hr2
          have : (some p >>= fun p => readInt 4 p.2 >>= fun q => some ((p.1, q.1), q.2)) = some ((p.1, q.1), q.2) := by
            show (readInt 4 p.2 >>= _) = _
            rw [hr2]
            rfl
          rw [this] at hnil
          simp only [Option.some.injEq, Prod.mk.injEq] at hnil
          have e1 := hnil.1.1
          have e2 := hnil.1.2
          omega
    have hA : r.a.toNat < 64 := by omega
    have hshift : (r.b <<< r.a).toNat = r.b.toNat <<< r.a.toNat := by
      have key : ∀ x < 4, ∀ y < 16, y <<< x ≤ 120 := by decide
      have := key _ hv.1 _ hv.2
      rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hA]
      exact Nat.mod_eq_of_lt (by omega)
    have hnd : r.b.toNat <<< r.a.toNat ≤ 120 := by
      have key : ∀ x < 4, ∀ y < 16, y <<< x ≤ 120 := by decide
      exact key _ hv.1 _ hv.2
    have hcL := hu.cat .L (by decide)
    have hwfL : g.m.literal.n ≤ 256 := hcL.wf.2.1
    have hnL : st.d.nL.toNat = g.m.literal.n := hcL.n
    have hfs : (zeroBytes st.d.nL.toNat).size ≤ 16384 := by
      rw [zeroBytes_size (by omega)]
      omega
    refine HStepOk.ofNext (g' := { g with m := { g.m with npostfix := r.a.toNat, ndirect := r.b.toNat <<< r.a.toNat } })
      (p' := .modes [] g.m.literal.n) (hm := ⟨rfl, rfl, fun h => ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
        by simp only [capH, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩) rfl ⟨hw2, hu.npDone rfl hshift (by omega) hnd, rfl, rfl, hnL, by simp, ?_, by simp, by simp⟩
      (Nat.le_refl _) hp (fun F => ?_)
    · show (zeroBytes st.d.nL.toNat).size = g.m.literal.n
      rw [zeroBytes_size (by omega), hnL]
    · have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      rfl

/-! ### The context modes -/

/-- The place in the context modes. -/
def stepHModes (st : Hd) (pos : USize) : Hd :=
  let left := st.left
  if left = 0 then
    let fill := st.fill
    { st with pos := pos, status := .next, tag := .trees, isL := true, d := { st.d with modes := fill } }
  else if 2 ≤ st.count then
    let b : BitBuffer := ⟨st.word, st.count⟩
    let idx := st.idx
    let fill := st.fill
    let st0 := clearFill st
    let b1 := b.drop 2
    { st0 with
      word := b1.word, count := b1.count, pos := pos, status := .next, idx := idx + 1, left := left - 1
      fill := setU fill idx.toUSize (b.peek 2).toUInt8 }
  else markH st pos .needsInput

/-- The context modes settled move the stage on. -/
theorem Upto.modesDone {d : Done} {g : Gh} (h : Upto d g 4) {b : ByteArray} {l : List Nat} (hm : MapOk b l g.m.literal.n 4) :
    Upto { d with modes := b } { g with m := { g.m with contextModes := l } } 5 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := hm
  lmap h := absurd h (by omega)
  dmap h := absurd h (by omega)
  codes _ h := absurd h (by omega)

theorem stepHModes_ok {done : List Nat} {left : Nat} {st : Hd} {g : Gh} {pos : USize} (hrel : HRel st g (.modes done left))
    (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.modes done left) st pos (stepHModes st pos) := by
  obtain ⟨hw, hu, ht, hidx, hleft, hlen, hsize, hlt, hat⟩ := hrel
  have hrel : HRel st g (.modes done left) := ⟨hw, hu, ht, hidx, hleft, hlen, hsize, hlt, hat⟩
  have hcL := hu.cat .L (by show 0 < 4; omega)
  have h256 : g.m.literal.n ≤ 256 := hcL.wf.2.1
  unfold stepHModes
  dsimp only
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    have hl0 : left = 0 := by
      rw [← hleft, h0]
      rfl
    subst hl0
    have hmap : MapOk st.fill done g.m.literal.n 4 := ⟨hsize, by omega, fun i hi => hat i (by omega), hlt⟩
    refine HStepOk.ofNext (g' := { g with m := { g.m with contextModes := done } }) (p' := .trees true)
      (hm := ⟨rfl, rfl, fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, by show st.fill.size ≤ 256; rw [hsize]; exact h256, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
        by simp only [capH, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩) rfl
      ⟨hw, hu.modesDone hmap, rfl, rfl⟩ (Nat.le_refl _) hp (fun F => ?_)
    exact hrest_modes_zero K g done _
  rw [ite_eq_right h0]
  have hl0 : st.left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
  obtain ⟨n, rfl⟩ : ∃ n, left = n + 1 := ⟨left - 1, by omega⟩
  by_cases h2 : 2 ≤ st.count
  · rw [ite_eq_left h2]
    have hread := fun f => read_int (b := ⟨st.word, st.count⟩) (k := 2) f (by decide) h2
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    have hvlt : ((BitBuffer.mk st.word st.count).peek 2).toNat < 4 := peek_lt _ (k := 2) (by decide)
    generalize hb1 : (BitBuffer.mk st.word st.count).drop 2 = b1 at hread hw1
    generalize (BitBuffer.mk st.word st.count).peek 2 = v at hread hvlt
    have hus : st.idx.toUSize.toNat = done.length := by
      rw [word_toUSize (by omega), hidx]
    have hi1 : (st.idx + 1).toNat = done.length + 1 := by
      rw [UInt64.toNat_add, hidx, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hl1 : (st.left - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hleft]
      rfl
    have hbyte : v.toUInt8.toNat = v.toNat := by
      rw [UInt64.toNat_toUInt8]
      omega
    have hsz' : (setU st.fill st.idx.toUSize v.toUInt8).size = g.m.literal.n := by rw [size_setU]; exact hsize
    refine HStepOk.ofNext (g' := g) (p' := .modes (done ++ [v.toNat]) n) (hd := Or.inl (Or.inr ⟨rfl, Nat.lt_succ_self n⟩))
      (hm := ⟨rfl, rfl, fun h => ⟨by show (setU st.fill st.idx.toUSize v.toUInt8).size ≤ 16384; rw [hsz']; omega, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
        by simp only [capH, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩) rfl
      ⟨hw1, hu, ht, by simpa using hi1, hl1, by simp only [List.length_append, List.length_singleton]; omega, hsz', ?_, ?_⟩
      (Nat.le_refl _) hp (fun F => ?_)
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact hlt x h
      · rw [List.mem_singleton.mp h]
        omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      by_cases he : i = done.length
      · subst he
        have hget := setU_get_same (t := st.fill) (i := st.idx.toUSize) (v := v.toUInt8) (by rw [hus, hsize]; omega)
        rw [hus] at hget
        simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        show some v.toNat = some _
        rw [hget, hbyte]
      · have hlt' : i < done.length := by omega
        rw [List.getElem?_append_left hlt', hat i hlt']
        have hget := setU_get_ne (t := st.fill) (i := st.idx.toUSize) (v := v.toUInt8) (j := i) (by rw [hus]; exact he)
        show _ = some (((setU st.fill st.idx.toUSize v.toUInt8).data[i]?).getD 0).toNat
        rw [hget]
    · show hrest K g (.modes done (n + 1)) _ = hrest K g (.modes (done ++ [v.toNat]) n) _
      rw [avail_mk, hrest_modes_succ, show readInt 2 ((BitBuffer.mk st.word st.count).held ++
        (chunkBits a pos.toNat stop.toNat ++ F)) = _ from hread _]
      rfl
  · rw [ite_eq_right h2]
    have hc : st.count.toNat < 2 := not_le_lt' h2
    have hnone : hrest K g (.modes done (n + 1)) (BitBuffer.mk st.word st.count).held = none := by
      rw [hrest_modes_succ, readInt_short (b := ⟨st.word, st.count⟩) hc]
      rfl
    exact HStepOk.ofShortRead (X := 2) hrel hfull (by omega) hc hnone

end

end Brotli.Decoder
