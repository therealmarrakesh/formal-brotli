import Brotli.Decoder.StreamCall

/-!
# The limit changes nothing but whether the decoder stops

The decoder reads the memory limit only where it checks it: the room left for the window at WBITS, and the room left for a
header's tables when the groups' tables are reserved. Everywhere else a state's limit, and its header's table room, are
carried along unread.
So two states that differ only in those two fields step alike, until one of them reports the limit.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### A header's table room -/

/-- A header machine's state with another table room. -/
def hdSet (st : Hd) (a : UInt64) : Hd := { st with d := { st.d with arenaMax := a } }

theorem setN_am (d : Done) (a : UInt64) (i : Cat) (n : UInt64) :
    ({ d with arenaMax := a } : Done).setN i n = { d.setN i n with arenaMax := a } := by
  cases i <;> rfl

theorem setCount_am (d : Done) (a : UInt64) (i : Cat) (n : UInt64) :
    ({ d with arenaMax := a } : Done).setCount i n = { d.setCount i n with arenaMax := a } := by
  cases i <;> rfl

theorem setBaseT_am (d : Done) (a : UInt64) (i : Cat) (b : USize) :
    ({ d with arenaMax := a } : Done).setBaseT i b = { d.setBaseT i b with arenaMax := a } := by
  cases i <;> rfl

theorem setBaseC_am (d : Done) (a : UInt64) (i : Cat) (b : USize) :
    ({ d with arenaMax := a } : Done).setBaseC i b = { d.setBaseC i b with arenaMax := a } := by
  cases i <;> rfl

theorem setBases_am (d : Done) (a : UInt64) (k : CK) (b : ByteArray) :
    ({ d with arenaMax := a } : Done).setBases k b = { d.setBases k b with arenaMax := a } := by
  cases k <;> rfl

theorem nOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).nOf i = d.nOf i := by
  cases i <;> rfl

theorem countOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).countOf i = d.countOf i := by
  cases i <;> rfl

theorem baseTOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).baseTOf i = d.baseTOf i := by
  cases i <;> rfl

theorem baseCOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).baseCOf i = d.baseCOf i := by
  cases i <;> rfl

theorem basesOf_am (d : Done) (a : UInt64) (k : CK) : ({ d with arenaMax := a } : Done).basesOf k = d.basesOf k := by
  cases k <;> rfl

/-- Settles a step that neither reads nor sets the table room: split every branch, and match the two sides. -/
macro "lim_tac" : tactic =>
  `(tactic| ((repeat' split) <;> (try simp_all [hdSet, setN_am, setCount_am, setBaseT_am, setBaseC_am, setBases_am, nOf_am,
    countOf_am, baseTOf_am, baseCOf_am, basesOf_am]) <;> (try rfl)))

/-- What two header steps from states that differ only in their table room leave: one of them ran out of room, or they
again differ only in their table room. -/
def HLim (r1 r2 : Hd) : Prop := r1.status = .memory ∨ r2.status = .memory ∨ ∃ a, r1 = hdSet r2 a

theorem HLim.same {r1 r2 : Hd} {a : UInt64} (h : r1 = hdSet r2 a) : HLim r1 r2 := Or.inr (Or.inr ⟨a, h⟩)

section
variable (st : Hd) (a : UInt64) (pos : USize)

theorem catMoveOn_lim : catMoveOn (hdSet st a) = hdSet (catMoveOn st) a := by
  simp only [catMoveOn]; lim_tac

theorem ckFinish_lim : ckFinish (hdSet st a) = hdSet (ckFinish st) a := by
  simp only [ckFinish]; lim_tac

theorem installTable_lim (base : UInt64) : installTable (hdSet st a) base = hdSet (installTable st base) a := by
  simp only [installTable, clearFill]; lim_tac

theorem clFinish_lim : clFinish (hdSet st a) = hdSet (clFinish st) a := by
  show clFinish { st with d := { st.d with arenaMax := a } } = _
  simp only [clFinish, clTable]; lim_tac

theorem mapTableDone_lim (t : ByteArray) : mapTableDone (hdSet st a) t = hdSet (mapTableDone st t) a := by
  simp only [mapTableDone, mapSizeFast]; lim_tac

theorem growSingle_lim (sym : UInt64) : growSingle (hdSet st a) sym = hdSet (growSingle st sym) a := by
  simp only [growSingle, clearDone, clearArena, hdSet]

theorem growPlanned_lim (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (p : Plan) :
    growPlanned (hdSet st a) lens n hn p = hdSet (growPlanned st lens n hn p) a := by
  simp only [growPlanned, clearDone, clearArena, hdSet]

/-- Two checks of the room that may disagree: the states agree when both pass, and a failed one reports the limit. -/
private theorem check_lim {c1 c2 : Prop} [Decidable c1] [Decidable c2] {x1 x2 y1 y2 : Hd} (h : c1 → c2 → x1 = hdSet x2 a)
    (hy1 : y1.status = .memory) (hy2 : y2.status = .memory) : HLim (if c1 then x1 else y1) (if c2 then x2 else y2) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp only [h1, h2, ↓reduceIte]
  · exact HLim.same (h h1 h2)
  · exact Or.inr (Or.inl hy2)
  · exact Or.inl hy1
  · exact Or.inl hy1

theorem mapFinish_lim (n : UInt64) (map : ByteArray) : HLim (mapFinish (hdSet st a) n map) (mapFinish st n map) := by
  unfold mapFinish
  rw [show (hdSet st a).isL = st.isL from rfl]
  cases st.isL with
  | true => exact HLim.same (a := a) rfl
  | false =>
    dsimp only
    exact check_lim a (fun _ _ => rfl) rfl rfl

theorem mapFinish_lim' {L : Hd} (h : L = hdSet st a) (n : UInt64) (map map' : ByteArray) (hm : map = map') :
    HLim (mapFinish L n map) (mapFinish st n map') := h ▸ hm ▸ mapFinish_lim st a n map

theorem tableDone_lim (single : Bool) (sym : UInt64) : HLim (tableDone (hdSet st a) single sym) (tableDone st single sym) := by
  unfold tableDone
  have er : (hdSet st a).role = st.role := rfl
  have es : (hdSet st a).size = st.size := rfl
  have el : (hdSet st a).lens = st.lens := rfl
  have ea : (hdSet st a).d.arena = st.d.arena := rfl
  have em : (hdSet st a).d.arenaCap = st.d.arenaCap := rfl
  simp only [er, es, el, ea, em]
  by_cases hn : st.size.toUSize.toNat ≤ st.lens.size
  · rw [dite_eq_left hn, dite_eq_left hn]
    cases hr : st.role with
    | map => dsimp only; exact HLim.same (mapTableDone_lim st a _)
    | type | count | codes =>
      dsimp only
      cases single with
      | true =>
        simp only [↓reduceIte]
        refine check_lim a (fun _ _ => ?_) ?_ ?_
        · rw [growSingle_lim, installTable_lim]
        · rfl
        · rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine check_lim a (fun _ _ => ?_) ?_ ?_
        · rw [growPlanned_lim, installTable_lim]
        · rfl
        · rfl
  · rw [dite_eq_right hn, dite_eq_right hn]
    exact HLim.same (a := a) rfl

theorem stepHCat_lim : stepHCat (hdSet st a) pos = hdSet (stepHCat st pos) a := by
  simp only [stepHCat, markH, catMoveOn]; lim_tac

theorem stepHFirst_lim : stepHFirst (hdSet st a) pos = hdSet (stepHFirst st pos) a := by
  show stepHFirst { st with d := { st.d with arenaMax := a } } pos = _
  simp only [stepHFirst, markH, catMoveOn, baseCOf_am]; lim_tac

theorem stepHNp_lim : stepHNp (hdSet st a) pos = hdSet (stepHNp st pos) a := by
  simp only [stepHNp, markH]; lim_tac

theorem stepHModes_lim : stepHModes (hdSet st a) pos = hdSet (stepHModes st pos) a := by
  simp only [stepHModes, markH, clearFill]; lim_tac

theorem stepHTrees_lim : HLim (stepHTrees (hdSet st a) pos) (stepHTrees st pos) := by
  show HLim (stepHTrees { st with d := { st.d with arenaMax := a } } pos) _
  simp only [stepHTrees, markH]
  (repeat' split) <;> first | exact mapFinish_lim' _ a (by rfl) _ _ _ (by rfl) | exact HLim.same (a := a) (by rfl) | contradiction | (simp_all [hdSet]; done)

theorem stepHRlemax_lim : stepHRlemax (hdSet st a) pos = hdSet (stepHRlemax st pos) a := by
  simp only [stepHRlemax, markH]; lim_tac

theorem stepHVals_lim : stepHVals (hdSet st a) pos = hdSet (stepHVals st pos) a := by
  simp only [stepHVals, markH, clearMap]; lim_tac

theorem stepHImtf_lim : HLim (stepHImtf (hdSet st a) pos) (stepHImtf st pos) := by
  show HLim (stepHImtf { st with d := { st.d with arenaMax := a } } pos) _
  simp only [stepHImtf, markH, clearMap]
  (repeat' split) <;> first | exact mapFinish_lim' _ a (by rfl) _ _ _ (by rfl) | exact HLim.same (a := a) (by rfl) | contradiction | (simp_all [hdSet]; done)

theorem stepHCodes_lim : stepHCodes (hdSet st a) pos = hdSet (stepHCodes st pos) a := by
  simp only [stepHCodes, ckFinish, ckSizeFast]; lim_tac

theorem clFinish_lim' {L : Hd} (h : L = hdSet st a) : clFinish L = hdSet (clFinish st) a := h ▸ clFinish_lim st a

theorem tableDone_lim' {L : Hd} (h : L = hdSet st a) (single : Bool) (sym : UInt64) :
    HLim (tableDone L single sym) (tableDone st single sym) := h ▸ tableDone_lim st a single sym

theorem stepHClens_lim : stepHClens (hdSet st a) pos = hdSet (stepHClens st pos) a := by
  show stepHClens { st with d := { st.d with arenaMax := a } } pos = _
  simp only [stepHClens, markH, clearClLens]
  (repeat' split) <;> first | exact clFinish_lim' _ a (by rfl) | rfl | (simp_all [hdSet]; done)

theorem stepHCode_lim : HLim (stepHCode (hdSet st a) pos) (stepHCode st pos) := by
  show HLim (stepHCode { st with d := { st.d with arenaMax := a } } pos) _
  simp only [stepHCode, markH]
  (repeat' split) <;> first | exact tableDone_lim' _ a (by rfl) _ _ | exact HLim.same (a := a) (by rfl) | (simp_all [hdSet]; done)

theorem stepHSyms_lim : HLim (stepHSyms (hdSet st a) pos) (stepHSyms st pos) := by
  show HLim (stepHSyms { st with d := { st.d with arenaMax := a } } pos) _
  unfold stepHSyms
  by_cases h1 : st.symSum = 32768
  · rw [ite_eq_left h1, ite_eq_left h1]
    exact tableDone_lim' _ a (by rfl) _ _
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : st.ln = st.size
    · rw [ite_eq_left h2, ite_eq_left h2]
      exact HLim.same (a := a) rfl
    · rw [ite_eq_right h2, ite_eq_right h2]
      refine HLim.same (a := a) ?_
      simp only [markH, clearLens]
      lim_tac

theorem stepAtH_lim : HLim (stepAtH (hdSet st a) pos) (stepAtH st pos) := by
  unfold stepAtH
  rw [show (hdSet st a).tag = st.tag from rfl]
  cases st.tag with
  | cat => exact HLim.same (stepHCat_lim st a pos)
  | code => exact stepHCode_lim st a pos
  | clens => exact HLim.same (stepHClens_lim st a pos)
  | syms => exact stepHSyms_lim st a pos
  | first => exact HLim.same (stepHFirst_lim st a pos)
  | np => exact HLim.same (stepHNp_lim st a pos)
  | modes => exact HLim.same (stepHModes_lim st a pos)
  | trees => exact stepHTrees_lim st a pos
  | rlemax => exact HLim.same (stepHRlemax_lim st a pos)
  | vals => exact HLim.same (stepHVals_lim st a pos)
  | imtf => exact stepHImtf_lim st a pos
  | codes => exact HLim.same (stepHCodes_lim st a pos)
  | ready => exact HLim.same (a := a) rfl

theorem stepAtH_lim' {L : Hd} (h : L = hdSet st a) : HLim (stepAtH L pos) (stepAtH st pos) := h ▸ stepAtH_lim st a pos

theorem stepH_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) :
    HLim (stepH ar stop hs (hdSet st a) pos) (stepH ar stop hs st pos) := by
  unfold stepH
  by_cases hp : pos ≤ stop
  · rw [dite_eq_left hp, dite_eq_left hp]
    exact stepAtH_lim' _ a _ (by rfl)
  · rw [dite_eq_right hp, dite_eq_right hp]
    exact HLim.same (a := a) rfl

end

/-! ### A stream's limit -/

/-- A stream state with another limit and table room. -/
def decSet (D : Dec) (l a : UInt64) : Dec := { D with limit := l, hd := hdSet D.hd a }

/-- What two stream steps from states that differ only in their limit and table room leave: one of them reports the limit,
or they again differ only in those. -/
def DLim (r1 r2 : Dec) : Prop := r1.status = .memory ∨ r2.status = .memory ∨ ∃ l a, r1 = decSet r2 l a

theorem DLim.same {r1 r2 : Dec} {l a : UInt64} (h : r1 = decSet r2 l a) : DLim r1 r2 := Or.inr (Or.inr ⟨l, a, h⟩)

section
variable (D : Dec) (l a : UInt64) (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) (pos : USize)

theorem stepDSkip_lim : stepDSkip stop (decSet D l a) pos = decSet (stepDSkip stop D pos) l a := by
  show stepDSkip stop { D with limit := l, hd := hdSet D.hd a } pos = _
  simp only [stepDSkip, moveOn]
  (repeat' split) <;> first | rfl | contradiction | (simp_all [decSet, hdSet]; done)

theorem stepDCmds_lim : stepDCmds ar stop hs (decSet D l a) pos = decSet (stepDCmds ar stop hs D pos) l a := by
  show stepDCmds ar stop hs { D with limit := l, hd := hdSet D.hd a } pos = _
  simp only [stepDCmds, takeCmd, clearCmd]
  (repeat' split) <;> first | rfl | contradiction | (simp_all [decSet, hdSet]; done) |
    (by_cases hc : seenOk (runCmd D.H D.k ar stop hs cmdBudget D.cmd pos).seen D.H.nL D.H.nI D.H.nD = true <;>
      simp only [hc, ↓reduceIte] <;> rfl)

theorem stepDRaw_lim : stepDRaw ar stop hs (decSet D l a) pos = decSet (stepDRaw ar stop hs D pos) l a := by
  show stepDRaw ar stop hs { D with limit := l, hd := hdSet D.hd a } pos = _
  simp only [stepDRaw, takeRing, moveOn, clearCmd, rawFinish]
  (repeat' split) <;> first | rfl | contradiction | (simp_all [decSet, hdSet]; done)

theorem stepDMeta_lim : DLim (stepDMeta ar stop hs (decSet D l a) pos) (stepDMeta ar stop hs D pos) := by
  show DLim (stepDMeta ar stop hs { D with limit := l, hd := hdSet D.hd a } pos) _
  simp only [stepDMeta, metaGo]
  (repeat' split) <;>
    first | exact DLim.same (l := l) (a := a) (by rfl) | exact DLim.same (l := l) (a := l) (by rfl) | contradiction | (simp_all [decSet, hdSet]; done)

theorem stepDWbits_lim : DLim (stepDWbits ar stop hs (decSet D l a) pos) (stepDWbits ar stop hs D pos) := by
  show DLim (stepDWbits ar stop hs { D with limit := l, hd := hdSet D.hd a } pos) _
  unfold stepDWbits
  by_cases hp : pos ≤ stop
  · rw [dite_eq_left hp, dite_eq_left hp]
    dsimp only
    split
    · exact DLim.same (l := l) (a := a) (by rfl)
    · exact DLim.same (l := l) (a := a) (by rfl)
    · rename_i hok
      by_cases h1 : (1 : UInt64) <<< (wbitsFast ⟨(refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).word,
          (refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).count⟩).a ≤ l
      · rw [ite_eq_left h1]
        by_cases h2 : (1 : UInt64) <<< (wbitsFast ⟨(refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).word,
            (refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).count⟩).a ≤ D.limit
        · rw [ite_eq_left h2]
          exact DLim.same (l := l - (1 : UInt64) <<< (wbitsFast ⟨(refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).word,
            (refill D.cmd.word D.cmd.count ar pos stop hs (USize.le_iff_toNat_le.mp hp)).count⟩).a) (a := a) (by rfl)
        · rw [ite_eq_right h2]
          exact Or.inr (Or.inl rfl)
      · rw [ite_eq_right h1]
        exact Or.inl rfl
  · rw [dite_eq_right hp, dite_eq_right hp]
    exact DLim.same (l := l) (a := a) (by rfl)

theorem stepDHdr_lim (hH1 : ∃ g p, HRel (decSet D l a).hd g p) (hH2 : ∃ g p, HRel D.hd g p) (hp : pos.toNat ≤ stop.toNat) :
    DLim (stepDHdr ar stop hs (decSet D l a) pos hH1 hp) (stepDHdr ar stop hs D pos hH2 hp) := by
  unfold stepDHdr takeHd clearHd
  dsimp only
  have hr : HLim (stepH ar stop hs (decSet D l a).hd pos) (stepH ar stop hs D.hd pos) := stepH_lim D.hd a pos ar stop hs
  generalize e1 : stepHR ar stop hs (decSet D l a).hd pos hH1 hp = rr1
  generalize e2 : stepHR ar stop hs D.hd pos hH2 hp = rr2
  obtain ⟨r1, h1⟩ := rr1
  obtain ⟨r2, h2⟩ := rr2
  have v1 : r1 = stepH ar stop hs (decSet D l a).hd pos := by rw [← stepHR_val (h := hH1) (hp := hp), e1]
  have v2 : r2 = stepH ar stop hs D.hd pos := by rw [← stepHR_val (h := hH2) (hp := hp), e2]
  rw [← v1, ← v2] at hr
  unfold hdrNext
  dsimp only
  rcases hr with h | h | ⟨a', rfl⟩
  · exact Or.inl (by split <;> first | rfl | (rename_i s; exact absurd (h.symm.trans s) (fun e => HStatus.noConfusion e)))
  · exact Or.inr (Or.inl (by split <;> first | rfl | (rename_i s; exact absurd (h.symm.trans s) (fun e => HStatus.noConfusion e))))
  · split <;> rename_i s1 <;> split <;> rename_i s2 <;> first
      | exact absurd (s1.symm.trans s2) (fun e => HStatus.noConfusion e)
      | exact Or.inl rfl
      | exact DLim.same (l := l) (a := a') (by rfl)
      | exact DLim.same (l := l) (a := 0) (by rfl)

theorem stepD_lim (h1 : DInv stop (decSet D l a)) (h2 : DInv stop D) :
    DLim (stepD ar stop hs (decSet D l a) h1) (stepD ar stop hs D h2) := by
  cases ht : D.tag with
  | wbits =>
    rw [stepD_wbits (D := decSet D l a) ht, stepD_wbits ht]
    exact stepDWbits_lim D l a ar stop hs D.pos
  | mblock =>
    rw [stepD_mblock (D := decSet D l a) ht, stepD_mblock ht]
    exact stepDMeta_lim D l a ar stop hs D.pos
  | skip =>
    rw [stepD_skip (D := decSet D l a) ht, stepD_skip ht]
    exact DLim.same (stepDSkip_lim D l a stop D.pos)
  | raw =>
    rw [stepD_raw (D := decSet D l a) ht, stepD_raw ht]
    exact DLim.same (stepDRaw_lim D l a ar stop hs D.pos)
  | hdr =>
    rw [stepD_hdr (D := decSet D l a) ht, stepD_hdr ht]
    exact stepDHdr_lim D l a ar stop hs D.pos _ _ h2.2
  | cmds =>
    rw [stepD_cmds (D := decSet D l a) ht, stepD_cmds ht]
    exact DLim.same (stepDCmds_lim D l a ar stop hs D.pos)
  | ended =>
    rw [stepD_ended (D := decSet D l a) ht, stepD_ended ht]
    exact DLim.same (l := l) (a := a) rfl

end

/-- The loop from two states that differ only in their limit and table room. -/
theorem runD_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) : ∀ (x : RunArg ar stop hs) (l a : UInt64)
    (h1 : DInv stop (decSet x.D l a)), DLim (runD ar stop hs (decSet x.D l a) h1) (runD ar stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf ar stop hs).induction with
  | _ x ih =>
    intro l a h1
    rw [runD, runD]
    by_cases he : x.D.tag = .ended
    · rw [dite_eq_left (show (decSet x.D l a).tag = .ended from he), dite_eq_left he]
      exact DLim.same (l := l) (a := a) rfl
    · rw [dite_eq_right (show ¬ (decSet x.D l a).tag = .ended from he), dite_eq_right he]
      dsimp only
      have hs1 := stepD_lim x.D l a ar stop hs h1 x.inv
      rcases hs1 with h | h | ⟨l', a', e⟩
      · rw [dite_eq_right (show ¬ (stepD ar stop hs (decSet x.D l a) h1).status = .next by rw [h]; exact fun e => DStatus.noConfusion e)]
        exact Or.inl h
      · rw [dite_eq_right (show ¬ (stepD ar stop hs x.D x.inv).status = .next by rw [h]; exact fun e => DStatus.noConfusion e)]
        exact Or.inr (Or.inl h)
      · by_cases hn : (stepD ar stop hs x.D x.inv).status = .next
        · have hn1 : (stepD ar stop hs (decSet x.D l a) h1).status = .next := by rw [e]; exact hn
          rw [dite_eq_left hn1, dite_eq_left hn]
          have := ih ⟨stepD ar stop hs x.D x.inv, x.inv.step he hn⟩ ⟨he, hn, rfl⟩ l' a' (by rw [← e]; exact h1.step he hn1)
          simp only [e] at this ⊢
          exact this
        · have hn1 : ¬ (stepD ar stop hs (decSet x.D l a) h1).status = .next := by rw [e]; exact hn
          rw [dite_eq_right hn1, dite_eq_right hn]
          exact DLim.same e

/-- What two calls from states that differ only in their limit and table room leave, as a caller sees it. -/
def OLim (o1 o2 : Out) : Prop :=
  o1.status = .memoryLimit ∨ o2.status = .memoryLimit ∨
    (o1.status = o2.status ∧ o1.buf = o2.buf ∧ o1.pos = o2.pos ∧ ∃ l a, o1.D = decSet o2.D l a)

theorem OLim.same {o1 o2 : Out} {l a : UInt64} (hs : o1.status = o2.status) (hb : o1.buf = o2.buf) (hp : o1.pos = o2.pos)
    (hD : o1.D = decSet o2.D l a) : OLim o1 o2 := Or.inr (Or.inr ⟨hs, hb, hp, l, a, hD⟩)

theorem deadD_dec : deadD = decSet deadD 0 0 := rfl

theorem flushD_lim (D : Dec) (l a : UInt64) (buf : ByteArray) (space : Nat) :
    flushD (decSet D l a) buf space = ⟨decSet (flushD D buf space).D l a, (flushD D buf space).buf, (flushD D buf space).space⟩ := rfl

theorem endCheck_lim (D : Dec) (l a : UInt64) (stop : USize) (final : Bool) (buf : ByteArray) :
    OLim (endCheck (decSet D l a) stop final buf) (endCheck D stop final buf) := by
  show OLim (endCheck { D with limit := l, hd := hdSet D.hd a } stop final buf) _
  simp only [endCheck]
  (repeat' split) <;>
    first | exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl | exact OLim.same (l := l) (a := a) rfl rfl rfl rfl | contradiction |
      (simp_all [decSet, hdSet]; done)

theorem afterRun_lim {r1 r2 : Dec} (h : DLim r1 r2) (stop : USize) (final : Bool) (buf : ByteArray) (space : Nat) :
    OLim (afterRun r1 stop final buf space) (afterRun r2 stop final buf space) := by
  rcases h with h | h | ⟨l, a, rfl⟩
  · refine Or.inl ?_
    simp only [afterRun, h]
  · refine Or.inr (Or.inl ?_)
    simp only [afterRun, h]
  · unfold afterRun
    rw [show (decSet r2 l a).status = r2.status from rfl]
    cases r2.status with
    | bad => exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl
    | memory => exact Or.inl rfl
    | needsInput =>
      dsimp only
      rw [flushD_lim]
      dsimp only
      rw [show (decSet (flushD r2 buf space).D l a).cmd = (flushD r2 buf space).D.cmd from rfl]
      by_cases hp : (flushD r2 buf space).D.cmd.pend = 0
      · rw [ite_eq_left hp, ite_eq_left hp]
        cases final with
        | true => exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl
        | false => exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
      · rw [ite_eq_right hp, ite_eq_right hp]
        exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
    | next =>
      dsimp only
      rw [flushD_lim]
      dsimp only
      rw [show (decSet (flushD r2 buf space).D l a).cmd = (flushD r2 buf space).D.cmd from rfl]
      by_cases hp : (flushD r2 buf space).D.cmd.pend = 0
      · rw [ite_eq_left hp, ite_eq_left hp]
        exact endCheck_lim _ l a stop final _
      · rw [ite_eq_right hp, ite_eq_right hp]
        exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
    | needsOutput => exact OLim.same (l := l) (a := a) rfl rfl rfl rfl

/-- A call from two states that differ only in their limit and table room. -/
theorem callD_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) (final : Bool) : ∀ (space : Nat) (D2 : Dec)
    (h2 : DInv stop D2) (D1 : Dec) (h1 : DInv stop D1) (buf : ByteArray), (∃ l a, D1 = decSet D2 l a) →
    OLim (callD ar stop hs final D1 h1 buf space) (callD ar stop hs final D2 h2 buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h2 D1 h1 buf ⟨l, a, hD⟩
    subst hD
    rw [callD, callD]
    have hr : DLim (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space))
        (runD ar stop hs (withCap D space) (h2.withCap space)) :=
      runD_lim ar stop hs ⟨withCap D space, h2.withCap space⟩ l a (h1.withCap space)
    rcases hr with h | h | ⟨l', a', e⟩
    · rw [dite_eq_right (show ¬ (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput by rw [h]; exact fun e => DStatus.noConfusion e)]
      exact Or.inl (by simp only [afterRun, h])
    · rw [dite_eq_right (show ¬ (runD ar stop hs (withCap D space) (h2.withCap space)).status = .needsOutput by rw [h]; exact fun e => DStatus.noConfusion e)]
      refine Or.inr (Or.inl ?_)
      simp only [afterRun, h]
    · by_cases hn : (runD ar stop hs (withCap D space) (h2.withCap space)).status = .needsOutput
      · have hn1 : (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput := by rw [e]; exact hn
        rw [dite_eq_left hn1, dite_eq_left hn]
        dsimp only
        have hf : flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space =
            ⟨decSet (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D l' a', (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).buf,
              (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space⟩ := by
          rw [e, flushD_lim]
        have hp : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).D.cmd.pend = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D.cmd.pend := by
          rw [hf]; rfl
        have hsp : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).space = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space := by
          rw [hf]
        have hb : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).buf = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).buf := by
          rw [hf]
        have hDD : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).D = decSet (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D l' a' := by
          rw [hf]
        by_cases hq : (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D.cmd.pend = 0
        · rw [ite_eq_left hq, ite_eq_left (hp.trans hq)]
          by_cases hl : (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space < space
          · rw [dite_eq_left hl, dite_eq_left (hsp ▸ hl)]
            rw [hb, hsp]
            exact ih _ hl _ _ _ _ _ ⟨l', a', hDD⟩
          · rw [dite_eq_right hl, dite_eq_right (show ¬ _ from hsp ▸ hl)]
            exact OLim.same (l := 0) (a := 0) rfl hb rfl rfl
        · rw [ite_eq_right hq, ite_eq_right (show ¬ _ from hp ▸ hq)]
          exact OLim.same (l := l') (a := a') rfl hb (by rw [hDD]; rfl) hDD
      · have hn1 : ¬ (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput := by rw [e]; exact hn
        rw [dite_eq_right hn1, dite_eq_right hn]
        exact afterRun_lim (DLim.same e) stop final buf space
