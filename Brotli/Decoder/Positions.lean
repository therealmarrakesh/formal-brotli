import Brotli.Decoder.Loop
import Brotli.Decoder.HeaderDone

/-!
# Steps that only record the position

A step that reads no input only records the position it is given: its result is the same, but for that position, whatever
position it is given and whatever position its state held. Only the steps that refill, and the loops that read bytes, move
the position.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Splits the first branch in the goal, and takes the same branch wherever its condition recurs. -/
macro "split_all" : tactic => `(tactic| split <;> (try (rename_i hc; first
  | simp only [dite_eq_left hc, ite_eq_left hc] | simp only [dite_eq_right hc, ite_eq_right hc] | simp only [hc])))

theorem stepCommand_pos (H : Hdr) (st : Cmd) (p : USize) :
    stepCommand H st p = { stepCommand H { st with pos := 0 } 0 with pos := p } := by
  unfold stepCommand markStep clearSeen
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepInsertCopy_pos (H : Hdr) (st : Cmd) (p : USize) :
    stepInsertCopy H st p = { stepInsertCopy H { st with pos := 0 } 0 with pos := p } := by
  unfold stepInsertCopy insertStep markStep
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepCopyLength_pos (st : Cmd) (p : USize) :
    stepCopyLength st p = { stepCopyLength { st with pos := 0 } 0 with pos := p } := by
  unfold stepCopyLength markStep
  try dsimp only
  repeat' (first | split_all | rfl)

theorem applyBuilt_pos (st : Cmd) (p : USize) (word : ByteArray) :
    applyBuilt st p word = { applyBuilt { st with pos := 0 } 0 word with pos := p } := by
  unfold applyBuilt markStep
  try dsimp only
  repeat' (first | split_all | rfl)

theorem applyWord_pos (st : Cmd) (p : USize) (wordId : UInt64) :
    applyWord st p wordId = { applyWord { st with pos := 0 } 0 wordId with pos := p } := by
  unfold applyWord markStep
  simp only [applyBuilt_pos _ p]
  try dsimp only
  repeat' (first | split_all | rfl)

theorem applyDistance_pos (st : Cmd) (p : USize) (dcode d : UInt64) :
    applyDistance st p dcode d = { applyDistance { st with pos := 0 } 0 dcode d with pos := p } := by
  unfold applyDistance markStep
  simp only [applyWord_pos _ p]
  try dsimp only
  repeat' (first | split_all | rfl)

theorem distanceStep_pos (H : Hdr) (st : Cmd) (p : USize) (v : UInt64) :
    distanceStep H st p v = { distanceStep H { st with pos := 0 } 0 v with pos := p } := by
  unfold distanceStep markStep
  simp only [applyDistance_pos _ p]
  try dsimp only
  repeat' (first | split_all | rfl)

theorem distanceThrough_pos (H : Hdr) (st : Cmd) (p : USize) (tree : UInt8) (htree : tree.toNat < H.treesD.toNat) :
    distanceThrough H st p tree htree = { distanceThrough H { st with pos := 0 } 0 tree htree with pos := p } := by
  unfold distanceThrough
  simp only [distanceStep_pos _ _ p]

theorem stepDistance_pos (H : Hdr) (st : Cmd) (p : USize) :
    stepDistance H st p = { stepDistance H { st with pos := 0 } 0 with pos := p } := by
  unfold stepDistance markStep clearSeen
  simp only [applyDistance_pos _ p]
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepDistanceSymbol_pos (H : Hdr) (st : Cmd) (p : USize) :
    stepDistanceSymbol H st p = { stepDistanceSymbol H { st with pos := 0 } 0 with pos := p } := by
  unfold stepDistanceSymbol markStep
  simp only [distanceThrough_pos _ _ p]
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepCopy_pos (k : USize) (st : Cmd) (p : USize) :
    stepCopy k st p = { stepCopy k { st with pos := 0 } 0 with pos := p } := by
  unfold stepCopy finishCopy markStep
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepWord_pos (k : USize) (st : Cmd) (p : USize) :
    stepWord k st p = { stepWord k { st with pos := 0 } 0 with pos := p } := by
  unfold stepWord finishWord markStep
  try dsimp only
  repeat' (first | split_all | rfl)

/-! A helper on the header's state keeps the position its state holds. -/

/-- A finished code length code is finished at any position. -/
theorem clDone_pos {st : Hd} (h : ∃ acc, ClDone st acc) (q : USize) : ∃ acc, ClDone { st with pos := q } acc := by
  obtain ⟨acc, hd⟩ := h
  exact ⟨acc, { hd with }⟩

theorem clTable_pos (st : Hd) (q : USize) (h : ∃ acc, ClDone st acc) : clTable { st with pos := q } (clDone_pos h q) = clTable st h := rfl

theorem mapSizeFast_pos (st : Hd) (q : USize) : mapSizeFast { st with pos := q } = mapSizeFast st := rfl

theorem installTable_nf (st : Hd) (base : UInt64) (hi : InstallOk st.role st.idx st.fill) :
    installTable st base hi = { installTable { st with pos := 0 } base hi with pos := st.pos } := by
  have hr4 : st.role = .type ∨ st.role = .count ∨ st.role = .codes ∨ st.role = .map := by
    cases st.role <;> simp
  rcases hr4 with hr | hr | hr | hr
  · rw [installTable_type hr, installTable_type (st := { st with pos := 0 }) hr]
  · rw [installTable_count hr, installTable_count (st := { st with pos := 0 }) hr]
  · rw [installTable_codes hr, installTable_codes (st := { st with pos := 0 }) hr]; rfl
  · rw [installTable_map hr, installTable_map (st := { st with pos := 0 }) hr]

theorem growLens_nf (st : Hd) (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (h : LensArgs st.d.arena lens n) :
    growLens st lens n hn h = { growLens { st with pos := 0 } lens n hn h with pos := st.pos } := rfl

theorem growSingle_nf (st : Hd) (sym : UInt64) (h : st.d.arena.size + 4096 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0) :
    growSingle st sym h = { growSingle { st with pos := 0 } sym h with pos := st.pos } := rfl

theorem mapTableDone_nf (st : Hd) (t : ByteArray) (hf : t.size < 2 ^ 32 ∧ TableFits t (USize.ofNat 0).toNat) :
    mapTableDone st t hf = { mapTableDone { st with pos := 0 } t hf with pos := st.pos } := by
  unfold mapTableDone
  try dsimp only
  repeat' (first | split_all | rfl)

set_option maxRecDepth 8192 in
theorem tableDone_nf (st : Hd) (single : Bool) (sym : UInt64) (ha : TableArgs st.size st.lens single sym)
    (hi : InstallOk st.role st.idx st.fill) (har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 4096 < 2 ^ 32) :
    tableDone st single sym ha hi har = { tableDone { st with pos := 0 } single sym ha hi har with pos := st.pos } := by
  unfold tableDone
  cases st
  try dsimp only
  repeat' (first | split_all | exact (installTable_nf _ _ _).trans rfl | exact (mapTableDone_nf _ _ _).trans rfl | rfl)

theorem catMoveOn_nf (st : Hd) : catMoveOn st = { catMoveOn { st with pos := 0 } with pos := st.pos } := by
  unfold catMoveOn
  cases st
  try dsimp only
  repeat' (first | split_all | rfl)

theorem clFinish_nf (st : Hd) (h : ∃ acc, ClDone st acc) :
    clFinish st h = { clFinish { st with pos := 0 } (clDone_pos h 0) with pos := st.pos } := by
  unfold clFinish
  rfl

theorem mapFinish_nf (st : Hd) (n : UInt64) (map : ByteArray) :
    mapFinish st n map = { mapFinish { st with pos := 0 } n map with pos := st.pos } := by
  unfold mapFinish
  cases st
  try dsimp only
  repeat' (first | split_all | rfl)

theorem ckFinish_nf (st : Hd) : ckFinish st = { ckFinish { st with pos := 0 } with pos := st.pos } := by
  unfold ckFinish
  cases st
  try dsimp only
  repeat' (first | split_all | rfl)

/-- Closes the goals the steps on the header's state leave. -/
macro "hd_nf" : tactic => `(tactic| ((try unfold markH) <;> (try dsimp only) <;> (try simp only [clTable_pos, mapSizeFast_pos]) <;>
  repeat' (first
    | split_all
    | exact (installTable_nf _ _ _).trans rfl
    | exact (mapTableDone_nf _ _ _).trans rfl
    | exact (tableDone_nf _ _ _ _ _ _).trans rfl
    | exact (catMoveOn_nf _).trans rfl
    | exact (clFinish_nf _ _).trans rfl
    | exact (mapFinish_nf _ _ _).trans rfl
    | exact (ckFinish_nf _).trans rfl
    | rfl)))

theorem stepHCat_pos (st : Hd) (p : USize) : stepHCat st p = { stepHCat { st with pos := 0 } 0 with pos := p } := by
  unfold stepHCat
  cases st
  hd_nf

theorem stepHCode_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .code) :
    stepHCode st p h ht = { stepHCode { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  unfold stepHCode simpleFastT
  cases st
  hd_nf

theorem stepHClens_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .clens) :
    stepHClens st p h ht = { stepHClens { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  unfold stepHClens
  cases st
  hd_nf

set_option maxHeartbeats 2000000 in
theorem stepHSyms_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) :
    stepHSyms st p h ht = { stepHSyms { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  unfold stepHSyms
  by_cases h0 : st.symSum = 32768
  · rw [dite_eq_left h0, dite_eq_left (show ({ st with pos := 0 } : Hd).symSum = 32768 from h0)]
    exact (tableDone_nf _ _ _ _ _ _).trans rfl
  · rw [dite_eq_right h0, dite_eq_right (show ¬ ({ st with pos := 0 } : Hd).symSum = 32768 from h0)]
    cases st
    hd_nf

theorem stepHFirst_pos (st : Hd) (p : USize) (hf : st.d.arena.size < 2 ^ 32 ∧ TableFits st.d.arena (st.d.baseCOf st.cat).toNat) :
    stepHFirst st p hf = { stepHFirst { st with pos := 0 } 0 hf with pos := p } := by
  unfold stepHFirst
  cases st
  hd_nf

theorem stepHNp_pos (st : Hd) (p : USize) : stepHNp st p = { stepHNp { st with pos := 0 } 0 with pos := p } := by
  unfold stepHNp
  cases st
  hd_nf

theorem stepHModes_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .modes) :
    stepHModes st p h ht = { stepHModes { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  unfold stepHModes
  cases st
  hd_nf

theorem stepHTrees_pos (st : Hd) (p : USize) : stepHTrees st p = { stepHTrees { st with pos := 0 } 0 with pos := p } := by
  unfold stepHTrees
  cases st
  hd_nf

theorem stepHRlemax_pos (st : Hd) (p : USize) : stepHRlemax st p = { stepHRlemax { st with pos := 0 } 0 with pos := p } := by
  unfold stepHRlemax
  cases st
  hd_nf

theorem stepHVals_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .vals) :
    stepHVals st p h ht = { stepHVals { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  have e : mapSymFastT { st with pos := 0 } (hrel_pos0 h) ht = mapSymFastT st h ht := rfl
  unfold stepHVals
  rw [e]
  generalize mapSymFastT st h ht = rr
  obtain ⟨⟨rs, rw, rc, ra, rb, rcc, rd, re⟩, hr⟩ := rr
  cases st
  cases rs <;> (try unfold markH) <;> (try dsimp only) <;>
    repeat' (first | split_all | contradiction | rfl | (simp only [clearMap]; done))

theorem stepHImtf_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .imtf) :
    stepHImtf st p h ht = { stepHImtf { st with pos := 0 } 0 (hrel_pos0 h) ht with pos := p } := by
  unfold stepHImtf
  cases st
  hd_nf

theorem stepHCodes_pos (st : Hd) (p : USize) : stepHCodes st p = { stepHCodes { st with pos := 0 } 0 with pos := p } := by
  unfold stepHCodes
  cases st
  hd_nf

theorem stepAtH_pos (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) :
    stepAtH st p h = { stepAtH { st with pos := 0 } 0 (hrel_pos0 h) with pos := p } := by
  unfold stepAtH
  cases st
  dsimp only
  split
  · exact (stepHCat_pos _ _).trans rfl
  · exact (stepHCode_pos _ _ _ _).trans rfl
  · exact (stepHClens_pos _ _ _ _).trans rfl
  · exact (stepHSyms_pos _ _ _ _).trans rfl
  · exact (stepHFirst_pos _ _ _).trans rfl
  · exact (stepHNp_pos _ _).trans rfl
  · exact (stepHModes_pos _ _ _ _).trans rfl
  · exact (stepHTrees_pos _ _).trans rfl
  · exact (stepHRlemax_pos _ _).trans rfl
  · exact (stepHVals_pos _ _ _ _).trans rfl
  · exact (stepHImtf_pos _ _ _ _).trans rfl
  · exact (stepHCodes_pos _ _).trans rfl
  · rfl

/-! ### Where a command step that rejects decides

A step rejects on the bits it holds once its refill is done: the step after the refill reads no further, so the rejection
stands whatever follows the bytes the refill took. -/

/-- A literal step that rejects does so before its loop reads anything, so where the chunk stops doesn't matter to it. -/
theorem stepLiterals_bad {H : Hdr} {k : USize} {a : ByteArray} {stop stop' : USize} {hs : stop.toNat ≤ a.size}
    (hs' : stop'.toNat ≤ a.size) {st : Cmd} {pos : USize} (hp : pos ≤ stop)
    (hb : (stepLiterals H k a stop hs st pos).status = .bad) :
    stepLiterals H k a stop hs st pos = stepLiterals H k a stop' hs' st pos ∧ (stepLiterals H k a stop hs st pos).pos = pos := by
  have hfin : ∀ (st0 : Cmd) (r : LitRun) (run size : USize), (finishLiterals st0 r run size).status ≠ .bad := by
    intro st0 r run size
    unfold finishLiterals
    dsimp only
    split <;> exact fun e => StepStatus.noConfusion e
  unfold stepLiterals at hb ⊢
  by_cases h0 : st.left = 0
  · simp only [h0, ↓reduceIte] at hb
    exact absurd hb (fun e => StepStatus.noConfusion e)
  simp only [h0, ↓reduceIte] at hb ⊢
  by_cases h1 : st.lCount = 0
  · simp only [h1, ↓reduceIte] at hb ⊢
    refine ⟨by first | rfl | trivial, ?_⟩
    repeat' split
    all_goals rfl
  simp only [h1, ↓reduceIte] at hb ⊢
  by_cases h2 : room k st.cap ≤ st.pend
  · simp only [h2, ↓reduceIte] at hb
    exact absurd hb (fun e => StepStatus.noConfusion e)
  simp only [h2, ↓reduceIte] at hb ⊢
  unfold literalsRun at hb ⊢
  by_cases ht : st.lCur < H.nL
  · rw [dite_eq_left ht] at hb ⊢
    rw [dite_eq_left ht]
    by_cases hw : winCheck k st.wpos st.ring = true ∧ wfCheck st.word st.count = true
    · rw [dite_eq_left ⟨hw.1, hp, hw.2⟩] at hb
      exact absurd hb (hfin _ _ _ _)
    · have n1 : ¬ (winCheck k st.wpos st.ring = true ∧ pos ≤ stop ∧ wfCheck st.word st.count = true) :=
        fun e => hw ⟨e.1, e.2.2⟩
      have n2 : ¬ (winCheck k st.wpos st.ring = true ∧ pos ≤ stop' ∧ wfCheck st.word st.count = true) :=
        fun e => hw ⟨e.1, e.2.2⟩
      rw [dite_eq_right n1, dite_eq_right n2]
      exact ⟨rfl, rfl⟩
  · rw [dite_eq_right ht, dite_eq_right ht]
    exact ⟨rfl, rfl⟩

/-- A step of the command loop's places that rejects stands where it was put, and does the same wherever the chunk stops. -/
theorem stepAt_bad {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hp : pos ≤ stop) (hb : (stepAt H k a stop hs st pos).status = .bad) :
    stepAt H k a stop hs st pos = stepAt H k a pos (Nat.le_trans (USize.le_iff_toNat_le.mp hp) hs) st pos ∧
      (stepAt H k a stop hs st pos).pos = pos := by
  unfold stepAt at hb ⊢
  cases ht : st.tag with
  | command => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepCommand_pos H st pos)).trans rfl⟩
  | insertCopy => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepInsertCopy_pos H st pos)).trans rfl⟩
  | copyLength => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepCopyLength_pos st pos)).trans rfl⟩
  | literals =>
    simp only [ht] at hb ⊢
    exact stepLiterals_bad _ hp hb
  | distance => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepDistance_pos H st pos)).trans rfl⟩
  | distanceSymbol => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepDistanceSymbol_pos H st pos)).trans rfl⟩
  | copy => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepCopy_pos k st pos)).trans rfl⟩
  | word => simp only [ht] at hb ⊢; exact ⟨trivial, (congrArg Cmd.pos (stepWord_pos k st pos)).trans rfl⟩

section
variable {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
  {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}

/-- A command step that rejects decides on the bits it held and the bytes its refill took, whatever follows them: at most
64 bits from the first bit it held. -/
theorem stepCmd_bad (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    {p : Phase} {st : Cmd} {pos : USize} (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat)
    (hb : (stepCmd H k a stop hs st pos).status = .bad) :
    pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧ (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧
      8 * (stepCmd H k a stop hs st pos).pos.toNat + st.count.toNat ≤ 8 * pos.toNat + 64 ∧
      ∀ F, rest w m K p (stateBits st a pos (stepCmd H k a stop hs st pos).pos F) = none := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmd at hb ⊢
  rw [dite_eq_left hp'] at hb ⊢
  obtain ⟨h1, h2, h3, _, h5⟩ := refill_spec hs hp hrel.wf
  obtain ⟨l1, l2⟩ := refill_local hs hp hrel.wf
  dsimp only at hb ⊢
  generalize hR : refill st.word st.count a pos stop hs hp = R at h1 h2 h3 h5 l1 l2 hb ⊢
  have hrp : R.pos ≤ stop := USize.le_iff_toNat_le.mpr h3
  obtain ⟨e1, e2⟩ := stepAt_bad hrp hb
  rw [e2]
  refine ⟨h2, h3, l2, fun F => ?_⟩
  have hok := stepAt_ok (hs := Nat.le_trans h3 hs) (H := H) (k := k) hK hH (hrel.withBits h1) (Nat.le_refl _) (Or.inr rfl)
  have hbad := hok.bad (by rw [← e1]; exact hb) F
  rw [stateBits_eq, chunkBits_self, List.nil_append] at hbad
  rw [stateBits_eq, ← List.append_assoc, ← l1]
  exact hbad

/-- A run of the command loop that rejects decides at the last of its steps: from a place the reading in order reaches,
on the bits that step held and the bytes its refill took, whatever follows them. -/
theorem runCmd_bad (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m) :
    ∀ (N : Nat) (n : USize) (p : Phase) (st : Cmd) (pos : USize), n.toNat = N → Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (runCmd H k a stop hs n st pos).status = .bad →
      ∃ (p1 : Phase) (st1 : Cmd) (pos1 : USize), pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ (runCmd H k a stop hs n st pos).pos.toNat ∧
        (runCmd H k a stop hs n st pos).pos.toNat ≤ stop.toNat ∧
        8 * (runCmd H k a stop hs n st pos).pos.toNat + st1.count.toNat ≤ 8 * pos1.toNat + 64 ∧
        (∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p1 (stateBits st1 a pos1 stop F)) ∧
        ∀ F, rest w m K p1 (stateBits st1 a pos1 (runCmd H k a stop hs n st pos).pos F) = none := by
  intro N
  induction N with
  | zero =>
    intro n p st pos hN _ _ hb
    rw [runCmd, dite_eq_left (usize_zero hN)] at hb
    exact absurd hb (fun e => StepStatus.noConfusion e)
  | succ N ih =>
    intro n p st pos hN hrel hp hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hstep := stepCmd_ok (hs := hs) (K := K) (a := a) hK hH hrel hp
    have hbad := stepCmd_bad (hs := hs) (K := K) hK hH hrel hp
    rw [runCmd, dite_eq_right hn] at hb ⊢
    dsimp only at hb ⊢
    generalize stepCmd H k a stop hs st pos = r at hstep hbad hb ⊢
    cases hst : r.status with
    | next =>
      rw [hst] at hb
      dsimp only at hb ⊢
      obtain ⟨p', hR, h1, h2, _, _, _, h5⟩ := hstep.next hst
      obtain ⟨p1, st1, pos1, g1, g2, g3, g4, g5, g6⟩ := ih _ p' r r.pos (by omega) hR h2 hb
      exact ⟨p1, st1, pos1, Nat.le_trans h1 g1, g2, g3, g4, fun F => (h5 F).trans (g5 F), g6⟩
    | bad =>
      dsimp only
      obtain ⟨g1, g2, g3, g4⟩ := hbad hst
      exact ⟨p, st, pos, Nat.le_refl _, g1, g2, g3, fun _ => .refl _ _, g4⟩
    | needsInput => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)
    | needsOutput => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)
    | done => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)

/-- The window and the bytes waiting of a command loop state. -/
def Cmd.WinSame (r st : Cmd) : Prop := r.ring = st.ring ∧ r.wpos = st.wpos ∧ r.pend = st.pend

/-- Closes the goals a step's rejecting branches leave. -/
macro "badWin_tac" : tactic => `(tactic| ((try dsimp only) <;> repeat' (first | split_all | (intro _; exact ⟨rfl, rfl, rfl⟩) | (intro _; exact ⟨trivial, trivial, trivial⟩) | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))))

/-- A command loop step, once the buffer is refilled, rejects only with its window and bytes waiting as they were. -/
theorem stepAt_badWin {st : Cmd} {pos : USize} :
    (stepAt H k a stop hs st pos).status = .bad → (stepAt H k a stop hs st pos).WinSame st := by
  unfold stepAt Cmd.WinSame
  cases ht : st.tag <;> dsimp only
  · unfold stepCommand markStep clearSeen
    badWin_tac
  · unfold stepInsertCopy insertStep markStep
    badWin_tac
  · unfold stepCopyLength markStep
    badWin_tac
  · unfold stepLiterals literalsRun finishLiterals markStep clearSeen clearRing
    badWin_tac
  · unfold stepDistance applyDistance applyWord applyBuilt markStep clearSeen
    badWin_tac
  · unfold stepDistanceSymbol
    by_cases hd : st.dCur < H.nD
    · rw [dite_eq_left hd]
      unfold distanceThrough distanceStep applyDistance applyWord applyBuilt markStep
      badWin_tac
    · rw [dite_eq_right hd]
      intro _
      exact ⟨rfl, rfl, rfl⟩
  · unfold stepCopy finishCopy markStep clearRing
    badWin_tac
  · unfold stepWord finishWord markStep clearRing
    badWin_tac

/-- A command loop step rejects only with its window and bytes waiting as they were. -/
theorem stepCmd_badWin {st : Cmd} {pos : USize} (h : (stepCmd H k a stop hs st pos).status = .bad) :
    (stepCmd H k a stop hs st pos).WinSame st := by
  unfold stepCmd at h ⊢
  by_cases hp : pos ≤ stop
  · rw [dite_eq_left hp] at h ⊢
    exact stepAt_badWin h
  · rw [dite_eq_right hp]
    exact ⟨rfl, rfl, rfl⟩

/-- A run of the command loop that rejects leaves the window and the bytes waiting of a state at a place the reading in
order reaches. -/
theorem runCmd_badWin (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m) :
    ∀ (N : Nat) (n : USize) (p : Phase) (st : Cmd) (pos : USize), n.toNat = N → Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (runCmd H k a stop hs n st pos).status = .bad →
      ∃ (p1 : Phase) (st1 : Cmd), Rel w k.toNat m st1 p1 ∧ (runCmd H k a stop hs n st pos).WinSame st1 := by
  intro N
  induction N with
  | zero =>
    intro n p st pos hN _ _ hb
    rw [runCmd, dite_eq_left (usize_zero hN)] at hb
    exact absurd hb (fun e => StepStatus.noConfusion e)
  | succ N ih =>
    intro n p st pos hN hrel hp hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hstep := stepCmd_ok (hs := hs) (K := K) (a := a) hK hH hrel hp
    have hbad := stepCmd_badWin (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos)
    rw [runCmd, dite_eq_right hn] at hb ⊢
    dsimp only at hb ⊢
    generalize stepCmd H k a stop hs st pos = r at hstep hbad hb ⊢
    cases hst : r.status with
    | next =>
      rw [hst] at hb
      dsimp only at hb ⊢
      obtain ⟨p', hR, _, h2, _, _, _, _⟩ := hstep.next hst
      exact ih _ p' r r.pos (by omega) hR h2 hb
    | bad =>
      dsimp only
      exact ⟨p, st, hrel, hbad hst⟩
    | needsInput => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)
    | needsOutput => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)
    | done => rw [hst] at hb; exact absurd (hst.symm.trans hb) (fun e => StepStatus.noConfusion e)

end

/-! ### Where a header step that stops decides -/

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}

/-- A header step that rejects decides on the bits it held and the bytes its refill took, whatever follows them: at most
64 bits from the first bit it held. -/
theorem stepH_bad {g : Gh} {p : HPhase} {st : Hd} {pos : USize} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) {h : HIn st} (hbd : (stepH a stop hs st pos h hp).status = .bad) :
    pos.toNat ≤ (stepH a stop hs st pos h hp).pos.toNat ∧ (stepH a stop hs st pos h hp).pos.toNat ≤ stop.toNat ∧
      8 * (stepH a stop hs st pos h hp).pos.toNat + st.count.toNat ≤ 8 * pos.toNat + 64 ∧
      ∀ F, hrest K g p (availBits st.word st.count a pos (stepH a stop hs st pos h hp).pos F) = none := by
  unfold stepH at hbd ⊢
  dsimp only at hbd ⊢
  generalize hRR : refillH st.word st.count a pos stop hs hp (hrel_wf h.rel) = RR at hbd ⊢
  obtain ⟨R, hRw⟩ := RR
  have eR : R = refill st.word st.count a pos stop hs hp := by rw [← refillH_val (hw := hrel_wf h.rel), hRR]
  obtain ⟨h1, h2, h3, _, _⟩ := refill_spec hs hp hrel.wf
  obtain ⟨l1, l2⟩ := refill_local hs hp hrel.wf
  rw [← eR] at h1 h2 h3 l1 l2
  dsimp only at hbd ⊢
  have e2 : (stepAtH { st with word := R.word, count := R.count } R.pos (hrel_bits h.rel hRw)).pos = R.pos :=
    (congrArg Hd.pos (stepAtH_pos _ R.pos _)).trans rfl
  rw [e2]
  refine ⟨h2, h3, l2, fun F => ?_⟩
  have hok := stepAtH_ok (K := K) (a := a) (stop := R.pos) (h := hrel_bits h.rel hRw) (hrel.withBits h1) (Nat.le_refl _) (Or.inr rfl) hb
  have hbad := hok.bad hbd F
  rw [avail_mk, chunkBits_self, List.nil_append] at hbad
  rw [avail_mk, ← List.append_assoc, ← l1]
  exact hbad

/-- A header step that goes on does so on the bits it held and the bytes its refill took, whatever follows them: what the
place it started at is worth is what the place it got to is worth, with the table of any code it read. -/
theorem stepH_next {g : Gh} {p : HPhase} {st : Hd} {pos : USize} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) {h : HIn st} (hn : (stepH a stop hs st pos h hp).status = .next) :
    ∃ g' p' oc, HRel (stepH a stop hs st pos h hp) g' p' ∧ HMove st (stepH a stop hs st pos h hp) g p g' p' oc ∧ HDown p p' ∧
      pos.toNat ≤ (stepH a stop hs st pos h hp).pos.toNat ∧ (stepH a stop hs st pos h hp).pos.toNat ≤ stop.toNat ∧
      (∀ F, hrest K g p (availBits st.word st.count a pos (stepH a stop hs st pos h hp).pos F) =
        Wr K oc (hrest K g' p' ((BitBuffer.mk (stepH a stop hs st pos h hp).word (stepH a stop hs st pos h hp).count).held ++ F))) ∧
      ∀ F, hStepP (g, p) (availBits st.word st.count a pos (stepH a stop hs st pos h hp).pos F) = .next (g', p')
        ((BitBuffer.mk (stepH a stop hs st pos h hp).word (stepH a stop hs st pos h hp).count).held ++ F) := by
  unfold stepH at hn ⊢
  dsimp only at hn ⊢
  generalize hRR : refillH st.word st.count a pos stop hs hp (hrel_wf h.rel) = RR at hn ⊢
  obtain ⟨R, hRw⟩ := RR
  have eR : R = refill st.word st.count a pos stop hs hp := by rw [← refillH_val (hw := hrel_wf h.rel), hRR]
  obtain ⟨h1, h2, h3, _, _⟩ := refill_spec hs hp hrel.wf
  obtain ⟨l1, _⟩ := refill_local hs hp hrel.wf
  rw [← eR] at h1 h2 h3 l1
  dsimp only at hn ⊢
  have e2 : (stepAtH { st with word := R.word, count := R.count } R.pos (hrel_bits h.rel hRw)).pos = R.pos :=
    (congrArg Hd.pos (stepAtH_pos _ R.pos _)).trans rfl
  have hok := stepAtH_ok (K := K) (a := a) (stop := R.pos) (h := hrel_bits h.rel hRw) (hrel.withBits h1) (Nat.le_refl _) (Or.inr rfl) hb
  obtain ⟨g', p', oc, hR, _, _, hW, hD, hM, hJ⟩ := hok.next hn
  refine ⟨g', p', oc, hR, ⟨hM.max, hM.grow, fun hz => hM.size { hz with }, hM.cap.same rfl⟩, hD, by rw [e2]; exact h2,
    by rw [e2]; exact h3, fun F => ?_, fun F => ?_⟩
  · have h := hW F
    rw [avail_mk, chunkBits_self, List.nil_append, avail_mk, e2, chunkBits_self, List.nil_append] at h
    rw [avail_mk, e2, ← List.append_assoc, ← l1]
    exact h
  · have h := hJ F
    rw [avail_mk, chunkBits_self, List.nil_append, avail_mk, e2, chunkBits_self, List.nil_append] at h
    rw [avail_mk, e2, ← List.append_assoc, ← l1]
    exact h

/-- A header step that reports the limit decides on the bits it held and the bytes its refill took, whatever follows them:
at most 64 bits from the first bit it held. -/
theorem stepH_memory {g : Gh} {p : HPhase} {st : Hd} {pos : USize} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) {h : HIn st} (hm : (stepH a stop hs st pos h hp).status = .memory) :
    pos.toNat ≤ (stepH a stop hs st pos h hp).pos.toNat ∧ (stepH a stop hs st pos h hp).pos.toNat ≤ stop.toNat ∧
      8 * (stepH a stop hs st pos h hp).pos.toNat + st.count.toNat ≤ 8 * pos.toNat + 64 ∧
      ∃ g', st.d.arenaMax.toNat < resBytes g' ∧ resBytes g' ≤ resMax ∧ st.d.arenaCap.toNat = smallMax ∧
        ∀ F, ∃ x, hrest K g p (availBits st.word st.count a pos (stepH a stop hs st pos h hp).pos F) = K.r g' x := by
  unfold stepH at hm ⊢
  dsimp only at hm ⊢
  generalize hRR : refillH st.word st.count a pos stop hs hp (hrel_wf h.rel) = RR at hm ⊢
  obtain ⟨R, hRw⟩ := RR
  have eR : R = refill st.word st.count a pos stop hs hp := by rw [← refillH_val (hw := hrel_wf h.rel), hRR]
  obtain ⟨h1, h2, h3, _, _⟩ := refill_spec hs hp hrel.wf
  obtain ⟨l1, l2⟩ := refill_local hs hp hrel.wf
  rw [← eR] at h1 h2 h3 l1 l2
  dsimp only at hm ⊢
  have e2 : (stepAtH { st with word := R.word, count := R.count } R.pos (hrel_bits h.rel hRw)).pos = R.pos :=
    (congrArg Hd.pos (stepAtH_pos _ R.pos _)).trans rfl
  rw [e2]
  refine ⟨h2, h3, l2, ?_⟩
  have hok := stepAtH_ok (K := K) (a := a) (stop := R.pos) (h := hrel_bits h.rel hRw) (hrel.withBits h1) (Nat.le_refl _) (Or.inr rfl) hb
  obtain ⟨g', c1, c2, c3, c4⟩ := hok.memory hm
  refine ⟨g', c1, c2, c3, fun F => ?_⟩
  obtain ⟨x, hx⟩ := c4 F
  rw [avail_mk, chunkBits_self, List.nil_append] at hx
  refine ⟨x, ?_⟩
  rw [avail_mk, ← List.append_assoc, ← l1]
  exact hx

end

end Brotli.Decoder
