import Brotli.Decoder.StreamTop

/-!
# Where the chunk sits

A call's reply depends only on the chunk's bytes, the output space and the end flag: not on where the chunk sits in its
array, the bytes around it, or what the output buffer held.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Splits the first branch in the goal, and takes the same branch wherever its condition recurs. -/
macro "split_all" : tactic => `(tactic| split <;> (try (rename_i hc; first
  | simp only [dite_eq_left hc, ite_eq_left hc] | simp only [dite_eq_right hc, ite_eq_right hc] | simp only [hc])))

/-! ### Steps that only record the position

A step that reads no input only records the position it is given: its result is the same, but for that position, whatever
position it is given and whatever position its state held. -/

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

theorem clTable_pos (st : Hd) (q : USize) : clTable { st with pos := q } = clTable st := rfl

theorem mapSizeFast_pos (st : Hd) (q : USize) : mapSizeFast { st with pos := q } = mapSizeFast st := rfl

theorem installTable_nf (st : Hd) (base : UInt64) :
    installTable st base = { installTable { st with pos := 0 } base with pos := st.pos } := by
  unfold installTable clearFill
  cases st
  try dsimp only
  repeat' (first | split_all | rfl)

theorem growPlanned_nf (st : Hd) (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (pl : Plan) :
    growPlanned st lens n hn pl = { growPlanned { st with pos := 0 } lens n hn pl with pos := st.pos } := rfl

theorem growSingle_nf (st : Hd) (sym : UInt64) :
    growSingle st sym = { growSingle { st with pos := 0 } sym with pos := st.pos } := rfl

theorem mapTableDone_nf (st : Hd) (t : ByteArray) :
    mapTableDone st t = { mapTableDone { st with pos := 0 } t with pos := st.pos } := by
  unfold mapTableDone
  try dsimp only
  repeat' (first | split_all | rfl)

set_option maxRecDepth 8192 in
theorem tableDone_nf (st : Hd) (single : Bool) (sym : UInt64) :
    tableDone st single sym = { tableDone { st with pos := 0 } single sym with pos := st.pos } := by
  unfold tableDone
  cases st
  try dsimp only
  repeat' (first | split_all | exact (installTable_nf _ _).trans rfl | exact (mapTableDone_nf _ _).trans rfl | rfl)

theorem catMoveOn_nf (st : Hd) : catMoveOn st = { catMoveOn { st with pos := 0 } with pos := st.pos } := by
  unfold catMoveOn
  cases st
  try dsimp only
  repeat' (first | split_all | rfl)

theorem clFinish_nf (st : Hd) : clFinish st = { clFinish { st with pos := 0 } with pos := st.pos } := by
  unfold clFinish
  dsimp only
  by_cases hc : fitsFast (clTable st) 0 = true
  · have hc' : fitsFast (clTable { st with pos := 0 }) 0 = true := hc
    rw [dite_eq_left hc, dite_eq_left hc']
    rfl
  · have hc' : ¬ fitsFast (clTable { st with pos := 0 }) 0 = true := hc
    rw [dite_eq_right hc, dite_eq_right hc']

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
    | exact (installTable_nf _ _).trans rfl
    | exact (mapTableDone_nf _ _).trans rfl
    | exact (tableDone_nf _ _ _).trans rfl
    | exact (catMoveOn_nf _).trans rfl
    | exact (clFinish_nf _).trans rfl
    | exact (mapFinish_nf _ _ _).trans rfl
    | exact (ckFinish_nf _).trans rfl
    | rfl)))

theorem stepHCat_pos (st : Hd) (p : USize) : stepHCat st p = { stepHCat { st with pos := 0 } 0 with pos := p } := by
  unfold stepHCat
  cases st
  hd_nf

theorem stepHCode_pos (st : Hd) (p : USize) : stepHCode st p = { stepHCode { st with pos := 0 } 0 with pos := p } := by
  unfold stepHCode
  cases st
  hd_nf

theorem stepHClens_pos (st : Hd) (p : USize) : stepHClens st p = { stepHClens { st with pos := 0 } 0 with pos := p } := by
  unfold stepHClens
  cases st
  hd_nf

set_option maxHeartbeats 2000000 in
theorem stepHSyms_pos (st : Hd) (p : USize) : stepHSyms st p = { stepHSyms { st with pos := 0 } 0 with pos := p } := by
  unfold stepHSyms
  cases st
  hd_nf

theorem stepHFirst_pos (st : Hd) (p : USize) : stepHFirst st p = { stepHFirst { st with pos := 0 } 0 with pos := p } := by
  unfold stepHFirst
  cases st
  hd_nf

theorem stepHNp_pos (st : Hd) (p : USize) : stepHNp st p = { stepHNp { st with pos := 0 } 0 with pos := p } := by
  unfold stepHNp
  cases st
  hd_nf

theorem stepHModes_pos (st : Hd) (p : USize) : stepHModes st p = { stepHModes { st with pos := 0 } 0 with pos := p } := by
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

theorem stepHVals_pos (st : Hd) (p : USize) : stepHVals st p = { stepHVals { st with pos := 0 } 0 with pos := p } := by
  unfold stepHVals
  cases st
  hd_nf

theorem stepHImtf_pos (st : Hd) (p : USize) : stepHImtf st p = { stepHImtf { st with pos := 0 } 0 with pos := p } := by
  unfold stepHImtf
  cases st
  hd_nf

theorem stepHCodes_pos (st : Hd) (p : USize) : stepHCodes st p = { stepHCodes { st with pos := 0 } 0 with pos := p } := by
  unfold stepHCodes
  cases st
  hd_nf

/-! ### Loops that read the input -/

/-- The loop for uncompressed bytes depends only on the unread bytes. -/
theorem rawRun_same {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size) (mask : USize)
    (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n : USize) (w1 w2 c1 c2 : UInt64) (p1 p2 : USize) (r1 r2 : ByteArray) (u1 u2 : USize) (x1 x2 y1 y2 : UInt8)
      (hp1 : p1.toNat ≤ e1.toNat) (hp2 : p2.toNat ≤ e2.toNat) (hz1 : r1.size = 2 ^ k) (hz2 : r2.size = 2 ^ k)
      (hu1 : u1.toNat < 2 ^ k) (hu2 : u2.toNat < 2 ^ k),
      n.toNat = N → w1 = w2 → c1 = c2 → r1 = r2 → u1 = u2 → x1 = x2 → y1 = y2 → Same a1 e1 a2 e2 p1 p2 →
      { rawRun a1 e1 hs1 mask k hk hmask n w1 c1 p1 r1 u1 x1 y1 hp1 hz1 hu1 with pos := 0 } =
          { rawRun a2 e2 hs2 mask k hk hmask n w2 c2 p2 r2 u2 x2 y2 hp2 hz2 hu2 with pos := 0 } ∧
        Same a1 e1 a2 e2 (rawRun a1 e1 hs1 mask k hk hmask n w1 c1 p1 r1 u1 x1 y1 hp1 hz1 hu1).pos
          (rawRun a2 e2 hs2 mask k hk hmask n w2 c2 p2 r2 u2 x2 y2 hp2 hz2 hu2).pos := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n w1 w2 c1 c2 p1 p2 r1 r2 u1 u2 x1 x2 y1 y2 hp1 hp2 hz1 hz2 hu1 hu2 hN ew ec er eu ex ey h
    subst ew ec er eu ex ey
    rw [rawRun, rawRun]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      exact ⟨rfl, h⟩
    · rw [dite_eq_right hn, dite_eq_right hn]
      dsimp only
      have hlt : (n - USize.ofNat 1).toNat < N := by
        have := usize_pred hn
        have := usize_ne hn
        omega
      by_cases h8 : 8 ≤ c1
      · rw [ite_eq_left h8, ite_eq_left h8]
        exact ih _ hlt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl h
      · rw [ite_eq_right h8, ite_eq_right h8]
        obtain ⟨ew, ec, hS⟩ := refill_same (word := w1) (count := c1) hs1 hs2 hp1 hp2 h
        have hq1 := hS.2.2.1
        have hq2 := hS.2.2.2.1
        by_cases hc : 8 ≤ (refill w1 c1 a1 p1 e1 hs1 hp1).count ∧ (refill w1 c1 a1 p1 e1 hs1 hp1).pos ≤ e1
        · have hc2 : 8 ≤ (refill w1 c1 a2 p2 e2 hs2 hp2).count ∧ (refill w1 c1 a2 p2 e2 hs2 hp2).pos ≤ e2 :=
            ⟨ec ▸ hc.1, USize.le_iff_toNat_le.mpr hq2⟩
          rw [dite_eq_left hc, dite_eq_left hc2]
          exact ih _ hlt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl (by rw [ew]) (by rw [ec]) (by rw [ew]) rfl
            (by rw [ew]) rfl hS
        · have hc2 : ¬ (8 ≤ (refill w1 c1 a2 p2 e2 hs2 hp2).count ∧ (refill w1 c1 a2 p2 e2 hs2 hp2).pos ≤ e2) :=
            fun e => hc ⟨ec ▸ e.1, USize.le_iff_toNat_le.mpr hq1⟩
          rw [dite_eq_right hc, dite_eq_right hc2]
          refine ⟨?_, hS⟩
          show RawRun.mk _ _ 0 _ _ _ _ _ = RawRun.mk _ _ 0 _ _ _ _ _
          rw [ew, ec]

/-- The literal loop depends only on the unread bytes. -/
theorem literalRun_same {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size) (mapBase modeOff mask : USize)
    (k : Nat) (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) :
    ∀ (N : Nat) (n : USize) (w1 w2 c1 c2 : UInt64) (p1 p2 u1 u2 : USize) (r1 r2 : ByteArray) (x1 x2 y1 y2 : UInt8)
      (hp1 : p1.toNat ≤ e1.toNat) (hp2 : p2.toNat ≤ e2.toNat) (hw1 : (BitBuffer.mk w1 c1).Wf) (hw2 : (BitBuffer.mk w2 c2).Wf)
      (hz1 : r1.size = 2 ^ k) (hz2 : r2.size = 2 ^ k) (hu1 : u1.toNat < 2 ^ k) (hu2 : u2.toNat < 2 ^ k),
      n.toNat = N → w1 = w2 → c1 = c2 → u1 = u2 → r1 = r2 → x1 = x2 → y1 = y2 → Same a1 e1 a2 e2 p1 p2 →
      { literalRun C a1 e1 hs1 mapBase modeOff mask k hmb hm hd hmask hk n w1 c1 p1 u1 r1 x1 y1 hp1 hw1 hz1 hu1 with pos := 0 } =
          { literalRun C a2 e2 hs2 mapBase modeOff mask k hmb hm hd hmask hk n w2 c2 p2 u2 r2 x2 y2 hp2 hw2 hz2 hu2 with pos := 0 } ∧
        Same a1 e1 a2 e2 (literalRun C a1 e1 hs1 mapBase modeOff mask k hmb hm hd hmask hk n w1 c1 p1 u1 r1 x1 y1 hp1 hw1 hz1 hu1).pos
          (literalRun C a2 e2 hs2 mapBase modeOff mask k hmb hm hd hmask hk n w2 c2 p2 u2 r2 x2 y2 hp2 hw2 hz2 hu2).pos := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n w1 w2 c1 c2 p1 p2 u1 u2 r1 r2 x1 x2 y1 y2 hp1 hp2 hw1 hw2 hz1 hz2 hu1 hu2 hN ew ec eu er ex ey h
    subst ew ec eu er ex ey
    rw [literalRun, literalRun]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      exact ⟨rfl, h⟩
    · rw [dite_eq_right hn, dite_eq_right hn]
      dsimp only
      have hlt : (n - USize.ofNat 1).toNat < N := by
        have := usize_pred hn
        have := usize_ne hn
        omega
      obtain ⟨ew, ec, hS⟩ := refill_same (word := w1) (count := c1) hs1 hs2 hp1 hp2 h
      simp only [← ew, ← ec]
      split_all
      · exact ih _ hlt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl rfl rfl rfl rfl hS
      · exact ⟨trivial, hS⟩

/-! ### The command loop -/

/-- Two command states the same but for their positions, which have the same unread bytes. -/
def CmdSame (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (s1 s2 : Cmd) : Prop :=
  { s1 with pos := 0 } = { s2 with pos := 0 } ∧ Same a1 e1 a2 e2 s1.pos s2.pos

theorem cmd_er {s t : Cmd} (h : { s with pos := 0 } = { t with pos := 0 }) : t = { s with pos := t.pos } := by
  cases s
  cases t
  cases h
  rfl

theorem litRun_er {s t : LitRun} (h : { s with pos := 0 } = { t with pos := 0 }) : s = { t with pos := s.pos } := by
  cases s
  cases t
  cases h
  rfl

/-- A step that only records the position. -/
theorem nf_same {a1 a2 : ByteArray} {e1 e2 : USize} {f : Cmd → USize → Cmd}
    (hf : ∀ st p, f st p = { f { st with pos := 0 } 0 with pos := p }) {s t : Cmd}
    (he : { s with pos := 0 } = { t with pos := 0 }) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    CmdSame a1 e1 a2 e2 (f s p1) (f t p2) := by
  rw [hf s p1, hf t p2]
  refine ⟨?_, h⟩
  show { f { s with pos := 0 } 0 with pos := 0 } = { f { t with pos := 0 } 0 with pos := 0 }
  rw [he]

theorem literalsRun_same (H : Hdr) (k : USize) {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) (s : Cmd) (q : USize) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    CmdSame a1 e1 a2 e2 (literalsRun H k a1 e1 hs1 s p1) (literalsRun H k a2 e2 hs2 { s with pos := q } p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  unfold literalsRun
  dsimp only
  by_cases ht : s.lCur < H.nL
  · rw [dite_eq_left ht, dite_eq_left ht]
    by_cases hc : winCheck k s.wpos s.ring = true ∧ wfCheck s.word s.count = true
    · rw [dite_eq_left (show winCheck k s.wpos s.ring = true ∧ p1 ≤ e1 ∧ wfCheck s.word s.count = true from ⟨hc.1, hq1, hc.2⟩),
        dite_eq_left (show winCheck k s.wpos s.ring = true ∧ p2 ≤ e2 ∧ wfCheck s.word s.count = true from ⟨hc.1, hq2, hc.2⟩)]
      obtain ⟨e, hS⟩ := literalRun_same H.lit hs1 hs2
        _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _ _ _
        rfl rfl rfl rfl rfl rfl rfl h
      refine ⟨?_, hS⟩
      rw [litRun_er e]
      rfl
    · rw [dite_eq_right (show ¬ (winCheck k s.wpos s.ring = true ∧ p1 ≤ e1 ∧ wfCheck s.word s.count = true) from
          fun e => hc ⟨e.1, e.2.2⟩),
        dite_eq_right (show ¬ (winCheck k s.wpos s.ring = true ∧ p2 ≤ e2 ∧ wfCheck s.word s.count = true) from
          fun e => hc ⟨e.1, e.2.2⟩)]
      exact ⟨rfl, h⟩
  · rw [dite_eq_right ht, dite_eq_right ht]
    exact ⟨rfl, h⟩

theorem stepLiterals_same (H : Hdr) (k : USize) {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) {s t : Cmd} (he : { s with pos := 0 } = { t with pos := 0 }) {p1 p2 : USize}
    (h : Same a1 e1 a2 e2 p1 p2) :
    CmdSame a1 e1 a2 e2 (stepLiterals H k a1 e1 hs1 s p1) (stepLiterals H k a2 e2 hs2 t p2) := by
  rw [cmd_er he]
  generalize t.pos = q
  have hL := literalsRun_same H k hs1 hs2 s q h
  unfold stepLiterals markStep clearSeen
  cases s
  dsimp only at hL ⊢
  repeat' (first | split_all | exact hL | exact ⟨rfl, h⟩)

theorem stepAt_same (H : Hdr) (k : USize) {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) {s t : Cmd} (he : { s with pos := 0 } = { t with pos := 0 }) {p1 p2 : USize}
    (h : Same a1 e1 a2 e2 p1 p2) :
    CmdSame a1 e1 a2 e2 (stepAt H k a1 e1 hs1 s p1) (stepAt H k a2 e2 hs2 t p2) := by
  have htag : t.tag = s.tag := by rw [cmd_er he]
  unfold stepAt
  rw [htag]
  cases s.tag
  · exact nf_same (stepCommand_pos H) he h
  · exact nf_same (stepInsertCopy_pos H) he h
  · exact nf_same stepCopyLength_pos he h
  · exact stepLiterals_same H k hs1 hs2 he h
  · exact nf_same (stepDistance_pos H) he h
  · exact nf_same (stepDistanceSymbol_pos H) he h
  · exact nf_same (stepCopy_pos k) he h
  · exact nf_same (stepWord_pos k) he h

theorem stepCmd_same (H : Hdr) (k : USize) {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) {s t : Cmd} (he : { s with pos := 0 } = { t with pos := 0 }) {p1 p2 : USize}
    (h : Same a1 e1 a2 e2 p1 p2) :
    CmdSame a1 e1 a2 e2 (stepCmd H k a1 e1 hs1 s p1) (stepCmd H k a2 e2 hs2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  have hw : t.word = s.word := by rw [cmd_er he]
  have hc : t.count = s.count := by rw [cmd_er he]
  unfold stepCmd
  rw [dite_eq_left hq1, dite_eq_left hq2]
  dsimp only
  obtain ⟨ew, ec, hS⟩ := refill_same (word := s.word) (count := s.count) hs1 hs2 h.2.2.1 h.2.2.2.1 h
  rw [hw, hc]
  refine stepAt_same H k hs1 hs2 ?_ hS
  show { s with word := _, count := _, pos := 0 } = { t with word := _, count := _, pos := 0 }
  rw [ew, ec, cmd_er he]

theorem runCmd_same (H : Hdr) (k : USize) {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size)
    (hs2 : e2.toNat ≤ a2.size) : ∀ (N : Nat) (n : USize) {s t : Cmd} {p1 p2 : USize}, n.toNat = N →
    { s with pos := 0 } = { t with pos := 0 } → Same a1 e1 a2 e2 p1 p2 →
    CmdSame a1 e1 a2 e2 (runCmd H k a1 e1 hs1 n s p1) (runCmd H k a2 e2 hs2 n t p2) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n s t p1 p2 hN he h
    rw [runCmd, runCmd]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      refine ⟨?_, h⟩
      show { s with pos := 0, status := .next } = { t with pos := 0, status := .next }
      rw [cmd_er he]
    · rw [dite_eq_right hn, dite_eq_right hn]
      dsimp only
      have hlt : (n - USize.ofNat 1).toNat < N := by
        have := usize_pred hn
        have := usize_ne hn
        omega
      obtain ⟨e, hS⟩ := stepCmd_same H k hs1 hs2 he h
      have hst : (stepCmd H k a2 e2 hs2 t p2).status = (stepCmd H k a1 e1 hs1 s p1).status := by rw [cmd_er e]
      rw [hst]
      split
      · exact ih _ hlt _ rfl e hS
      · exact ⟨e, hS⟩

/-! ### The header machine -/

/-- Two header states the same but for their positions, which have the same unread bytes. -/
def HdSame (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (s1 s2 : Hd) : Prop :=
  { s1 with pos := 0 } = { s2 with pos := 0 } ∧ Same a1 e1 a2 e2 s1.pos s2.pos

theorem hd_er {s t : Hd} (h : { s with pos := 0 } = { t with pos := 0 }) : t = { s with pos := t.pos } := by
  cases s
  cases t
  cases h
  rfl

theorem stepAtH_pos (st : Hd) (p : USize) : stepAtH st p = { stepAtH { st with pos := 0 } 0 with pos := p } := by
  unfold stepAtH
  cases st
  dsimp only
  split
  · exact (stepHCat_pos _ _).trans rfl
  · exact (stepHCode_pos _ _).trans rfl
  · exact (stepHClens_pos _ _).trans rfl
  · exact (stepHSyms_pos _ _).trans rfl
  · exact (stepHFirst_pos _ _).trans rfl
  · exact (stepHNp_pos _ _).trans rfl
  · exact (stepHModes_pos _ _).trans rfl
  · exact (stepHTrees_pos _ _).trans rfl
  · exact (stepHRlemax_pos _ _).trans rfl
  · exact (stepHVals_pos _ _).trans rfl
  · exact (stepHImtf_pos _ _).trans rfl
  · exact (stepHCodes_pos _ _).trans rfl
  · rfl

theorem stepH_same {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size) {s t : Hd}
    (he : { s with pos := 0 } = { t with pos := 0 }) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    HdSame a1 e1 a2 e2 (stepH a1 e1 hs1 s p1) (stepH a2 e2 hs2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  have hw : t.word = s.word := by rw [hd_er he]
  have hc : t.count = s.count := by rw [hd_er he]
  unfold stepH
  rw [dite_eq_left hq1, dite_eq_left hq2]
  dsimp only
  obtain ⟨ew, ec, hS⟩ := refill_same (word := s.word) (count := s.count) hs1 hs2 h.2.2.1 h.2.2.2.1 h
  rw [hw, hc, stepAtH_pos _ (refill s.word s.count a1 p1 e1 hs1 _).pos, stepAtH_pos _ (refill s.word s.count a2 p2 e2 hs2 _).pos]
  refine ⟨?_, hS⟩
  show { stepAtH { s with word := _, count := _, pos := 0 } 0 with pos := 0 } =
    { stepAtH { t with word := _, count := _, pos := 0 } 0 with pos := 0 }
  rw [ew, ec, hd_er he]

/-! ### The stream's steps -/

/-- A stream state without the positions it holds. -/
def Dec.er (D : Dec) : Dec := { D with pos := 0, cmd := { D.cmd with pos := 0 }, hd := { D.hd with pos := 0 } }

/-- Two stream states the same but for their positions, which have the same unread bytes. -/
def DecSame (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (D1 D2 : Dec) : Prop :=
  D1.er = D2.er ∧ Same a1 e1 a2 e2 D1.pos D2.pos

theorem dec_er {s t : Dec} (h : s.er = t.er) :
    t = { s with pos := t.pos, cmd := { s.cmd with pos := t.cmd.pos }, hd := { s.hd with pos := t.hd.pos } } := by
  cases s with
  | mk tag c d H k last left limit pos status =>
    cases c
    cases d
    cases t with
    | mk tag' c' d' H' k' last' left' limit' pos' status' =>
      cases c'
      cases d'
      cases h
      rfl

theorem rawRun_er {s t : RawRun} (h : { s with pos := 0 } = { t with pos := 0 }) : s = { t with pos := s.pos } := by
  cases s
  cases t
  cases h
  rfl

section
variable {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size)

include hs1 hs2 in
theorem stepDWbits_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDWbits a1 e1 hs1 s p1) (stepDWbits a2 e2 hs2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  unfold stepDWbits
  rw [dite_eq_left hq1, dite_eq_left hq2]
  dsimp only
  obtain ⟨ew, ec, hS⟩ := refill_same (word := s.cmd.word) (count := s.cmd.count) hs1 hs2 h.2.2.1 h.2.2.2.1 h
  simp only [← ew, ← ec]
  repeat' (first | split_all | (refine ⟨rfl, ?_⟩; exact hS) | (refine ⟨rfl, ?_⟩; exact h))

include hs1 hs2 in
theorem stepDMeta_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDMeta a1 e1 hs1 s p1) (stepDMeta a2 e2 hs2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  unfold stepDMeta metaGo
  dsimp only
  by_cases hz : s.cmd.pend = 0
  · rw [ite_eq_left hz, ite_eq_left hz, dite_eq_left hq1, dite_eq_left hq2]
    try dsimp only
    obtain ⟨ew, ec, hS⟩ := refill_same (word := s.cmd.word) (count := s.cmd.count) hs1 hs2 h.2.2.1 h.2.2.2.1 h
    simp only [← ew, ← ec]
    repeat' (first | split_all | (refine ⟨rfl, ?_⟩; exact hS) | (refine ⟨rfl, ?_⟩; exact h))
  · rw [ite_eq_right hz, ite_eq_right hz]
    exact ⟨rfl, h⟩

theorem stepDSkip_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDSkip e1 s p1) (stepDSkip e2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  have hd : e2 - p2 = e1 - p1 := USize.toNat_inj.mp (by
    rw [USize.toNat_sub_of_le _ _ hq1, USize.toNat_sub_of_le _ _ hq2]
    exact h.2.2.2.2.1.symm)
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  unfold stepDSkip moveOn
  dsimp only
  rw [ite_eq_left hq1, ite_eq_left hq2, hd]
  repeat' (first | split_all | (refine ⟨rfl, ?_⟩; exact h))
  all_goals
    refine ⟨rfl, h.adv ?_⟩
    rw [UInt64.toNat_toUSize]
    have hsz := e1.toNat_lt_size
    have hsub : (e1 - p1).toNat = e1.toNat - p1.toNat := USize.toNat_sub_of_le _ _ hq1
    have hpow : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
    first
      | (rename_i hlt _
         have := UInt64.lt_iff_toNat_lt.mp hlt
         rw [USize.toNat_toUInt64, hsub] at this
         rw [Nat.mod_eq_of_lt (by omega)]
         omega)
      | ((rw [USize.toNat_toUInt64, hsub, Nat.mod_eq_of_lt (by omega)]) <;> exact Nat.le_refl _)

include hs1 hs2 in
theorem stepDRaw_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDRaw a1 e1 hs1 s p1) (stepDRaw a2 e2 hs2 t p2) := by
  have hq1 : p1 ≤ e1 := USize.le_iff_toNat_le.mpr h.2.2.1
  have hq2 : p2 ≤ e2 := USize.le_iff_toNat_le.mpr h.2.2.2.1
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  unfold stepDRaw moveOn rawFinish clearCmd clearRing
  dsimp only
  by_cases hl : s.left = 0
  · rw [ite_eq_left hl, ite_eq_left hl]
    exact ⟨rfl, h⟩
  · rw [ite_eq_right hl, ite_eq_right hl]
    by_cases hw : winCheck s.k s.cmd.wpos s.cmd.ring = true
    · rw [dite_eq_left (show winCheck s.k s.cmd.wpos s.cmd.ring = true ∧ p1 ≤ e1 from ⟨hw, hq1⟩),
        dite_eq_left (show winCheck s.k s.cmd.wpos s.cmd.ring = true ∧ p2 ≤ e2 from ⟨hw, hq2⟩)]
      by_cases hp : room s.k s.cmd.cap ≤ s.cmd.pend
      · rw [ite_eq_left hp, ite_eq_left hp]
        exact ⟨rfl, h⟩
      · rw [ite_eq_right hp, ite_eq_right hp]
        obtain ⟨e, hS⟩ := rawRun_same hs1 hs2 _ _ _ _
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _
          rfl rfl rfl rfl rfl rfl rfl h
        refine ⟨?_, hS⟩
        rw [rawRun_er e]
        rfl
    · rw [dite_eq_right (fun e => hw e.1), dite_eq_right (fun e => hw e.1)]
      exact ⟨rfl, h⟩

include hs1 hs2 in
theorem stepDHdr_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDHdr a1 e1 hs1 s p1) (stepDHdr a2 e2 hs2 t p2) := by
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  obtain ⟨e, hS⟩ := stepH_same hs1 hs2 (s := s.hd) (t := { s.hd with pos := q2 }) rfl h
  have e' := hd_er e
  unfold stepDHdr clearHd
  dsimp only at e' hS ⊢
  rw [e']
  generalize (stepH a2 e2 hs2 { s.hd with pos := q2 } p2).pos = q3 at hS ⊢
  generalize stepH a1 e1 hs1 s.hd p1 = R at hS ⊢
  cases R
  dsimp only at hS ⊢
  repeat' (first | split_all | (refine ⟨rfl, ?_⟩; exact hS))

include hs1 hs2 in
theorem stepDCmds_same {s t : Dec} (he : s.er = t.er) {p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) :
    DecSame a1 e1 a2 e2 (stepDCmds a1 e1 hs1 s p1) (stepDCmds a2 e2 hs2 t p2) := by
  rw [dec_er he]
  generalize t.pos = q0
  generalize t.cmd.pos = q1
  generalize t.hd.pos = q2
  obtain ⟨e, hS⟩ := runCmd_same s.H s.k hs1 hs2 _ cmdBudget (s := s.cmd) (t := { s.cmd with pos := q1 }) rfl rfl h
  have e' := cmd_er e
  unfold stepDCmds clearCmd
  dsimp only at e' hS ⊢
  rw [e']
  generalize (runCmd s.H s.k a2 e2 hs2 cmdBudget { s.cmd with pos := q1 } p2).pos = q3 at hS ⊢
  generalize runCmd s.H s.k a1 e1 hs1 cmdBudget s.cmd p1 = R at hS ⊢
  cases R
  dsimp only at hS ⊢
  repeat' (first | split_all | (refine ⟨rfl, ?_⟩; exact hS))

include hs1 hs2 in
theorem stepD_same {s t : Dec} (he : s.er = t.er) (h : Same a1 e1 a2 e2 s.pos t.pos) :
    DecSame a1 e1 a2 e2 (stepD a1 e1 hs1 s) (stepD a2 e2 hs2 t) := by
  have htag : t.tag = s.tag := by rw [dec_er he]
  unfold stepD
  rw [htag]
  cases s.tag
  · exact stepDWbits_same hs1 hs2 he h
  · exact stepDMeta_same hs1 hs2 he h
  · exact stepDSkip_same he h
  · exact stepDRaw_same hs1 hs2 he h
  · exact stepDHdr_same hs1 hs2 he h
  · exact stepDCmds_same hs1 hs2 he h
  · exact ⟨he, h⟩

include hs1 hs2 in
theorem runD_same : ∀ (x : RunArg a1 e1 hs1) (t : Dec) (ht : DInv e2 t), x.D.er = t.er → Same a1 e1 a2 e2 x.D.pos t.pos →
    DecSame a1 e1 a2 e2 (runD a1 e1 hs1 x.D x.inv) (runD a2 e2 hs2 t ht) := by
  intro x
  induction x using (runRel_wf a1 e1 hs1).induction with
  | _ x ih =>
    intro t ht he h
    obtain ⟨D, hinv⟩ := x
    dsimp only at he h ih ⊢
    rw [runD, runD]
    have htag : t.tag = D.tag := by rw [dec_er he]
    by_cases hE : D.tag = .ended
    · rw [dite_eq_left hE, dite_eq_left (htag.trans hE)]
      refine ⟨?_, h⟩
      rw [dec_er he]
      rfl
    · rw [dite_eq_right hE, dite_eq_right (fun e => hE (htag.symm.trans e))]
      dsimp only
      obtain ⟨e, hS⟩ := stepD_same hs1 hs2 he h
      have hst : (stepD a2 e2 hs2 t).status = (stepD a1 e1 hs1 D).status := by rw [dec_er e]
      by_cases hn : (stepD a1 e1 hs1 D).status = .next
      · rw [dite_eq_left hn, dite_eq_left (hst.trans hn)]
        exact ih ⟨_, hinv.step hE hn⟩ ⟨hE, hn, rfl⟩ _ _ e hS
      · rw [dite_eq_right hn, dite_eq_right (fun e => hn (hst.symm.trans e))]
        exact ⟨e, hS⟩

end

/-! ### Handing bytes out -/

/-- A run of bytes goes after what the buffer held, whatever it held. -/
theorem emitRun_app (ring buf : ByteArray) (s n : Nat) :
    (emitRun ring buf s n).data.toList = buf.data.toList ++ (ring.data.extract s (s + n)).toList := by
  show (buf.data.extract 0 buf.size ++ ring.data.extract s (s + n) ++
    buf.data.extract (buf.size + min n (ring.data.size - s)) buf.data.size).toList = _
  have hb : buf.size = buf.data.size := rfl
  have hA : buf.data.extract 0 buf.data.size = buf.data := by simp
  have hC : buf.data.extract (buf.data.size + min n (ring.data.size - s)) buf.data.size = #[] :=
    Array.extract_eq_empty_of_le (by omega)
  rw [hb, hA, hC, Array.append_empty, Array.toList_append]

theorem flushCmd_same (k : USize) (st : Cmd) (q : USize) (b1 b2 : ByteArray) (sp : USize) :
    { (flushCmd k st b1 sp).st with pos := 0 } = { (flushCmd k { st with pos := q } b2 sp).st with pos := 0 } ∧
      (flushCmd k st b1 sp).st.pos = st.pos ∧ (flushCmd k { st with pos := q } b2 sp).st.pos = q ∧
      ∃ L, (flushCmd k st b1 sp).buf.data.toList = b1.data.toList ++ L ∧
        (flushCmd k { st with pos := q } b2 sp).buf.data.toList = b2.data.toList ++ L := by
  unfold flushCmd
  dsimp only
  by_cases hc : st.pend = 0 ∨ sp = 0
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact ⟨rfl, rfl, rfl, [], by simp, by simp⟩
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact ⟨rfl, rfl, rfl, _, emitRun_app _ _ _ _, emitRun_app _ _ _ _⟩

theorem flushAll_same (k : USize) : ∀ (N : Nat) (st : Cmd) (q : USize) (b1 b2 : ByteArray) (sp : Nat), st.pend.toNat = N →
    { (flushAll k st b1 sp).st with pos := 0 } = { (flushAll k { st with pos := q } b2 sp).st with pos := 0 } ∧
      (flushAll k st b1 sp).st.pos = st.pos ∧ (flushAll k { st with pos := q } b2 sp).st.pos = q ∧
      (flushAll k st b1 sp).space = (flushAll k { st with pos := q } b2 sp).space ∧
      ∃ L, (flushAll k st b1 sp).buf.data.toList = b1.data.toList ++ L ∧
        (flushAll k { st with pos := q } b2 sp).buf.data.toList = b2.data.toList ++ L := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro st q b1 b2 sp hN
    rw [flushAll, flushAll]
    dsimp only
    by_cases hc : st.pend = 0 ∨ sp = 0
    · rw [ite_eq_left hc, ite_eq_left hc]
      exact ⟨rfl, rfl, rfl, rfl, [], by simp, by simp⟩
    · rw [ite_eq_right hc, ite_eq_right hc]
      obtain ⟨f1, f2, f3, L, f4, f5⟩ := flushCmd_same k st q b1 b2 (USize.ofNat (min sp 16777216))
      have e2 := cmd_er f1
      rw [f3] at e2
      rw [e2]
      generalize flushCmd k st b1 (USize.ofNat (min sp 16777216)) = r1 at f2 f4 ⊢
      generalize (flushCmd k { st with pos := q } b2 (USize.ofNat (min sp 16777216))).buf = c2 at f5 ⊢
      by_cases hl : r1.st.pend < st.pend
      · rw [dite_eq_left hl, dite_eq_left hl]
        obtain ⟨g1, g2, g3, g4, L', g5, g6⟩ := ih _ (by rw [← hN]; exact USize.lt_iff_toNat_lt.mp hl) r1.st q r1.buf c2
          (sp - (st.pend - r1.st.pend).toNat) rfl
        refine ⟨g1, g2.trans f2, g3, g4, L ++ L', ?_, ?_⟩
        · rw [g5, f4, List.append_assoc]
        · rw [g6, f5, List.append_assoc]
      · rw [dite_eq_right hl, dite_eq_right hl]
        exact ⟨rfl, f2, rfl, rfl, L, f4, f5⟩

/-- Handing a stream state's bytes out depends neither on its positions nor on what the buffer held. -/
theorem flushD_same {D1 D2 : Dec} (he : D1.er = D2.er) (b1 b2 : ByteArray) (sp : Nat) :
    (flushD D1 b1 sp).D.er = (flushD D2 b2 sp).D.er ∧ (flushD D1 b1 sp).D.pos = D1.pos ∧ (flushD D2 b2 sp).D.pos = D2.pos ∧
      (flushD D1 b1 sp).space = (flushD D2 b2 sp).space ∧
      ∃ L, (flushD D1 b1 sp).buf.data.toList = b1.data.toList ++ L ∧ (flushD D2 b2 sp).buf.data.toList = b2.data.toList ++ L := by
  rw [dec_er he]
  obtain ⟨f1, f2, f3, f4, L, f5, f6⟩ := flushAll_same D1.k _ D1.cmd D2.cmd.pos b1 b2 sp rfl
  unfold flushD
  dsimp only at f1 f2 f3 f4 f5 f6 ⊢
  refine ⟨?_, rfl, rfl, f4, L, f5, f6⟩
  have e2 := cmd_er f1
  rw [f3] at e2
  rw [e2]
  rfl

/-! ### A call -/

/-- Two calls' results the same but for their positions, which have the same unread bytes, with the same bytes added to
what each buffer held. -/
def OutSame (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (b1 b2 : ByteArray) (o1 o2 : Out) : Prop :=
  o1.D.er = o2.D.er ∧ Same a1 e1 a2 e2 o1.pos o2.pos ∧ o1.status = o2.status ∧
    ∃ L, o1.buf.data.toList = b1.data.toList ++ L ∧ o2.buf.data.toList = b2.data.toList ++ L

/-- Being at the stop, for positions with the same unread bytes. -/
theorem Same.eq_stop {a1 a2 : ByteArray} {e1 e2 p1 p2 : USize} (h : Same a1 e1 a2 e2 p1 p2) : p1 = e1 ↔ p2 = e2 := by
  obtain ⟨_, _, h3, h4, h5, _⟩ := h
  constructor
  · intro e
    subst e
    exact USize.toNat_inj.mp (by omega)
  · intro e
    subst e
    exact USize.toNat_inj.mp (by omega)

theorem endCheck_same {a1 a2 : ByteArray} {e1 e2 : USize} {D1 D2 : Dec} (he : D1.er = D2.er)
    (h : Same a1 e1 a2 e2 D1.pos D2.pos) (final : Bool) (c1 c2 : ByteArray) :
    (endCheck D1 e1 final c1).D.er = (endCheck D2 e2 final c2).D.er ∧
      Same a1 e1 a2 e2 (endCheck D1 e1 final c1).pos (endCheck D2 e2 final c2).pos ∧
      (endCheck D1 e1 final c1).status = (endCheck D2 e2 final c2).status ∧
      (endCheck D1 e1 final c1).buf = c1 ∧ (endCheck D2 e2 final c2).buf = c2 := by
  have hst := h.eq_stop
  rw [dec_er he] at hst ⊢
  generalize D2.pos = q0 at h hst ⊢
  generalize D2.cmd.pos = q1
  generalize D2.hd.pos = q2
  unfold endCheck
  dsimp only at hst ⊢
  by_cases hp : (BitBuffer.mk D1.cmd.word D1.cmd.count).peek (D1.cmd.count &&& 7) = 0
  · rw [ite_eq_left hp, ite_eq_left hp]
    by_cases hc : ((BitBuffer.mk D1.cmd.word D1.cmd.count).drop (D1.cmd.count &&& 7)).count = 0 ∧ D1.pos = e1
    · rw [ite_eq_left hc, ite_eq_left (show ((BitBuffer.mk D1.cmd.word D1.cmd.count).drop (D1.cmd.count &&& 7)).count = 0 ∧
        q0 = e2 from ⟨hc.1, hst.mp hc.2⟩)]
      cases final
      · exact ⟨rfl, h, rfl, rfl, rfl⟩
      · exact ⟨rfl, h, rfl, rfl, rfl⟩
    · rw [ite_eq_right hc, ite_eq_right (show ¬ (((BitBuffer.mk D1.cmd.word D1.cmd.count).drop (D1.cmd.count &&& 7)).count = 0 ∧
        q0 = e2) from fun e => hc ⟨e.1, hst.mpr e.2⟩)]
      exact ⟨rfl, h, rfl, rfl, rfl⟩
  · rw [ite_eq_right hp, ite_eq_right hp]
    exact ⟨rfl, h, rfl, rfl, rfl⟩

theorem afterRun_same {a1 a2 : ByteArray} {e1 e2 : USize} {r1 r2 : Dec} (he : r1.er = r2.er)
    (h : Same a1 e1 a2 e2 r1.pos r2.pos) (final : Bool) {q1 q2 : USize} (hq : Same a1 e1 a2 e2 q1 q2) (b1 b2 : ByteArray)
    (space : Nat) :
    OutSame a1 e1 a2 e2 b1 b2 (afterRun r1 e1 final q1 b1 space) (afterRun r2 e2 final q2 b2 space) := by
  have hstat : r2.status = r1.status := by rw [dec_er he]
  obtain ⟨f1, f2, f3, f4, L, f5, f6⟩ := flushD_same he b1 b2 space
  have hf : Same a1 e1 a2 e2 (flushD r1 b1 space).D.pos (flushD r2 b2 space).D.pos := by rw [f2, f3]; exact h
  have hpend : (flushD r2 b2 space).D.cmd.pend = (flushD r1 b1 space).D.cmd.pend := by rw [dec_er f1]
  unfold afterRun
  rw [hstat]
  cases r1.status
  · dsimp only
    by_cases hz : (flushD r1 b1 space).D.cmd.pend = 0
    · rw [ite_eq_left hz, ite_eq_left (hpend.trans hz)]
      obtain ⟨g1, g2, g3, g4, g5⟩ := endCheck_same f1 hf final (flushD r1 b1 space).buf (flushD r2 b2 space).buf
      exact ⟨g1, g2, g3, L, by rw [g4, f5], by rw [g5, f6]⟩
    · rw [ite_eq_right hz, ite_eq_right (fun e => hz (hpend.symm.trans e))]
      exact ⟨f1, hf, rfl, L, f5, f6⟩
  · dsimp only
    by_cases hz : (flushD r1 b1 space).D.cmd.pend = 0
    · rw [ite_eq_left hz, ite_eq_left (hpend.trans hz)]
      cases final
      · exact ⟨f1, hf, rfl, L, f5, f6⟩
      · exact ⟨rfl, hf, rfl, L, f5, f6⟩
    · rw [ite_eq_right hz, ite_eq_right (fun e => hz (hpend.symm.trans e))]
      exact ⟨f1, hf, rfl, L, f5, f6⟩
  · exact ⟨he, h, rfl, [], by simp, by simp⟩
  · exact ⟨rfl, hq, rfl, [], by simp, by simp⟩
  · exact ⟨rfl, hq, rfl, [], by simp, by simp⟩

theorem withCap_er (D : Dec) (space : Nat) :
    (withCap D space).er = { D.er with cmd := { D.er.cmd with cap := capFor space } } := rfl

theorem callD_same {a1 a2 : ByteArray} {e1 e2 : USize} (hs1 : e1.toNat ≤ a1.size) (hs2 : e2.toNat ≤ a2.size) (final : Bool) :
    ∀ (space : Nat) (D1 : Dec) (h1 : DInv e1 D1) (D2 : Dec) (h2 : DInv e2 D2) (b1 b2 : ByteArray), D1.er = D2.er →
    Same a1 e1 a2 e2 D1.pos D2.pos →
    OutSame a1 e1 a2 e2 b1 b2 (callD a1 e1 hs1 final D1 h1 b1 space) (callD a2 e2 hs2 final D2 h2 b2 space) := by
  intro space
  induction space using Nat.strongRecOn with
  | ind space ih =>
    intro D1 h1 D2 h2 b1 b2 he h
    rw [callD, callD]
    dsimp only
    have he' : (withCap D1 space).er = (withCap D2 space).er := by
      rw [withCap_er, withCap_er, he]
    obtain ⟨e, hS⟩ := runD_same hs1 hs2 ⟨withCap D1 space, h1.withCap space⟩ (withCap D2 space) (h2.withCap space) he' h
    dsimp only at e hS
    have hstat : (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)).status = (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)).status := by rw [dec_er e]
    by_cases hO : (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO, dite_eq_left (hstat.trans hO)]
      obtain ⟨f1, f2, f3, f4, L, f5, f6⟩ := flushD_same e b1 b2 space
      have hf : Same a1 e1 a2 e2 (flushD (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)) b1 space).D.pos (flushD (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)) b2 space).D.pos := by
        rw [f2, f3]
        exact hS
      have hpend : (flushD (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)) b2 space).D.cmd.pend = (flushD (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)) b1 space).D.cmd.pend := by
        rw [dec_er f1]
      by_cases hz : (flushD (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)) b1 space).D.cmd.pend = 0
      · rw [ite_eq_left hz, ite_eq_left (hpend.trans hz)]
        by_cases hlt : (flushD (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)) b1 space).space < space
        · rw [dite_eq_left hlt, dite_eq_left (show (flushD (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)) b2 space).space < space by rw [← f4]; exact hlt)]
          rw [← f4]
          obtain ⟨g1, g2, g3, L', g4, g5⟩ := ih _ hlt _ (flushD_inv (runD_full hO) b1 space) _
            (flushD_inv (runD_full (hstat.trans hO)) b2 space) (flushD (runD a1 e1 hs1 (withCap D1 space) (h1.withCap space)) b1 space).buf
            (flushD (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)) b2 space).buf f1 hf
          exact ⟨g1, g2, g3, L ++ L', by rw [g4, f5, List.append_assoc], by rw [g5, f6, List.append_assoc]⟩
        · rw [dite_eq_right hlt, dite_eq_right (show ¬ (flushD (runD a2 e2 hs2 (withCap D2 space) (h2.withCap space)) b2 space).space < space by rw [← f4]; exact hlt)]
          exact ⟨rfl, h, rfl, L, f5, f6⟩
      · rw [ite_eq_right hz, ite_eq_right (fun e => hz (hpend.symm.trans e))]
        exact ⟨f1, hf, rfl, L, f5, f6⟩
    · rw [dite_eq_right hO, dite_eq_right (fun e => hO (hstat.symm.trans e))]
      exact afterRun_same e hS final h b1 b2 space

/-! ### What the caller sees -/

theorem atPos_er (D : Dec) (p : Nat) : (atPos D p).er = D.er := rfl

/-- Two calls that give the same chunk start with the same unread bytes. -/
theorem input_same {x : List UInt8} {R1 R2 : Run DState} {c1 c2 : Call} (hr : R1.read = R2.read) (hsz : c1.size = c2.size)
    (h1 : R1.Allowed x c1) (h2 : R2.Allowed x c2) :
    Same (R1.input x c1) (USize.ofNat (c1.pre.length + c1.size)) (R2.input x c2) (USize.ofNat (c2.pre.length + c2.size))
      (USize.ofNat c1.pre.length) (USize.ofNat c2.pre.length) := by
  have hin1 := h1.inside
  have hin2 := h2.inside
  have hf1 := h1.fits
  have hf2 := h2.fits
  have u1 : (USize.ofNat (c1.pre.length + c1.size)).toNat = c1.pre.length + c1.size := usize_of (by omega)
  have u2 : (USize.ofNat (c2.pre.length + c2.size)).toNat = c2.pre.length + c2.size := usize_of (by omega)
  have v1 : (USize.ofNat c1.pre.length).toNat = c1.pre.length := usize_of (by omega)
  have v2 : (USize.ofNat c2.pre.length).toNat = c2.pre.length := usize_of (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u1, input_size hin1]
    omega
  · rw [u2, input_size hin2]
    omega
  · rw [v1, u1]
    omega
  · rw [v2, u2]
    omega
  · rw [v1, u1, v2, u2]
    omega
  · rw [v1, u1, v2, u2]
    have k1 := chunk_input (R := R1) (c := c1) hin1 (Nat.zero_le _)
    have k2 := chunk_input (R := R2) (c := c2) hin2 (Nat.zero_le _)
    rw [Nat.add_zero] at k1 k2
    rw [k1, k2, hr, hsz]

theorem decStep_eq (s : DState) (a : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat) (final : Bool)
    (h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size) :
    decStep s a start stop buf space final =
      { state := ⟨(callD a (USize.ofNat stop) (by rw [usize_of h.2.2]; exact h.1) final (atPos s.val start)
            (atPos_inv s h.2.1 h.2.2) buf space).D, callD_rel _ _ _⟩
        used := (callD a (USize.ofNat stop) (by rw [usize_of h.2.2]; exact h.1) final (atPos s.val start)
            (atPos_inv s h.2.1 h.2.2) buf space).pos.toNat - start
        output := (callD a (USize.ofNat stop) (by rw [usize_of h.2.2]; exact h.1) final (atPos s.val start)
            (atPos_inv s h.2.1 h.2.2) buf space).buf
        status := (callD a (USize.ofNat stop) (by rw [usize_of h.2.2]; exact h.1) final (atPos s.val start)
            (atPos_inv s h.2.1 h.2.2) buf space).status } := by
  unfold decStep
  rw [dite_eq_left h]

/-- Two calls from states the same but for their positions, giving the same chunk, space and end flag, reply the same. -/
theorem reply_same {x : List UInt8} {R1 R2 : Run DState} {c1 c2 : Call} (he : R1.state.val.er = R2.state.val.er)
    (hr : R1.read = R2.read) (h1 : R1.Allowed x c1) (h2 : R2.Allowed x c2) (hsz : c1.size = c2.size)
    (hsp : c1.space = c2.space) (hf : c1.final = c2.final) :
    (R1.reply decoder x c1).state.val.er = (R2.reply decoder x c2).state.val.er ∧
      (R1.reply decoder x c1).used = (R2.reply decoder x c2).used ∧
      (R1.reply decoder x c1).status = (R2.reply decoder x c2).status ∧
      (R1.reply decoder x c1).output.data.toList.drop c1.buf.length =
        (R2.reply decoder x c2).output.data.toList.drop c2.buf.length := by
  have hin1 := h1.inside
  have hin2 := h2.inside
  have hf1 := h1.fits
  have hf2 := h2.fits
  have hg1 : c1.pre.length + c1.size ≤ (R1.input x c1).size ∧ c1.pre.length ≤ c1.pre.length + c1.size ∧
      c1.pre.length + c1.size < USize.size := ⟨by rw [input_size hin1]; omega, by omega, by omega⟩
  have hg2 : c2.pre.length + c2.size ≤ (R2.input x c2).size ∧ c2.pre.length ≤ c2.pre.length + c2.size ∧
      c2.pre.length + c2.size < USize.size := ⟨by rw [input_size hin2]; omega, by omega, by omega⟩
  have hs1 : (USize.ofNat (c1.pre.length + c1.size)).toNat ≤ (R1.input x c1).size := by rw [usize_of hg1.2.2]; exact hg1.1
  have hs2 : (USize.ofNat (c2.pre.length + c2.size)).toNat ≤ (R2.input x c2).size := by rw [usize_of hg2.2.2]; exact hg2.1
  obtain ⟨o1, o2, o3, L, o4, o5⟩ := callD_same hs1 hs2 c1.final c1.space (atPos R1.state.val c1.pre.length)
    (atPos_inv R1.state hg1.2.1 hg1.2.2) (atPos R2.state.val c2.pre.length) (atPos_inv R2.state hg2.2.1 hg2.2.2)
    c1.buf.toByteArray c2.buf.toByteArray he (input_same hr hsz h1 h2)
  rw [show R1.reply decoder x c1 = decStep R1.state (R1.input x c1) c1.pre.length (c1.pre.length + c1.size)
      c1.buf.toByteArray c1.space c1.final from rfl, decStep_eq _ _ _ _ _ _ _ hg1,
    show R2.reply decoder x c2 = decStep R2.state (R2.input x c2) c2.pre.length (c2.pre.length + c2.size)
      c2.buf.toByteArray c2.space c2.final from rfl, decStep_eq _ _ _ _ _ _ _ hg2, ← hsp, ← hf]
  dsimp only
  have u1 : (USize.ofNat (c1.pre.length + c1.size)).toNat = c1.pre.length + c1.size := usize_of (by omega)
  have u2 : (USize.ofNat (c2.pre.length + c2.size)).toNat = c2.pre.length + c2.size := usize_of (by omega)
  obtain ⟨_, _, q3, q4, q5, _⟩ := o2
  rw [u1] at q3 q5
  rw [u2] at q4 q5
  have l1 : c1.buf.toByteArray.data.toList = c1.buf := by simp [List.data_toByteArray]
  have l2 : c2.buf.toByteArray.data.toList = c2.buf := by simp [List.data_toByteArray]
  rw [l1] at o4
  rw [l2] at o5
  refine ⟨o1, by omega, o3, ?_⟩
  rw [o4, o5, List.drop_left, List.drop_left]

/-- The decoder's replies depend only on the chunks, space and end flags it is given. -/
theorem decoder_layoutBlind : LayoutBlind decoder := by
  intro limit x R1 R2 h
  have key : R1.state.val.er = R2.state.val.er ∧ R1.status = R2.status ∧ R1.read = R2.read ∧ R1.emitted = R2.emitted := by
    induction h with
    | start => exact ⟨rfl, rfl, rfl, rfl⟩
    | call _ a1 a2 hsz hsp hf ih =>
      obtain ⟨i1, _, i3, i4⟩ := ih
      obtain ⟨r1, r2, r3, r4⟩ := reply_same i1 i3 a1 a2 hsz hsp hf
      refine ⟨r1, r3, ?_, ?_⟩
      · show _ + _ = _ + _
        rw [i3, r2]
      · show _ ++ _ = _ ++ _
        rw [i4, r4]
  exact key.2

end Brotli.Decoder
