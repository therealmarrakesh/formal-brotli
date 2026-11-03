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

end Brotli.Decoder
