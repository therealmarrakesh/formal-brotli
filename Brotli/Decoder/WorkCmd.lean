module

public import Brotli.Decoder.Work
public import Brotli.Decoder.CostHeader

@[expose] public section

/-!
# The work of a meta-block's commands

Each function here mirrors the command loop's step or helper of the same name without its `W`, branch by branch, and
counts the rounds of its loops. A step's work is a constant, ten for each byte it adds to the window, and for a step that
begins a dictionary word, the word's building.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The loops -/

/-- The work of `literalRun`: a refill and a round for each literal, and one for the round that stops it. -/
def literalRunW {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : Nat :=
  if hn : n = 0 then 1
  else
    let r := refill word count a pos stop hs hp
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    have hspec := refill_spec hs hp hw
    let cid := cidFast modeOff p1 p2 hm
    have hcid : cid.toNat < 64 := cid_lt hm hd
    have hi : (mapIndex mapBase cid).toNat < lMap.size := by
      rw [mapIndex_toNat (by have := C.map32; omega)]
      omega
    let tree := lMap.uget (mapIndex mapBase cid) hi
    have htree : tree.toNat < nTrees := C.treeLt _ hi
    have hb : 4 * tree.toNat + 4 ≤ litBase.size := by
      rw [C.baseSize]
      omega
    let base := treeBase litBase tree hb C.base32
    have hfit : TableFits arena base.toNat := by
      rw [treeBase_toNat]
      exact C.fits _ htree
    let v := lookup arena base rw hfit C.arena32
    let l := v &&& 15
    if hl : l ≤ rc then
      let byte := (v >>> 4).toUInt8
      have hl63 : l.toNat < 64 := by
        have : (v &&& 15).toNat = v.toNat % 16 := by
          rw [UInt64.toNat_and]
          exact Nat.and_two_pow_sub_one_eq_mod v.toNat 4
        show (v &&& 15).toNat < 64
        omega
      have hr : wpos.toNat < ring.size := by omega
      let ring' := ringWrite ring wpos byte hr
      have hsize' : ring'.size = 2 ^ k := (size_ringWrite ring wpos byte hr).trans hsize
      have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
        unfold ringNext
        rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      let b := (BitBuffer.mk rw rc).drop l
      refillW word count a pos stop hs + 1 +
        literalRunW C a stop hs mapBase modeOff mask k hmb hm hd hmask hk (n - USize.ofNat 1) b.word b.count rp (ringNext wpos mask) ring'
          byte p1 hspec.2.2.1 (BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl)) hsize' hnext
    else refillW word count a pos stop hs + 1
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

/-- The literal loop's work: two for each literal it writes, two, and a round for each byte its refills take. -/
theorem literalRunW_le {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    literalRunW C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp +
      2 * (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤
      2 * N + 2 + ((literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).pos.toNat -
        pos.toNat) ∧
    pos.toNat ≤ (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).pos.toNat := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [literalRunW, dite_eq_left hz, literalRun, dite_eq_left hz]
    show 1 + 2 * (0 : USize).toNat ≤ _ ∧ _
    rw [show (0 : USize).toNat = 0 from rfl]
    exact ⟨by omega, Nat.le_refl _⟩
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hR := refillW_take (word := word) (count := count) hs hp
    have hq := (refill_spec hs hp hw).2.1
    rw [literalRunW, dite_eq_right hn, literalRun, dite_eq_right hn]
    dsimp only
    split
    · obtain ⟨i1, i2⟩ := ih _ _ _ _ _ _ _ _ _ _ _ _ (by rw [hpred]; omega)
      constructor
      · rw [Nat.add_assoc]
        refine Nat.le_trans (Nat.add_le_add_left i1 _) ?_
        omega
      · omega
    · show refillW word count a pos stop hs + 1 + 2 * n.toNat ≤ _ ∧ _
      dsimp only
      omega

/-- The literal loop leaves at most the literals it was given. -/
theorem literalRun_left_le {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤ N := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [literalRun, dite_eq_left hz]
    show (0 : USize).toNat ≤ 0
    exact Nat.le_refl _
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [literalRun, dite_eq_right hn]
    dsimp only
    split
    · exact Nat.le_trans (ih _ _ _ _ _ _ _ _ _ _ _ _ (by omega)) (Nat.le_succ _)
    · show n.toNat ≤ _
      omega

/-! ### A dictionary word -/

/-- The work of `elementStep`: a round for each byte of the run, and the first byte's ferment. -/
def elementStepW (kind : UInt8) (len : USize) : Nat :=
  if kind = 1 then len.toNat + 2 else len.toNat + 1

/-- The work of `buildWord`: the buffer's 38 bytes, then a round for each byte of the prefix, the run and the suffix. -/
def buildWordW (id len : USize) : Nat :=
  let base := id * USize.ofNat 32
  38 + (getU transLut (base + USize.ofNat 2)).toNat + elementStepW (getU transLut base) len +
    (getU transLut (base + USize.ofNat 3)).toNat + 1

/-- The work of `dictBuild`. -/
def dictBuildW (clen wordId : UInt64) (h : dictValid clen wordId) : Nat :=
  buildWordW (dictTid (lenRow clen (lt25 h.1)) wordId).toUSize clen.toUSize

private theorem base_plus {id : USize} (hid : id.toNat < 121) (j : Nat) (hj : j < 32) :
    (id * USize.ofNat 32 + USize.ofNat j).toNat = 32 * id.toNat + j := by
  have hs := USize.le_size
  have e32 : (USize.ofNat 32).toNat = 32 := usize_ofNat' (by decide)
  have ej : (USize.ofNat j).toNat = j := usize_ofNat' (by omega)
  have hmul : (id * USize.ofNat 32).toNat = 32 * id.toNat := by
    rw [USize.toNat_mul, e32, Nat.mul_comm, ← USize.size_eq_two_pow]
    exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_add, hmul, ej, ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (by omega)

/-- A dictionary word's building: at most 78 rounds. -/
theorem dictBuildW_le (clen wordId : UInt64) (h : dictValid clen wordId) : dictBuildW clen wordId h ≤ 78 := by
  obtain ⟨hc, ht⟩ := h
  have hid : (dictTid (lenRow clen (lt25 hc)) wordId).toUSize.toNat < 121 := by
    rw [word_toUSize (by have := lt121 ht; omega)]
    exact lt121 ht
  have hl : clen.toUSize.toNat ≤ 24 := by
    rw [word_toUSize (by have := lt25 hc; omega)]
    have := lt25 hc
    omega
  unfold dictBuildW buildWordW elementStepW
  generalize (dictTid (lenRow clen (lt25 hc)) wordId).toUSize = id at hid ⊢
  generalize clen.toUSize = len at hl ⊢
  have h2 : (getU transLut (id * USize.ofNat 32 + USize.ofNat 2)).toNat = (transLut.data[32 * id.toNat + 2]?.getD 0).toNat := by
    rw [getU_toNat, base_plus hid 2 (by decide)]
  have h3 : (getU transLut (id * USize.ofNat 32 + USize.ofNat 3)).toNat = (transLut.data[32 * id.toNat + 3]?.getD 0).toNat := by
    rw [getU_toNat, base_plus hid 3 (by decide)]
  have := affix_le hid
  dsimp only
  rw [h2, h3]
  split <;> omega

/-! ### The steps -/

/-- The work of `applyWord`: the word's building. -/
def applyWordW (st : Cmd) (wordId : UInt64) : Nat :=
  if h : dictValid st.clen wordId then dictBuildW st.clen wordId h + 1 else 1

/-- The work of `applyDistance`. -/
def applyDistanceW (st : Cmd) (d : UInt64) : Nat :=
  if st.written.toUInt64 < d then applyWordW st (d - (st.written.toUInt64 + 1)) else 1

/-- The work of `distanceStep`. -/
def distanceStepW (H : Hdr) (st : Cmd) (v : UInt64) : Nat :=
  if wordBits v ≤ st.count then
    let nbits := extraBitsFast H.npostfix H.ndirect (wordSym v)
    let b1 := (BitBuffer.mk st.word st.count).drop (wordBits v)
    if nbits ≤ 24 then
      if nbits ≤ b1.count then
        let b2 := b1.drop nbits
        let d := distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v) (b1.peek nbits)
        if d = 0 then 1 else applyDistanceW (setBits st b2.word b2.count) d
      else 1
    else 1
  else 1

/-- The work of `distanceThrough`. -/
def distanceThroughW (H : Hdr) (st : Cmd) (tree : UInt8) (htree : tree.toNat < H.treesD.toNat) : Nat :=
  have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
    rw [H.dSize, UInt8.toNat_toUInt64]
    omega
  have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
    rw [tableBase_toNat, UInt8.toNat_toUInt64]
    exact H.dFits _ htree
  distanceStepW H st (lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) st.word hfit H.lit.arena32)

/-- The work of `stepDistanceSymbol`. -/
def stepDistanceSymbolW (H : Hdr) (st : Cmd) : Nat :=
  if ht : st.dCur < H.nD then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hi : (dMapIndex st.dCur st.clen).toNat < H.dMap.size := by
      have h1 := H.dMap32
      have h2 := H.dMapSize
      have hcid := distanceContextId_lt st.clen.toNat
      rw [dMapIndex_toNat (by omega)]
      omega
    distanceThroughW H st (H.dMap.uget (dMapIndex st.dCur st.clen) hi) (H.dMapLt _ hi)
  else 1

/-- The work of `stepDistance`. -/
def stepDistanceW (st : Cmd) : Nat :=
  if st.remaining = 0 then 1
  else if st.code < 128 then (if st.d0 = 0 then 1 else applyDistanceW st st.d0)
  else 1

/-- The work of `literalsRun`. -/
def literalsRunW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if ht : st.lCur < H.nL then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hm : st.lCur.toUSize.toNat < H.modes.size := by
      rw [cur_usize ht', H.modesSize]
      exact ht'
    have hmLt := H.modesLt _ hm
    if h : winCheck k st.wpos st.ring = true ∧ pos ≤ stop ∧ wfCheck st.word st.count = true then
      let run := (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize
      let ring := st.ring
      let st0 := clearRing st
      literalRunW H.lit a stop hs (st.lCur <<< 6).toUSize ((H.modes.uget st.lCur.toUSize hm).toUInt64 <<< 9).toUSize
        (ringMask k) k.toNat
        (by
          rw [mapBase_toNat ht', H.lMapSize]
          omega)
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (ringMask_toNat (winCheck_k h.1)) (winCheck_k h.1) run st0.word st0.count pos st0.wpos ring st0.p1 st0.p2
        (USize.le_iff_toNat_le.mp h.2.1) (wfCheck_wf h.2.2) (winCheck_size h.1) (winCheck_pos h.1) + 1
    else 1
  else 1

/-- The work of `stepLiterals`. -/
def stepLiteralsW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if st.left = 0 then 1
  else if st.lCount = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else literalsRunW H k a stop hs st pos

/-- The work of `stepCopy`: a round for each byte copied. -/
def stepCopyW (k : USize) (st : Cmd) : Nat :=
  if st.left = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else
    let run := (umin st.left (room k st.cap - st.pend).toUInt64).toUSize
    let d := st.dist.toUSize
    if winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ d ∧ d ≤ ringSize k then run.toNat + 1 else 1

/-- The work of `stepWord`: a round for each byte written. -/
def stepWordW (k : USize) (st : Cmd) : Nat :=
  let n := st.wordBuf.usize - st.wordPos
  if n = 0 then 1
  else if room k st.cap ≤ st.pend then 1
  else
    let run := usmin n (room k st.cap - st.pend)
    if winCheck k st.wpos st.ring = true ∧ st.wordPos.toNat + run.toNat ≤ st.wordBuf.size ∧
        st.wordPos.toNat + run.toNat ≤ 2 ^ 32 - 1 then run.toNat + 1 else 1

/-- The work of a command loop step, once the buffer is refilled. -/
def stepAtW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  match st.tag with
  | .command => 1
  | .insertCopy => 1
  | .copyLength => 1
  | .literals => stepLiteralsW H k a stop hs st pos
  | .distance => stepDistanceW st
  | .distanceSymbol => stepDistanceSymbolW H st
  | .copy => stepCopyW k st
  | .word => stepWordW k st

/-- The work of a command loop step: the refill, then the step. -/
def stepCmdW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Nat :=
  if hp : pos ≤ stop then
    let r := refill st.word st.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    refillW st.word st.count a pos stop hs + stepAtW H k a stop hs { st with word := r.word, count := r.count } r.pos
  else 1

/-- The work of the command loop: its rounds, and each one's step. -/
def runCmdW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd) (pos : USize) :
    Nat :=
  if _hn : n = 0 then 1
  else
    let r := stepCmd H k a stop hs st pos
    stepCmdW H k a stop hs st pos + 1 +
      match r.status with
      | .next => runCmdW H k a stop hs (n - USize.ofNat 1) r r.pos
      | _ => 0
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-! ### A step's work -/

/-- A distance's copy: a dictionary word is built only when the step goes on to its bytes or stops. -/
theorem applyDistanceW_le (st : Cmd) (pos : USize) (dc d : UInt64) :
    applyDistanceW st d ≤ 1 + (if (applyDistance st pos dc d).status = .next ∧ (applyDistance st pos dc d).tag ≠ .word then 0 else 79) ∧
      (applyDistance st pos dc d).pend = st.pend := by
  unfold applyDistanceW applyDistance
  by_cases hw : st.written.toUInt64 < d
  · rw [ite_eq_left hw, ite_eq_left hw]
    unfold applyWordW applyWord
    by_cases hv : dictValid st.clen (d - (st.written.toUInt64 + 1))
    · rw [dite_eq_left hv, dite_eq_left hv]
      have := dictBuildW_le st.clen (d - (st.written.toUInt64 + 1)) hv
      unfold applyBuilt
      split
      · refine ⟨?_, rfl⟩
        rw [ite_eq_right (fun h => StepStatus.noConfusion h.1)]
        omega
      · refine ⟨?_, rfl⟩
        rw [ite_eq_right (fun h => h.2 rfl)]
        omega
    · rw [dite_eq_right hv, dite_eq_right hv]
      exact ⟨by omega, rfl⟩
  · rw [ite_eq_right hw, ite_eq_right hw]
    split
    · exact ⟨by omega, rfl⟩
    · split
      · exact ⟨by omega, rfl⟩
      · exact ⟨by omega, rfl⟩

/-- A run that fits the room left: adding it to the bytes waiting doesn't wrap. -/
theorem pend_add {pend run : USize} (h : pend.toNat + run.toNat ≤ 2 ^ 24) : (pend + run).toNat = pend.toNat + run.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- A run of at most the room left, as an index. -/
theorem run_le {k cap pend : USize} {x : UInt64} (hk : k.toNat ≤ 24) (hr : ¬ room k cap ≤ pend) :
    (umin x (room k cap - pend).toUInt64).toUSize.toNat ≤ (room k cap).toNat - pend.toNat := by
  have h1 := room_lt hr
  have h2 := room_le (cap := cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hs : (room k cap - pend).toNat = (room k cap).toNat - pend.toNat := room_sub' (by omega)
  have hm := umin_toNat x (room k cap - pend).toUInt64
  rw [USize.toNat_toUInt64, hs] at hm
  have h4 : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
  rw [word_toUSize (by rw [hm]; omega), hm]
  omega

/-- The bytes a step adds to the window, counted when it doesn't reject. -/
def addedW (pend : USize) (r : Cmd) : Nat := if r.status = .bad then 0 else r.pend.toNat - pend.toNat

theorem copyW_le {k : USize} {st : Cmd} {pos : USize} (hk : k.toNat ≤ 24) :
    stepCopyW k st ≤ 1 + addedW st.pend (stepCopy k st pos) := by
  unfold addedW
  unfold stepCopyW stepCopy
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr, ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  dsimp only
  have hrun := run_le (x := st.left) hk hr
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  generalize (umin st.left (room k st.cap - st.pend).toUInt64).toUSize = run at hrun ⊢
  by_cases hc : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ st.dist.toUSize ∧ st.dist.toUSize ≤ ringSize k
  · rw [ite_eq_left hc, dite_eq_left hc]
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    show _ ≤ 1 + ((((clearRing st).pend + run)).toNat - st.pend.toNat)
    rw [show (clearRing st).pend = st.pend from rfl, pend_add (by omega)]
    omega
  · rw [ite_eq_right hc, dite_eq_right hc]
    split <;> omega

theorem wordW_le {k : USize} {st : Cmd} {pos : USize} (hk : k.toNat ≤ 24) :
    stepWordW k st ≤ 1 + addedW st.pend (stepWord k st pos) := by
  unfold addedW
  unfold stepWordW stepWord
  dsimp only
  by_cases h0 : st.wordBuf.usize - st.wordPos = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr, ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hs : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
  have hrun : (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ (room k st.cap).toNat - st.pend.toNat := by
    rw [usmin_toNat, hs]
    omega
  by_cases hc : winCheck k st.wpos st.ring = true ∧
      st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ st.wordBuf.size ∧
      st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ 2 ^ 32 - 1
  · rw [ite_eq_left hc, dite_eq_left hc]
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    show _ ≤ 1 + (((clearRing st).pend + usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat - st.pend.toNat)
    rw [show (clearRing st).pend = st.pend from rfl, pend_add (by omega)]
    omega
  · rw [ite_eq_right hc, dite_eq_right hc]
    split <;> omega

/-- A literal step's work: three, two for each byte it adds and a round for each byte its refills take, and one for a step
that goes on having added none: a run of literals goes on only once it has written them all. -/
theorem literalsW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepLiteralsW H k a stop hs st pos ≤
      if (stepLiterals H k a stop hs st pos).status = .next ∧ addedW st.pend (stepLiterals H k a stop hs st pos) = 0 then 1
      else 3 + 2 * addedW st.pend (stepLiterals H k a stop hs st pos) + ((stepLiterals H k a stop hs st pos).pos.toNat - pos.toNat) := by
  have one : ∀ (c : Prop) [Decidable c] (x y : Nat), 1 ≤ if c then 1 else 3 + 2 * x + y := fun c _ x y => by split <;> omega
  unfold addedW
  unfold stepLiteralsW stepLiterals
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    exact one _ _ _
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hc : st.lCount = 0
  · rw [ite_eq_left hc]
    exact one _ _ _
  rw [ite_eq_right hc, ite_eq_right hc]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr]
    exact one _ _ _
  rw [ite_eq_right hr, ite_eq_right hr]
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  unfold literalsRunW literalsRun
  split
  · split
    · dsimp only
      simp only [literalRunS_eq]
      have hs : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
      have hm1 := umin_toNat st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)
      have hm2 := umin_toNat st.lCount (room k st.cap - st.pend).toUInt64
      have h4 : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
      rw [USize.toNat_toUInt64, hs] at hm2
      have hl0 : st.left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      have hc0 : st.lCount.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp (by rw [e]; rfl))
      have hrun' : (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize.toNat ≤
          (room k st.cap).toNat - st.pend.toNat ∧ 1 ≤ (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize.toNat := by
        rw [word_toUSize (by rw [hm1, hm2]; omega), hm1, hm2]
        omega
      generalize (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize = run at hrun' ⊢
      have key : ∀ (W : Nat) (L : LitRun), W + 2 * L.left.toNat ≤ 2 * run.toNat + 2 + (L.pos.toNat - pos.toNat) →
          L.left.toNat ≤ run.toNat →
          W + 1 ≤ if (finishLiterals (clearRing st) L run (ringSize k)).status = .next ∧
              (if (finishLiterals (clearRing st) L run (ringSize k)).status = .bad then 0
                else (finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat) = 0 then 1
            else 3 + 2 * (if (finishLiterals (clearRing st) L run (ringSize k)).status = .bad then 0
              else (finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat) +
              ((finishLiterals (clearRing st) L run (ringSize k)).pos.toNat - pos.toNat) := by
        intro W L hW hL
        have hnb : (finishLiterals (clearRing st) L run (ringSize k)).status ≠ .bad := by
          unfold finishLiterals
          dsimp only
          split <;> exact fun e => StepStatus.noConfusion e
        have hsub : (run - L.left).toNat = run.toNat - L.left.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hL)
        have hpe : (finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat = run.toNat - L.left.toNat := by
          show ((clearRing st).pend + (run - L.left)).toNat - st.pend.toNat = _
          rw [show (clearRing st).pend = st.pend from rfl, pend_add (by rw [hsub]; omega), hsub]
          omega
        have hnx : ¬ ((finishLiterals (clearRing st) L run (ringSize k)).status = .next ∧
            (if (finishLiterals (clearRing st) L run (ringSize k)).status = .bad then 0
              else (finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat) = 0) := by
          rintro ⟨hn, hz⟩
          rw [ite_eq_right hnb, hpe] at hz
          have hst : (finishLiterals (clearRing st) L run (ringSize k)).status = if L.left = 0 then .next else .needsInput := rfl
          rw [hst] at hn
          by_cases hl : L.left = 0
          · rw [hl] at hz
            rw [show (0 : USize).toNat = 0 from rfl] at hz
            omega
          · rw [ite_eq_right hl] at hn
            exact StepStatus.noConfusion hn
        rw [ite_eq_right hnx, ite_eq_right hnb, hpe]
        show W + 1 ≤ 3 + 2 * (run.toNat - L.left.toNat) + (L.pos.toNat - pos.toNat)
        omega
      exact key _ _ (literalRunW_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).1
        (literalRun_left_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
    · dsimp only
      exact one _ _ _
  · exact one _ _ _

/-- The word cost a step may have: none when it goes on to anything but a word's bytes. -/
def wordCost (t : Tag) (r : Cmd) : Nat := if r.status = .next ∧ ¬ (r.tag = .word ∧ t ≠ .word) then 0 else 80

/-- The word cost a step may have, counted only when it adds no byte to the window: a step that builds a word adds none. -/
def wcost (pend : USize) (t : Tag) (r : Cmd) : Nat := if r.pend = pend then wordCost t r else 0

theorem distanceW_le {H : Hdr} {st : Cmd} {pos : USize} (ht : st.tag = .distance) :
    stepDistanceW st ≤ 1 + (wordCost st.tag (stepDistance H st pos) - 1) ∧ (stepDistance H st pos).pend = st.pend := by
  unfold stepDistanceW stepDistance wordCost
  by_cases h0 : st.remaining = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    exact ⟨by omega, rfl⟩
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hc : st.code < 128
  · rw [ite_eq_left hc, ite_eq_left hc]
    by_cases hd : st.d0 = 0
    · rw [ite_eq_left hd, ite_eq_left hd]
      exact ⟨by omega, rfl⟩
    · rw [ite_eq_right hd, ite_eq_right hd]
      obtain ⟨h1, h2⟩ := applyDistanceW_le st pos 0 st.d0
      refine ⟨?_, h2⟩
      have hne : (st.tag ≠ .word) := by rw [ht]; exact fun e => Tag.noConfusion e
      split
      · rename_i hh
        have : (applyDistance st pos 0 st.d0).tag ≠ .word := fun e => hh.2 ⟨e, hne⟩
        rw [ite_eq_left ⟨hh.1, this⟩] at h1
        omega
      · split at h1 <;> omega
  · rw [ite_eq_right hc, ite_eq_right hc]
    refine ⟨by omega, ?_⟩
    dsimp only
    repeat' split
    all_goals rfl

theorem distanceStepW_le {H : Hdr} {st : Cmd} {pos : USize} {v : UInt64} (ht : st.tag ≠ .word) :
    distanceStepW H st v ≤ 1 + (wordCost st.tag (distanceStep H st pos v) - 1) ∧ (distanceStep H st pos v).pend = st.pend := by
  unfold distanceStepW distanceStep wordCost
  by_cases h1 : wordBits v ≤ st.count
  · rw [ite_eq_left h1, ite_eq_left h1]
    dsimp only
    by_cases h2 : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ 24
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ ((BitBuffer.mk st.word st.count).drop (wordBits v)).count
      · rw [ite_eq_left h3, ite_eq_left h3]
        generalize distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v)
          (((BitBuffer.mk st.word st.count).drop (wordBits v)).peek (extraBitsFast H.npostfix H.ndirect (wordSym v))) = d
        by_cases h4 : d = 0
        · rw [ite_eq_left h4, ite_eq_left h4]
          exact ⟨by omega, rfl⟩
        · rw [ite_eq_right h4, ite_eq_right h4]
          have key : ∀ st' : Cmd, st'.pend = st.pend →
              applyDistanceW st' d ≤ 1 + ((if (applyDistance st' pos (wordSym v) d).status = .next ∧
                ¬ ((applyDistance st' pos (wordSym v) d).tag = .word ∧ st.tag ≠ .word) then 0 else 80) - 1) ∧
              (applyDistance st' pos (wordSym v) d).pend = st.pend := by
            intro st' hp
            obtain ⟨e1, e2⟩ := applyDistanceW_le st' pos (wordSym v) d
            refine ⟨?_, e2.trans hp⟩
            by_cases hh : (applyDistance st' pos (wordSym v) d).status = .next ∧
                (applyDistance st' pos (wordSym v) d).tag ≠ .word
            · rw [ite_eq_left hh] at e1
              omega
            · rw [ite_eq_right hh] at e1
              have : ¬ ((applyDistance st' pos (wordSym v) d).status = .next ∧
                  ¬ ((applyDistance st' pos (wordSym v) d).tag = .word ∧ st.tag ≠ .word)) :=
                fun h => hh ⟨h.1, fun e => h.2 ⟨e, ht⟩⟩
              rw [ite_eq_right this]
              omega
          exact key _ rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        exact ⟨by omega, rfl⟩
    · rw [ite_eq_right h2, ite_eq_right h2]
      exact ⟨by omega, rfl⟩
  · rw [ite_eq_right h1, ite_eq_right h1]
    exact ⟨by omega, rfl⟩

theorem distanceSymbolW_le {H : Hdr} {st : Cmd} {pos : USize} (ht : st.tag = .distanceSymbol) :
    stepDistanceSymbolW H st ≤ 1 + (wordCost st.tag (stepDistanceSymbol H st pos) - 1) ∧
      (stepDistanceSymbol H st pos).pend = st.pend := by
  have hne : st.tag ≠ .word := by rw [ht]; exact fun e => Tag.noConfusion e
  unfold stepDistanceSymbolW stepDistanceSymbol
  by_cases hd : st.dCur < H.nD
  · rw [dite_eq_left hd, dite_eq_left hd]
    unfold distanceThroughW distanceThrough
    exact distanceStepW_le hne
  · rw [dite_eq_right hd, dite_eq_right hd]
    exact ⟨by unfold wordCost; split <;> omega, rfl⟩

/-- A literal step goes no further back than where it starts. -/
theorem stepLiterals_ge {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} :
    pos.toNat ≤ (stepLiterals H k a stop hs st pos).pos.toNat := by
  unfold stepLiterals literalsRun
  repeat' (first | split | dsimp only)
  all_goals first
    | exact Nat.le_refl _
    | (rw [literalRunS_eq]; exact (literalRunW_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).2)

/-- A command loop step goes no further back than where it starts. -/
theorem stepAt_ge {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} :
    pos.toNat ≤ (stepAt H k a stop hs st pos).pos.toNat := by
  unfold stepAt
  cases st.tag with
  | command => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepCommand_pos H st pos)).trans rfl)).symm
  | insertCopy => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepInsertCopy_pos H st pos)).trans rfl)).symm
  | copyLength => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepCopyLength_pos st pos)).trans rfl)).symm
  | literals => exact stepLiterals_ge
  | distance => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepDistance_pos H st pos)).trans rfl)).symm
  | distanceSymbol =>
    exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepDistanceSymbol_pos H st pos)).trans rfl)).symm
  | copy => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepCopy_pos k st pos)).trans rfl)).symm
  | word => exact Nat.le_of_eq (congrArg USize.toNat ((congrArg Cmd.pos (stepWord_pos k st pos)).trans rfl)).symm

/-- A command loop step's work, once the buffer is refilled: three, two for each byte it adds to the window, a round for
each byte its literals' refills take, and a dictionary word's building when it begins one or stops having added no byte. -/
theorem stepAtW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepAtW H k a stop hs st pos ≤
      3 + 2 * addedW st.pend (stepAt H k a stop hs st pos) + wcost st.pend st.tag (stepAt H k a stop hs st pos) +
        ((stepAt H k a stop hs st pos).pos.toNat - pos.toNat) := by
  unfold stepAtW stepAt
  cases ht : st.tag with
  | command => dsimp only; omega
  | insertCopy => dsimp only; omega
  | copyLength => dsimp only; omega
  | literals =>
    have := literalsW_le (H := H) (a := a) (hs := hs) (st := st) (pos := pos) hk
    dsimp only
    split at this <;> omega
  | distance =>
    have := distanceW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    unfold wcost
    rw [ite_eq_left this.2]
    omega
  | distanceSymbol =>
    have := distanceSymbolW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    unfold wcost
    rw [ite_eq_left this.2]
    omega
  | copy => have := copyW_le (st := st) (pos := pos) hk; dsimp only; omega
  | word => have := wordW_le (st := st) (pos := pos) hk; dsimp only; omega

/-- A command loop step's work: the refill's, then the step's. -/
theorem stepCmdW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk st.word st.count).Wf) : stepCmdW H k a stop hs st pos ≤
      4 + 2 * addedW st.pend (stepCmd H k a stop hs st pos) + wcost st.pend st.tag (stepCmd H k a stop hs st pos) +
        ((stepCmd H k a stop hs st pos).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmdW stepCmd
  rw [dite_eq_left hp', dite_eq_left hp']
  dsimp only
  have h1 := refillW_take (word := st.word) (count := st.count) hs hp
  have h1' := (refill_spec hs hp hw).2.1
  have h2 := stepAtW_le (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) hk
  have h3 := stepAt_ge (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) (k := k)
  dsimp only at h2 h3
  exact Nat.le_trans (Nat.add_le_add_left h2 _) (by omega)

/-- What a command loop step's kind adds to its work: for literals two and two for each byte, but nothing for a step that
goes on having added none, and for a copy or a word one for each byte. -/
def kindW (t : Tag) (r : Cmd) (added : Nat) : Nat :=
  match t with
  | .literals => if r.status = .next ∧ added = 0 then 0 else 2 + 2 * added
  | .copy => added
  | .word => added
  | _ => 0

/-- A command loop step's work by its kind, once the buffer is refilled: one, what its kind adds, a dictionary word's
building, and a round for each byte its literals' refills take. -/
theorem stepAtW_kind {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepAtW H k a stop hs st pos ≤
      1 + (wcost st.pend st.tag (stepAt H k a stop hs st pos) - 1) +
        kindW st.tag (stepAt H k a stop hs st pos) (addedW st.pend (stepAt H k a stop hs st pos)) +
        ((stepAt H k a stop hs st pos).pos.toNat - pos.toNat) := by
  unfold stepAtW stepAt
  cases ht : st.tag with
  | command => dsimp only; omega
  | insertCopy => dsimp only; omega
  | copyLength => dsimp only; omega
  | literals =>
    have := literalsW_le (H := H) (a := a) (hs := hs) (st := st) (pos := pos) hk
    dsimp only [kindW]
    split at this
    · rename_i hc
      rw [ite_eq_left hc]
      omega
    · rename_i hc
      rw [ite_eq_right hc]
      omega
  | distance =>
    have := distanceW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    unfold wcost kindW
    rw [ite_eq_left this.2]
    omega
  | distanceSymbol =>
    have := distanceSymbolW_le (H := H) (pos := pos) ht
    rw [ht] at this
    dsimp only
    unfold wcost kindW
    rw [ite_eq_left this.2]
    omega
  | copy => have := copyW_le (st := st) (pos := pos) hk; dsimp only [kindW]; omega
  | word => have := wordW_le (st := st) (pos := pos) hk; dsimp only [kindW]; omega

/-- A command loop step's work by its kind: the refill's, then the step's. -/
theorem stepCmdW_kind {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk st.word st.count).Wf) : stepCmdW H k a stop hs st pos ≤
      2 + (wcost st.pend st.tag (stepCmd H k a stop hs st pos) - 1) +
        kindW st.tag (stepCmd H k a stop hs st pos) (addedW st.pend (stepCmd H k a stop hs st pos)) +
        ((stepCmd H k a stop hs st pos).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmdW stepCmd
  rw [dite_eq_left hp', dite_eq_left hp']
  dsimp only
  have h1 := refillW_take (word := st.word) (count := st.count) hs hp
  have h1' := (refill_spec hs hp hw).2.1
  have h2 := stepAtW_kind (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) hk
  have h3 := stepAt_ge (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) (k := k)
  dsimp only at h2 h3
  exact Nat.le_trans (Nat.add_le_add_left h2 _) (by omega)

/-- A step, once the buffer is refilled, that is neither literals, a copy nor a word adds no byte. -/
theorem stepAt_pend_other {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd}
    {pos : USize} (h1 : st.tag ≠ .literals) (h2 : st.tag ≠ .copy) (h3 : st.tag ≠ .word) :
    (stepAt H k a stop hs st pos).pend = st.pend := by
  unfold stepAt
  cases ht : st.tag with
  | command => exact stepCommand_pend _ _ _
  | insertCopy =>
    dsimp only
    unfold stepInsertCopy insertStep markStep
    try dsimp only
    repeat' (first | split_all | rfl)
  | copyLength =>
    dsimp only
    unfold stepCopyLength markStep
    try dsimp only
    repeat' (first | split_all | rfl)
  | distance => exact (distanceW_le (H := H) (pos := pos) ht).2
  | distanceSymbol => exact (distanceSymbolW_le (H := H) (pos := pos) ht).2
  | literals => exact absurd ht h1
  | copy => exact absurd ht h2
  | word => exact absurd ht h3

/-- A step that is neither literals, a copy nor a word adds no byte. -/
theorem stepCmd_pend_other {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd}
    {pos : USize} (h1 : st.tag ≠ .literals) (h2 : st.tag ≠ .copy) (h3 : st.tag ≠ .word) :
    (stepCmd H k a stop hs st pos).pend = st.pend := by
  unfold stepCmd
  split
  · exact stepAt_pend_other h1 h2 h3
  · rfl

/-! ### Pausing for output

The command loop pauses for output only when its room is used up. -/

/-- A command loop step, once the buffer is refilled, pauses for output only with no room left. -/
theorem stepAt_full {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} :
    (stepAt H k a stop hs st pos).status = .needsOutput →
      room k (stepAt H k a stop hs st pos).cap ≤ (stepAt H k a stop hs st pos).pend := by
  unfold stepAt
  cases ht : st.tag <;> dsimp only
  · unfold stepCommand markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepInsertCopy insertStep markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepCopyLength markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepLiterals literalsRun finishLiterals markStep clearRing
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)) | (intro _; assumption))
  · unfold stepDistance applyDistance applyWord applyBuilt markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepDistanceSymbol
    by_cases hd : st.dCur < H.nD
    · rw [dite_eq_left hd]
      unfold distanceThrough distanceStep applyDistance applyWord applyBuilt markStep
      try dsimp only
      repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
    · rw [dite_eq_right hd]
      intro h
      exact absurd h (fun e => StepStatus.noConfusion e)
  · unfold stepCopy finishCopy markStep clearRing
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)) | (intro _; assumption))
  · unfold stepWord finishWord markStep clearRing
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)) | (intro _; assumption))

/-- A command loop step pauses for output only with no room left. -/
theorem stepCmd_full {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (h : (stepCmd H k a stop hs st pos).status = .needsOutput) :
    room k (stepCmd H k a stop hs st pos).cap ≤ (stepCmd H k a stop hs st pos).pend := by
  unfold stepCmd at h ⊢
  by_cases hp : pos ≤ stop
  · rw [dite_eq_left hp] at h ⊢
    exact stepAt_full h
  · rw [dite_eq_right hp] at h
    exact absurd h (fun e => StepStatus.noConfusion e)

/-- The command loop pauses for output only with no room left. -/
theorem runCmd_full {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ (N : Nat) (n : USize) (st : Cmd) (pos : USize), n.toNat = N → (runCmd H k a stop hs n st pos).status = .needsOutput →
      room k (runCmd H k a stop hs n st pos).cap ≤ (runCmd H k a stop hs n st pos).pend := by
  intro N
  induction N with
  | zero =>
    intro n st pos hN h
    have hz : n = 0 := usize_zero hN
    rw [runCmd, dite_eq_left hz] at h
    exact absurd h (fun e => StepStatus.noConfusion e)
  | succ N ih =>
    intro n st pos hN h
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have e : runCmd H k a stop hs n st pos = match (stepCmd H k a stop hs st pos).status with
        | .next => runCmd H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos
        | _ => stepCmd H k a stop hs st pos := by
      rw [runCmd, dite_eq_right hn]
      rfl
    rw [e] at h ⊢
    cases hst : (stepCmd H k a stop hs st pos).status
    case next =>
      rw [hst] at h
      exact ih _ _ _ (by omega) h
    case needsOutput => exact stepCmd_full hst
    all_goals
      rw [hst] at h
      have h' : (stepCmd H k a stop hs st pos).status = .needsOutput := h
      rw [hst] at h'
      exact absurd h' (fun e => StepStatus.noConfusion e)

/-! ### The potential on the commands' places

A step of the commands read in order reads bits, produces bytes, or goes lower in `crank`, which ranks the places in the
order the command loop's steps take them: a command, its insert and copy lengths, its literals, its distance and its
distance's symbol, its copy, and a copy's or word's end. A command loop step, with its round, costs 22, ten for each byte
and a word's building: the potential holds 22 for each rank and 95 for a word not yet built, so a step that reads and
produces nothing pays from the potential, and any other step pays at most 366 for each bit it reads and 281 for each byte
it adds. The most a byte pays for is the next command's steps, after a copy or word of one byte. -/

/-- The places' ranks are 2, for the commands' end, and from 13 on. -/
theorem cstage_vals (p : Phase) : cstage p = 2 ∨ 13 ≤ cstage p := by
  cases p with
  | command s => by_cases h0 : s.remaining = 0 <;> simp [cstage, h0]
  | copy s d n => cases n <;> simp [cstage]
  | word s pending => cases pending <;> simp [cstage]
  | _ => simp [cstage]

/-- A step from a literal's symbol reads or produces: it is the one place of rank 16. -/
theorem moved_of_16 {w : Nat} {m : MetaBlockHeader} {p q : Phase} {bs c : List Bool} (h16 : cstage p = 16)
    (h : cStep w m p bs = .next q c) : Moved bs c p.out q.out := by
  cases p with
  | literalSymbol s ic c0 ilen clen n lit out =>
    obtain ⟨_, _, h2⟩ := lookIn_next' h
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨_, _, h4⟩ := lookIn_next' h3
    obtain ⟨byte, b, _, e2⟩ := readIn_next' h4
    cases e2
    exact Or.inr (by simp [Phase.out])
  | command s => by_cases h0 : s.remaining = 0 <;> simp [cstage, h0] at h16
  | copy s d n => cases n <;> simp [cstage] at h16
  | word s pending => cases pending <;> simp [cstage] at h16
  | _ => simp [cstage] at h16

/-- A command's places ranked in the order the command loop's steps take them, a literal's symbol with the distance. -/
def crank (p : Phase) : Nat := if cstage p ≤ 2 then 0 else if cstage p ≤ 15 then cstage p - 12 else cstage p - 13

theorem crank_le (p : Phase) : crank p ≤ 8 := by
  have := cstage_le p
  unfold crank
  repeat' split
  all_goals omega

theorem crank_pos {p : Phase} (h : 13 ≤ cstage p) : 1 ≤ crank p := by
  unfold crank
  repeat' split
  all_goals omega

/-- A step of the commands read in order reads bits, produces bytes, or goes lower in `crank`. -/
theorem cStep_rank {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) {p q : Phase} {bs c : List Bool} (hi : CInv w p)
    (h : cStep w m p bs = .next q c) : CInv w q ∧ (∃ l, q.out = l ++ p.out) ∧ (Moved bs c p.out q.out ∨ crank q < crank p) := by
  obtain ⟨h1, h2, h3⟩ := cStep_moves hm p bs q c hi h
  refine ⟨h1, h2, ?_⟩
  rcases h3 with h3 | h3
  · exact Or.inl h3
  · by_cases h16 : cstage p = 16
    · exact Or.inl (moved_of_16 h16 h)
    · right
      have := cstage_le p
      have := cstage_vals p
      have := cstage_vals q
      unfold crank
      repeat' split
      all_goals omega

/-- What a copy or a dictionary word with bytes left holds for the next command's steps, less 26 for each byte left: the
next command's steps from a copy's end are paid for by the copy's bytes, at least two, or a word's, at least four when
no bit was read. -/
def cred : Phase → Nat
  | .copy _ _ n => if n = 0 then 0 else 103 - 26 * n
  | .word _ pending => if pending = [] then 0 else 103 - 26 * pending.length
  -- the other places are listed rather than matched by `_`, whose equation lemma took 4 s to generate
  | .command .. | .insertCopy .. | .copyLength .. | .literals .. | .literalSymbol .. | .distance .. | .distanceSymbol .. =>
    0

/-- The potential of a command's place: three for each rank, a dictionary word's building where one may begin, and what
a copy or a word holds. -/
def cpot (p : Phase) : Nat := 3 * crank p + (if 2 ≤ crank p then 79 else 0) + cred p

/-- Whether a place is a dictionary word's. -/
def isWordP : Phase → Bool
  | .word .. => true
  -- listed rather than matched by `_`, as in `cred`
  | .command .. | .insertCopy .. | .copyLength .. | .literals .. | .literalSymbol .. | .distance .. | .distanceSymbol ..
  | .copy .. => false

/-- A step of the commands read in order goes on only from a rank of 13 or more. -/
theorem cstage_next {w : Nat} {m : MetaBlockHeader} {p : Phase} {bs : List Bool} {q : Phase} {c : List Bool}
    (h : cStep w m p bs = .next q c) : 13 ≤ cstage p := by
  cases p with
  | command s =>
    by_cases h0 : s.remaining = 0
    · have h' : (if s.remaining = 0 then ORes.exit s bs else nextIn m.insertCopy s.insertCopy bs fun ic b =>
          .next (Phase.insertCopy s ic) b) = .next q c := h
      rw [ite_eq_left h0] at h'
      cases h'
    · simp only [cstage, h0, ↓reduceIte]
      omega
  | copy s d n => cases n <;> simp only [cstage] <;> omega
  | word s pending => cases pending <;> simp only [cstage] <;> omega
  | _ => simp only [cstage]; omega

/-- A run of the commands read in order: it keeps what its places have, reads and produces at least nothing, and goes down
a rank for each step, less nine for each bit it reads and each byte it produces. -/
theorem creach {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ {n : Nat} {p : Phase} {bs : List Bool} {q : Phase}
    {c : List Bool}, ReachN (cStep w m) n p bs q c → CInv w p → CInv w q ∧ c.length ≤ bs.length ∧ p.out.length ≤ q.out.length ∧
      crank q + n ≤ crank p + 9 * ((bs.length - c.length) + (q.out.length - p.out.length)) ∧ (1 ≤ n → 1 ≤ crank p) := by
  intro n p bs q c h
  induction h with
  | refl => intro hi; exact ⟨hi, Nat.le_refl _, Nat.le_refl _, by omega, fun h => absurd h (by omega)⟩
  | @next n p bs p' bs' q c hs _ ih =>
    intro hi
    obtain ⟨hi', ⟨l, hl⟩, hmv⟩ := cStep_rank hm hi hs
    have hs' : sStep (.cmds w false m p) bs = .next (.cmds w false m p') bs' := by simp only [sStep, hs]
    obtain ⟨u, hu, _⟩ := nfaith_sStep _ bs _ bs' hs'
    have hb : bs'.length + u.length = bs.length := by rw [hu, List.length_append]; omega
    have ho : p'.out.length = l.length + p.out.length := by rw [hl, List.length_append]
    obtain ⟨hq, h1, h2, h3, -⟩ := ih hi'
    have hr8 := crank_le p'
    refine ⟨hq, by omega, by omega, ?_, fun _ => crank_pos (cstage_next hs)⟩
    unfold Moved at hmv
    rcases hmv with (hm1 | hm1) | hm1 <;> omega

/-- Reaching in no steps stays put. -/
theorem reachN_zero {P E : Type} {step : P → List Bool → ORes P E} {p q : P} {a b : List Bool} (h : ReachN step 0 p a q b) :
    q = p ∧ b = a := by
  cases h
  exact ⟨rfl, rfl⟩

/-! ### Copies and dictionary words reached without reading

A copy is at least two bytes. A dictionary word reached without reading a bit has a special distance, at most three past
the four last distances, or a direct one, at most 120, so its word offset is below 120, which selects one of the first
four transforms: it has at least four bytes. -/

/-- The transforms a word offset below 120 selects keep at least 4 bytes. -/
private theorem tid_small : ∀ l, l < 25 → 4 ≤ l → ∀ x, x < 120 →
    x >>> NDBITS.getD l 0 ≤ 2 ∨ (x >>> NDBITS.getD l 0 = 3 ∧ 23 ≤ l) := by decide

/-- A dictionary word at most 120 past the largest backward distance has at least four bytes. -/
theorem dictionaryWord_four {l d maxd : Nat} {word : List Nat} (h : dictionaryWord l d maxd = some word)
    (hd : d ≤ maxd + 120) : 4 ≤ word.length := by
  unfold dictionaryWord at h
  split at h
  · simp at h
  · rename_i hlen
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    have key := tid_small l (by omega) (by omega) (d - (maxd + 1)) (by omega)
    generalize (d - (maxd + 1)) >>> NDBITS.getD l 0 = i at key ht
    have hw : ((List.range l).map fun k => DICT (wordOffset l ((d - (maxd + 1)) % NWORDS l) + k)).length = l := by simp
    generalize ((List.range l).map fun k => DICT (wordOffset l ((d - (maxd + 1)) % NWORDS l) + k)) = w0 at hw ⊢
    have e0 : transforms[0]? = some ⟨"", .identity, ""⟩ := rfl
    have e1 : transforms[1]? = some ⟨"", .identity, " "⟩ := rfl
    have e2 : transforms[2]? = some ⟨" ", .identity, " "⟩ := rfl
    have e3 : transforms[3]? = some ⟨"", .omitFirst 1, ""⟩ := rfl
    have hid : ∀ p s : String, 4 ≤ (applyTransform ⟨p, .identity, s⟩ w0).length := by
      intro p s
      simp only [applyTransform, applyElementary, List.length_append]
      omega
    rcases key with hi | ⟨hi, h23⟩
    · obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      · rw [e0] at ht; cases ht; exact hid _ _
      · rw [e1] at ht; cases ht; exact hid _ _
      · rw [e2] at ht; cases ht; exact hid _ _
    · subst hi
      rw [e3] at ht
      cases ht
      simp only [applyTransform, applyElementary, List.length_append, List.length_drop]
      omega

/-- A distance's place that is a dictionary word is the word of that distance. -/
theorem copyPhase_wordOf {w : Nat} {s : CommandState} {clen dcode d : Nat} {s' : CommandState} {pending : List Nat}
    (h : copyPhase w s clen dcode d = some (.word s' pending)) :
    dictionaryWord clen d (maxBackwardDistance w s.produced) = some pending := by
  unfold copyPhase at h
  dsimp only at h
  split at h
  · obtain ⟨word, hw, h2⟩ := Option.bind_eq_some_iff.mp h
    split at h2
    · cases h2
    · cases h2
      exact hw
  · split at h
    · cases h
    · cases h

/-- A distance's place that is a copy is the copy of its length. -/
theorem copyPhase_copyLen {w : Nat} {s : CommandState} {clen dcode d : Nat} {s' : CommandState} {d' n : Nat}
    (h : copyPhase w s clen dcode d = some (.copy s' d' n)) : n = clen := by
  unfold copyPhase at h
  dsimp only at h
  split at h
  · obtain ⟨word, _, h2⟩ := Option.bind_eq_some_iff.mp h
    split at h2
    · cases h2
    · cases h2
  · split at h
    · cases h
    · cases h
      rfl

/-- A dictionary word reached in a step that reads and produces nothing has at least four bytes. -/
theorem word_four {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) {p : Phase} {bs c : List Bool} {s : CommandState}
    {pending : List Nat} (hi : CInv w p) (h : cStep w m p bs = .next (.word s pending) c) (hb : bs.length ≤ c.length)
    (ho : (Phase.word s pending).out.length ≤ p.out.length) : 4 ≤ pending.length := by
  cases p with
  | distance s0 c0 clen =>
    obtain ⟨hd, _⟩ := hi
    have h' : (if s0.remaining = 0 then ORes.next (Phase.command s0) bs
        else if implicitZeroDistance c0 then
          lookIn (distanceOf m.npostfix m.ndirect s0.distances 0 0) fun d =>
          lookIn (copyPhase w s0 clen 0 d) fun q => .next q bs
        else nextIn m.distance s0.distance bs fun dist b => .next (.distanceSymbol s0 clen dist) b) =
        .next (.word s pending) c := h
    split at h'
    · cases h'
    · split at h'
      · obtain ⟨d, e1, e2⟩ := lookIn_next' h'
        obtain ⟨q, e3, e4⟩ := lookIn_next' e2
        cases e4
        have hw := copyPhase_wordOf e3
        unfold distanceOf at e1
        simp only [show (0 : Nat) < 16 from by decide, dite_true] at e1
        split at e1
        · cases e1
        · cases e1
          have := special_le s0.distances ⟨0, by decide⟩
          obtain ⟨d1, d2, d3, d4⟩ := hd
          refine dictionaryWord_four hw ?_
          omega
      · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
        cases e
  | distanceSymbol s0 clen dist =>
    obtain ⟨hd, _⟩ := hi
    obtain ⟨index, _, h1⟩ := lookIn_next' h
    obtain ⟨code, _, h2⟩ := lookIn_next' h1
    obtain ⟨v, b, e1, h3⟩ := readIn_next' h2
    obtain ⟨d, e2, h4⟩ := lookIn_next' h3
    obtain ⟨q, e3, e4⟩ := lookIn_next' h4
    cases e4
    have hw := copyPhase_wordOf e3
    unfold readDistanceParts at e1
    obtain ⟨⟨dcode, b1⟩, e5, e6⟩ := Option.bind_eq_some_iff.mp e1
    obtain ⟨⟨dx, b2⟩, e7, e8⟩ := Option.bind_eq_some_iff.mp e6
    cases e8
    have l1 := Brotli.Spec.decodeSymbol_le e5
    have l2 := readInt_length _ _ _ _ e7
    have hx : distanceExtraBits m.npostfix m.ndirect dcode = 0 := by omega
    have hlt : dcode < 16 + m.ndirect := by
      unfold distanceExtraBits at hx
      split at hx
      · assumption
      · exact absurd hx (by simp)
    obtain ⟨d1, d2, d3, d4⟩ := hd
    refine dictionaryWord_four hw ?_
    unfold distanceOf at e2
    dsimp only at e2
    split at e2
    · rename_i h16
      split at e2
      · cases e2
      · cases e2
        have := special_le s0.distances ⟨dcode, h16⟩
        dsimp only
        omega
    · cases e2
      dsimp only
      omega
  | command s0 =>
    have h' : (if s0.remaining = 0 then ORes.exit s0 bs
        else nextIn m.insertCopy s0.insertCopy bs fun ic b => .next (Phase.insertCopy s0 ic) b) = .next (.word s pending) c := h
    split at h'
    · cases h'
    · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
      cases e
  | insertCopy s0 ic =>
    obtain ⟨_, _, h1⟩ := lookIn_next' h
    obtain ⟨_, _, _, e⟩ := readIn_next' h1
    cases e
  | copyLength s0 ic c0 ilen cb cbase =>
    have h' : (if s0.remaining < ilen then ORes.bad
        else readIn 24 (readInt cb) bs fun e b => .next (Phase.literals s0 ic c0 ilen (cbase + e) ilen s0.literal s0.output) b) =
        .next (Phase.word s pending) c := h
    split at h'
    · cases h'
    · obtain ⟨_, _, _, e⟩ := readIn_next' h'
      cases e
  | literals s0 ic c0 ilen clen n lit out =>
    cases n with
    | zero => cases h
    | succ n =>
      have h' : (if lit.count = 0 then
          nextIn m.literal lit bs fun lit b => .next (Phase.literals s0 ic c0 ilen clen (n + 1) { lit with count := lit.count + 1 } out) b
          else .next (Phase.literalSymbol s0 ic c0 ilen clen n { lit with count := lit.count - 1 } out) bs) =
          .next (Phase.word s pending) c := h
      split at h'
      · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
        cases e
      · cases h'
  | literalSymbol s0 ic c0 ilen clen n lit out =>
    obtain ⟨_, _, h1⟩ := lookIn_next' h
    obtain ⟨_, _, h2⟩ := lookIn_next' h1
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨_, _, _, e⟩ := readIn_next' h3
    cases e
  | copy s0 d n =>
    cases n with
    | zero => cases h
    | succ n => cases h
  | word s0 pend =>
    cases pend with
    | nil => cases h
    | cons x r =>
      cases h
      simp [Phase.out] at ho
      omega

/-- A copy reached in a step that produces nothing is a command's, of at least two bytes. -/
theorem copy_two {w : Nat} {m : MetaBlockHeader} {p : Phase} {bs c : List Bool} {s : CommandState} {d n : Nat}
    (hi : CInv w p) (h : cStep w m p bs = .next (.copy s d n) c) (ho : (Phase.copy s d n).out.length ≤ p.out.length) :
    2 ≤ n := by
  cases p with
  | distance s0 c0 clen =>
    obtain ⟨_, h2⟩ := hi
    have h' : (if s0.remaining = 0 then ORes.next (Phase.command s0) bs
        else if implicitZeroDistance c0 then
          lookIn (distanceOf m.npostfix m.ndirect s0.distances 0 0) fun d =>
          lookIn (copyPhase w s0 clen 0 d) fun q => .next q bs
        else nextIn m.distance s0.distance bs fun dist b => .next (.distanceSymbol s0 clen dist) b) =
        .next (.copy s d n) c := h
    split at h'
    · cases h'
    · split at h'
      · obtain ⟨_, _, e2⟩ := lookIn_next' h'
        obtain ⟨q, e3, e4⟩ := lookIn_next' e2
        cases e4
        rw [copyPhase_copyLen e3]
        exact h2
      · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
        cases e
  | distanceSymbol s0 clen dist =>
    obtain ⟨_, h2⟩ := hi
    obtain ⟨_, _, h1⟩ := lookIn_next' h
    obtain ⟨_, _, h2'⟩ := lookIn_next' h1
    obtain ⟨_, _, _, h3⟩ := readIn_next' h2'
    obtain ⟨_, _, h4⟩ := lookIn_next' h3
    obtain ⟨q, e3, e4⟩ := lookIn_next' h4
    cases e4
    rw [copyPhase_copyLen e3]
    exact h2
  | command s0 =>
    have h' : (if s0.remaining = 0 then ORes.exit s0 bs
        else nextIn m.insertCopy s0.insertCopy bs fun ic b => .next (Phase.insertCopy s0 ic) b) = .next (.copy s d n) c := h
    split at h'
    · cases h'
    · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
      cases e
  | insertCopy s0 ic =>
    obtain ⟨_, _, h1⟩ := lookIn_next' h
    obtain ⟨_, _, _, e⟩ := readIn_next' h1
    cases e
  | copyLength s0 ic c0 ilen cb cbase =>
    have h' : (if s0.remaining < ilen then ORes.bad
        else readIn 24 (readInt cb) bs fun e b => .next (Phase.literals s0 ic c0 ilen (cbase + e) ilen s0.literal s0.output) b) =
        .next (Phase.copy s d n) c := h
    split at h'
    · cases h'
    · obtain ⟨_, _, _, e⟩ := readIn_next' h'
      cases e
  | literals s0 ic c0 ilen clen k lit out =>
    cases k with
    | zero => cases h
    | succ k =>
      have h' : (if lit.count = 0 then
          nextIn m.literal lit bs fun lit b => .next (Phase.literals s0 ic c0 ilen clen (k + 1) { lit with count := lit.count + 1 } out) b
          else .next (Phase.literalSymbol s0 ic c0 ilen clen k { lit with count := lit.count - 1 } out) bs) =
          .next (Phase.copy s d n) c := h
      split at h'
      · obtain ⟨_, _, _, e⟩ := nextIn_next' h'
        cases e
      · cases h'
  | literalSymbol s0 ic c0 ilen clen k lit out =>
    obtain ⟨_, _, h1⟩ := lookIn_next' h
    obtain ⟨_, _, h2⟩ := lookIn_next' h1
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨_, _, _, e⟩ := readIn_next' h3
    cases e
  | copy s0 d0 k =>
    cases k with
    | zero => cases h
    | succ k =>
      cases h
      simp [Phase.out] at ho
      omega
  | word s0 pend =>
    cases pend with
    | nil => cases h
    | cons x r => cases h

/-- The bits and bytes of a run of the commands read in order, and its first step's. -/
private theorem reach_first {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) {n : Nat} {p p' q : Phase}
    {bs bs' c : List Bool} (hi : CInv w p) (hs : cStep w m p bs = .next p' bs') (hr : ReachN (cStep w m) n p' bs' q c) :
    CInv w p' ∧ c.length ≤ bs'.length ∧ bs'.length ≤ bs.length ∧ p.out.length ≤ p'.out.length ∧ p'.out.length ≤ q.out.length := by
  obtain ⟨hi', ⟨l, hl⟩, _⟩ := cStep_rank hm hi hs
  obtain ⟨-, c1, c2, -, -⟩ := creach hm hr hi'
  have hs' : sStep (.cmds w false m p) bs = .next (.cmds w false m p') bs' := by simp only [sStep, hs]
  obtain ⟨u, hu, _⟩ := nfaith_sStep _ bs _ bs' hs'
  have hb' : bs'.length + u.length = bs.length := by rw [hu, List.length_append]; omega
  have ho' : p'.out.length = l.length + p.out.length := by rw [hl, List.length_append]
  exact ⟨hi', c1, by omega, by omega, c2⟩

/-- A run that reads and produces nothing, ending at a dictionary word, ends at one of at least four bytes. -/
theorem reach_word_four {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ {n : Nat} {p : Phase} {bs : List Bool}
    {q : Phase} {c : List Bool}, ReachN (cStep w m) n p bs q c → CInv w p → 1 ≤ n → bs.length ≤ c.length →
      q.out.length ≤ p.out.length → ∀ s pending, q = .word s pending → 4 ≤ pending.length := by
  intro n p bs q c h
  induction h with
  | refl => intro _ h1; omega
  | @next n p bs p' bs' q c hs hr ih =>
    intro hi _ hb ho s pending hq
    obtain ⟨hi', c1, c2, c3, c4⟩ := reach_first hm hi hs hr
    cases n with
    | zero =>
      cases hr
      subst hq
      exact word_four hm hi hs (by omega) (by omega)
    | succ n => exact ih hi' (by omega) (by omega) (by omega) s pending hq

/-- A run that reads and produces nothing, ending at a copy, ends at a command's copy, of at least two bytes. -/
theorem reach_copy_two {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ {n : Nat} {p : Phase} {bs : List Bool}
    {q : Phase} {c : List Bool}, ReachN (cStep w m) n p bs q c → CInv w p → 1 ≤ n → bs.length ≤ c.length →
      q.out.length ≤ p.out.length → ∀ s d k, q = .copy s d k → 2 ≤ k := by
  intro n p bs q c h
  induction h with
  | refl => intro _ h1; omega
  | @next n p bs p' bs' q c hs hr ih =>
    intro hi _ hb ho s d k hq
    obtain ⟨hi', c1, c2, c3, c4⟩ := reach_first hm hi hs hr
    cases n with
    | zero =>
      cases hr
      subst hq
      exact copy_two hi hs (by omega)
    | succ n => exact ih hi' (by omega) (by omega) (by omega) s d k hq

/-- A run from a copy that produces fewer bytes than the copy has left stays in the copy. -/
theorem reach_copy_left {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ {N : Nat} {p : Phase} {bs : List Bool}
    {q : Phase} {c : List Bool}, ReachN (cStep w m) N p bs q c → CInv w p → ∀ s d n, p = .copy s d n →
      q.out.length < p.out.length + n → ∃ s', q = .copy s' d (n - (q.out.length - p.out.length)) := by
  intro N p bs q c h
  induction h with
  | refl => intro _ s d n hp _; exact ⟨s, by rw [hp, Nat.sub_self, Nat.sub_zero]⟩
  | @next N p bs p' bs' q c hs hr ih =>
    intro hi s d n hp hlt
    obtain ⟨hi', c1, c2, c3, c4⟩ := reach_first hm hi hs hr
    subst hp
    cases n with
    | zero => omega
    | succ n =>
      cases hs
      have hl : (Phase.copy { s with output := s.output.getD (d - 1) 0 :: s.output } d n).out.length =
          (Phase.copy s d (n + 1)).out.length + 1 := by simp [Phase.out]
      obtain ⟨s', e⟩ := ih hi' _ d n rfl (by omega)
      have hk : n - (q.out.length - (Phase.copy { s with output := s.output.getD (d - 1) 0 :: s.output } d n).out.length) =
          n + 1 - (q.out.length - (Phase.copy s d (n + 1)).out.length) := by omega
      exact ⟨s', by rw [← hk]; exact e⟩

/-- A run from a dictionary word that produces fewer bytes than the word has left stays in the word. -/
theorem reach_word_left {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ {N : Nat} {p : Phase} {bs : List Bool}
    {q : Phase} {c : List Bool}, ReachN (cStep w m) N p bs q c → CInv w p → ∀ s pending, p = .word s pending →
      q.out.length < p.out.length + pending.length →
      ∃ s' rest, q = .word s' rest ∧ rest.length = pending.length - (q.out.length - p.out.length) := by
  intro N p bs q c h
  induction h with
  | refl => intro _ s pending hp _; exact ⟨s, pending, hp, by omega⟩
  | @next N p bs p' bs' q c hs hr ih =>
    intro hi s pending hp hlt
    obtain ⟨hi', c1, c2, c3, c4⟩ := reach_first hm hi hs hr
    subst hp
    cases pending with
    | nil => simp at hlt; omega
    | cons x rest =>
      cases hs
      have hl : (Phase.word { s with output := x :: s.output } rest).out.length = (Phase.word s (x :: rest)).out.length + 1 := by
        simp [Phase.out]
      obtain ⟨s', r', e, hr'⟩ := ih hi' _ rest rfl (by simp at hlt; omega)
      refine ⟨s', r', e, ?_⟩
      simp only [List.length_cons]
      omega

theorem Rel.k24 {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) : k ≤ 24 := by
  cases p
  case literalSymbol => exact h.elim
  all_goals exact h.1.k24

/-- A state at a word's bytes stands for a word's place. -/
theorem Rel.word_of {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (ht : st.tag = .word) :
    ∃ s pending, p = .word s pending := by
  cases p
  case word s pending => exact ⟨s, pending, rfl⟩
  case literalSymbol => exact h.elim
  all_goals exact absurd (h.2.1.symm.trans ht) (fun e => Tag.noConfusion e)

/-- A state at a copy stands for a copy's place. -/
theorem Rel.copy_of {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (ht : st.tag = .copy) :
    ∃ s d n, p = .copy s d n := by
  cases p
  case copy s d n => exact ⟨s, d, n, rfl⟩
  case literalSymbol => exact h.elim
  all_goals exact absurd (h.2.1.symm.trans ht) (fun e => Tag.noConfusion e)

/-- A state at literals stands for a place of literals. -/
theorem Rel.lit_of {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (ht : st.tag = .literals) :
    crank p = 4 ∧ cred p = 0 := by
  cases p
  case literals => exact ⟨rfl, rfl⟩
  case literalSymbol => exact h.elim
  all_goals exact absurd (h.2.1.symm.trans ht) (fun e => Tag.noConfusion e)

/-- A state at a word's place is at a word. -/
theorem Rel.word_tag {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (ht : st.tag = .word) :
    isWordP p = true := by
  obtain ⟨s, pending, rfl⟩ := h.word_of ht
  rfl

/-- Only a copy or a word with bytes left holds anything for the next command, and they have rank 1. -/
theorem cred_crank {p : Phase} (h : cred p ≠ 0) : crank p = 1 := by
  cases p with
  | copy s d n =>
    cases n with
    | zero => exact absurd rfl h
    | succ n => rfl
  | word s pending =>
    cases pending with
    | nil => exact absurd rfl h
    | cons => rfl
  | _ => exact absurd rfl h

/-- The places of rank 1 are a copy's and a word's with bytes left. -/
theorem crank_one {p : Phase} (h : crank p = 1) : (∃ s d k, p = .copy s d (k + 1)) ∨ (∃ s x r, p = .word s (x :: r)) := by
  cases p with
  | copy s d n =>
    cases n with
    | zero => simp [crank, cstage] at h
    | succ k => exact Or.inl ⟨s, d, k, rfl⟩
  | word s pending =>
    cases pending with
    | nil => simp [crank, cstage] at h
    | cons x r => exact Or.inr ⟨s, x, r, rfl⟩
  | command s =>
    unfold crank cstage at h
    by_cases h0 : s.remaining = 0 <;> simp [h0] at h
  | _ => simp [crank, cstage] at h

/-- A word's place has rank 1 or 8. -/
theorem word_crank {p : Phase} (h : isWordP p = true) : crank p = 1 ∨ crank p = 8 := by
  cases p with
  | word s pending => cases pending <;> simp [crank, cstage]
  | _ => cases h

/-- A state at a command's start has the potential of a command's place. -/
theorem cpot_command {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (ht : st.tag = .command) :
    cpot p ≤ 100 := by
  cases p with
  | command s => by_cases h0 : s.remaining = 0 <;> simp [cpot, crank, cstage, cred, h0]
  | _ => first | exact False.elim h | exact absurd (ht.symm.trans h.2.1) (fun e => by cases e)

theorem cpot_le (p : Phase) : cpot p ≤ 103 := by
  have := crank_le p
  by_cases hc : cred p = 0
  · unfold cpot
    rw [hc]
    split <;> omega
  · have h1 := cred_crank hc
    unfold cpot
    rw [h1]
    cases p with
    | copy s d n =>
      simp only [cred] at hc ⊢
      repeat' split
      all_goals omega
    | word s pending =>
      simp only [cred] at hc ⊢
      by_cases hp0 : pending = []
      · simp [hp0] at hc
      · have : 0 < pending.length := by cases pending with | nil => exact absurd rfl hp0 | cons => simp
        rw [ite_eq_right hp0]
        simp only [Nat.reduceLeDiff, ↓reduceIte]
        omega
    | _ => simp [cred] at hc

/-- A run of the commands read in order that reads and produces nothing goes down in potential by three, and by a word's
building when it ends at a word. -/
theorem cpot_down {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) {n : Nat} {p q : Phase} {bs c : List Bool}
    (hr : ReachN (cStep w m) n p bs q c) (hci : CInv w p) (hn : 1 ≤ n) (hb : bs.length ≤ c.length)
    (ho : q.out.length ≤ p.out.length) : cpot q + 3 + (if isWordP q then 79 else 0) ≤ cpot p := by
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hp1 := c4 hn
  have hlt : crank q + n ≤ crank p := by omega
  have hp8 := crank_le p
  have hpot : 3 * crank p + (if 2 ≤ crank p then 79 else 0) ≤ cpot p := by unfold cpot; omega
  by_cases hq1 : crank q = 1
  · have hp2 : 2 ≤ crank p := by omega
    have h85 : 85 ≤ cpot p := by rw [ite_eq_left hp2] at hpot; omega
    rcases crank_one hq1 with ⟨s, d, k, rfl⟩ | ⟨s, x, r, rfl⟩
    · have h2 := reach_copy_two hm hr hci hn hb ho s d (k + 1) rfl
      have e : cpot (.copy s d (k + 1)) = 3 + (103 - 26 * (k + 1)) := by simp [cpot, cred, crank, cstage]
      rw [e]
      simp only [isWordP, Bool.false_eq_true, ↓reduceIte]
      omega
    · have h4 := reach_word_four hm hr hci hn hb ho s (x :: r) rfl
      have e : cpot (.word s (x :: r)) = 3 + (103 - 26 * (x :: r).length) := by simp [cpot, cred, crank, cstage]
      rw [e]
      simp only [isWordP, ↓reduceIte]
      simp only [List.length_cons] at h4 ⊢
      omega
  · have hc0 : cred q = 0 := Classical.byContradiction fun h => hq1 (cred_crank h)
    have hw : isWordP q = false := by
      cases e : isWordP q
      · rfl
      · rcases word_crank e with h | h <;> omega
    rw [hw]
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold cpot
    rw [hc0]
    repeat' split
    all_goals omega

/-- What a command loop round pays, any way it ends but a rejection: its work, and the potential where it ends, are paid
for by the potential, 200 for each bit it reads, 30 for each byte it adds, a round for each byte its refills take, and 84
for a round that stops. -/
theorem round_pay {w : Nat} {m : MetaBlockHeader} {H : Hdr} {k : USize} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} {p q : Phase} {c0 L : Nat} {bs c : List Bool} (hm : m.ndirect ≤ 120)
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) (hrel : Rel w k.toNat m st p)
    (hrq : Rel w k.toNat m (stepCmd H k a stop hs st pos) q) (hnb : (stepCmd H k a stop hs st pos).status ≠ .bad)
    (hq1 : pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat) (hq2 : (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat)
    (hL : (stepCmd H k a stop hs st pos).pend.toNat = st.pend.toNat + L) (hci : CInv w p)
    (hr : ReachN (cStep w m) c0 p bs q c) (hlo : q.out.length = L + p.out.length)
    (hc0 : (stepCmd H k a stop hs st pos).status = .next → 1 ≤ c0) :
    stepCmdW H k a stop hs st pos + 1 + cpot q + 200 * c.length + (stop.toNat - (stepCmd H k a stop hs st pos).pos.toNat) ≤
      cpot p + 200 * bs.length + (stop.toNat - pos.toNat) + 30 * L +
        (if (stepCmd H k a stop hs st pos).status = .next then 0 else 84) := by
  have hW := stepCmdW_kind (H := H) (a := a) (hs := hs) (st := st) hk hp hrel.wf
  have hA : addedW st.pend (stepCmd H k a stop hs st pos) = L := by
    unfold addedW
    rw [ite_eq_right hnb, hL]
    omega
  rw [hA] at hW
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hcq := cpot_le q
  have hwc : wcost st.pend st.tag (stepCmd H k a stop hs st pos) ≤ 80 := by
    unfold wcost wordCost
    repeat' split
    all_goals omega
  have hkw : kindW st.tag (stepCmd H k a stop hs st pos) L ≤ 2 + 2 * L := by
    unfold kindW
    repeat' split
    all_goals omega
  generalize hRp : (stepCmd H k a stop hs st pos).pos.toNat = rp at hq1 hq2 hW ⊢
  by_cases hbits : c.length < bs.length
  · split <;> omega
  have hbb : bs.length ≤ c.length := by omega
  by_cases hL0 : L = 0
  · subst hL0
    have hpe : (stepCmd H k a stop hs st pos).pend = st.pend := USize.toNat_inj.mp (by rw [hL]; rfl)
    have hkw0 : kindW st.tag (stepCmd H k a stop hs st pos) 0 ≤ (if (stepCmd H k a stop hs st pos).status = .next then 0 else 2) := by
      unfold kindW
      repeat' split
      all_goals simp_all
    cases c0 with
    | zero =>
      have hn0 : (stepCmd H k a stop hs st pos).status ≠ .next := fun e => by have := hc0 e; omega
      obtain ⟨e1, e2⟩ := reachN_zero hr
      subst e1
      rw [ite_eq_right hn0] at hkw0 ⊢
      omega
    | succ c0 =>
      have hd := cpot_down hm hr hci (by omega) hbb (by omega)
      by_cases hnx : (stepCmd H k a stop hs st pos).status = .next
      · rw [ite_eq_left hnx] at hkw0 ⊢
        have hwq : wcost st.pend st.tag (stepCmd H k a stop hs st pos) - 1 ≤ if isWordP q then 79 else 0 := by
          unfold wcost wordCost
          rw [ite_eq_left hpe]
          by_cases hwd : (stepCmd H k a stop hs st pos).tag = .word ∧ st.tag ≠ .word
          · rw [hrq.word_tag hwd.1]
            split <;> simp
          · rw [ite_eq_left ⟨hnx, hwd⟩]
            simp
        by_cases hiw : isWordP q = true
        · rw [ite_eq_left hiw] at hd hwq
          omega
        · rw [ite_eq_right hiw] at hd hwq
          omega
      · rw [ite_eq_right hnx] at hkw0 ⊢
        split at hd <;> omega
  · have hpne : (stepCmd H k a stop hs st pos).pend ≠ st.pend := fun e => by
      rw [e] at hL
      omega
    have hw0 : wcost st.pend st.tag (stepCmd H k a stop hs st pos) = 0 := by
      unfold wcost
      rw [ite_eq_right hpne]
    rw [hw0] at hW
    have hext : 0 ≤ (if (stepCmd H k a stop hs st pos).status = .next then 0 else 84) := Nat.zero_le _
    by_cases hlit : st.tag = .literals
    · obtain ⟨hr4, hc4⟩ := hrel.lit_of hlit
      have e : cpot p = 91 := by unfold cpot; rw [hr4, hc4]; rfl
      omega
    by_cases hcp : st.tag = .copy
    · obtain ⟨s, d, n, rfl⟩ := hrel.copy_of hcp
      have hkc : kindW st.tag (stepCmd H k a stop hs st pos) L = L := by rw [hcp]; rfl
      rw [hkc] at hW
      cases n with
      | zero =>
        have e : cpot (.copy s d 0) = 103 := rfl
        omega
      | succ n =>
        have e : cpot (.copy s d (n + 1)) = 3 + (103 - 26 * (n + 1)) := by simp [cpot, cred, crank, cstage]
        by_cases hlt : L < n + 1
        · obtain ⟨s', e'⟩ := reach_copy_left hm hr hci s d (n + 1) rfl (by omega)
          have hsub : n + 1 - (q.out.length - (Phase.copy s d (n + 1)).out.length) = n + 1 - L := by omega
          rw [hsub] at e'
          subst e'
          have eq : cpot (.copy s' d (n + 1 - L)) = 3 + (103 - 26 * (n + 1 - L)) := by
            obtain ⟨j, hj⟩ : ∃ j, n + 1 - L = j + 1 := ⟨n - L, by omega⟩
            rw [hj]
            simp [cpot, cred, crank, cstage]
          omega
        · omega
    by_cases hwd : st.tag = .word
    · obtain ⟨s, pending, rfl⟩ := hrel.word_of hwd
      have hkc : kindW st.tag (stepCmd H k a stop hs st pos) L = L := by rw [hwd]; rfl
      rw [hkc] at hW
      cases pending with
      | nil =>
        have e : cpot (.word s []) = 103 := rfl
        omega
      | cons x r =>
        have e : cpot (.word s (x :: r)) = 3 + (103 - 26 * (r.length + 1)) := by simp [cpot, cred, crank, cstage]
        by_cases hlt : L < r.length + 1
        · obtain ⟨s', r', e', hr'⟩ := reach_word_left hm hr hci s (x :: r) rfl (by simp; omega)
          subst e'
          simp only [List.length_cons] at hr'
          cases r' with
          | nil => simp at hr'; omega
          | cons y r'' =>
            have eq : cpot (.word s' (y :: r'')) = 3 + (103 - 26 * (r''.length + 1)) := by simp [cpot, cred, crank, cstage]
            simp only [List.length_cons] at hr'
            omega
        · omega
    · have := stepCmd_pend_other (H := H) (k := k) (a := a) (hs := hs) (pos := pos) hlit hcp hwd
      exact absurd this hpne

/-- A command loop step that goes on, against the potential: what it does is paid by the potential, 200 for each bit it
reads, 30 for each byte it adds, and a round for each byte its refills take. -/
theorem stepCmd_pot {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hm : m.ndirect ≤ 120) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st p) (hci : CInv w p) (hp : pos.toNat ≤ stop.toNat) (hn : (stepCmd H k a stop hs st pos).status = .next) :
    ∃ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' ∧ OutStep p p' st (stepCmd H k a stop hs st pos) ∧ CInv w p' ∧
      (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧ pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧
      ∀ F, ∃ n, 1 ≤ n ∧ ReachN (cStep w m) n p (stateBits st a pos stop F) p'
        (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F) ∧
        stepCmdW H k a stop hs st pos + 1 + cpot p' + 200 * (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F).length +
          (stop.toNat - (stepCmd H k a stop hs st pos).pos.toNat) ≤
          cpot p + 200 * (stateBits st a pos stop F).length + (stop.toNat - pos.toNat) + 30 * (p'.out.length - p.out.length) := by
  obtain ⟨p', hR, hout, h2, h1, hj⟩ := stepCmd_count (hs := hs) hH hrel hp hn
  obtain ⟨l, hl1, hl2⟩ := hout
  refine ⟨p', hR, ⟨l, hl1, hl2⟩, ?_, h2, h1, fun F => ?_⟩
  · obtain ⟨n, hn1, hr⟩ := hj []
    exact (creach hm hr hci).1
  obtain ⟨n, hn1, hr⟩ := hj F
  refine ⟨n, hn1, hr, ?_⟩
  have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
  have hb : (stepCmd H k a stop hs st pos).status ≠ .bad := by rw [hn]; exact fun e => StepStatus.noConfusion e
  have := round_pay hm hrel.k24 hp hrel hR hb h1 h2 hl2 hci hr hlo (fun _ => hn1)
  rw [ite_eq_left hn] at this
  have hx : p'.out.length - p.out.length = l.length := by omega
  rw [hx]
  omega

/-- A round that stops the command loop where its step ends, without rejecting: its work, and the potential of where it
stops, are paid for by the potential, 200 for each bit it reads, 30 for each byte it adds, a round for each byte its
refills take, and 84. -/
theorem stopRound_pay {w : Nat} {m : MetaBlockHeader} {H : Hdr} {k : USize} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} {p q : Phase} {c0 L : Nat} {bs c : List Bool} (hm : m.ndirect ≤ 120)
    (hp : pos.toNat ≤ stop.toNat) (hrel : Rel w k.toNat m st p) (hrq : Rel w k.toNat m (stepCmd H k a stop hs st pos) q)
    (hnx : (stepCmd H k a stop hs st pos).status ≠ .next) (hnb : (stepCmd H k a stop hs st pos).status ≠ .bad)
    (hq1 : pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat) (hq2 : (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat)
    (hL : (stepCmd H k a stop hs st pos).pend.toNat = st.pend.toNat + L) (hci : CInv w p)
    (hr : ReachN (cStep w m) c0 p bs q c) (hlo : q.out.length = L + p.out.length) :
    stepCmdW H k a stop hs st pos + 1 + cpot q + 200 * c.length + (stop.toNat - (stepCmd H k a stop hs st pos).pos.toNat) ≤
      cpot p + 200 * bs.length + (stop.toNat - pos.toNat) + 30 * L + 84 := by
  have := round_pay hm hrel.k24 hp hrel hrq hnb hq1 hq2 hL hci hr hlo (fun e => absurd e hnx)
  rw [ite_eq_right hnx] at this
  exact this

/-- A round that rejects: its refill's bytes are not counted as taken, so it costs the refill's eight rounds. -/
theorem badRound_pay {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk st.word st.count).Wf)
    (hb : (stepCmd H k a stop hs st pos).status = .bad) :
    stepCmdW H k a stop hs st pos + 1 ≤ 92 := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmd at hb
  rw [dite_eq_left hp'] at hb
  unfold stepCmdW
  rw [dite_eq_left hp']
  dsimp only at hb ⊢
  have h1 := refillW_le (word := st.word) (count := st.count) hs hp
  have hq := (refill_spec hs hp hw).2.2.1
  have hpb := (stepAt_bad (USize.le_iff_toNat_le.mpr hq) hb).2
  have h2 := stepAtW_le (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) hk
  have hc : ∀ r : Cmd, wcost st.pend st.tag r ≤ 80 := by
    intro r
    unfold wcost wordCost
    repeat' split
    all_goals omega
  have ha : ∀ r : Cmd, r.status = .bad → addedW st.pend r = 0 := by
    intro r e
    unfold addedW
    rw [ite_eq_left e]
  rw [hpb, ha _ hb] at h2
  dsimp only at h2
  have := hc (stepAt H k a stop hs
    { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos)
  omega

/-- The end of the command loop's work: one when its budget runs out, 92 for a round that rejects, and 84 for one that
stops otherwise. -/
def cmdEnd (r : Cmd) : Nat := if r.status = .next then 1 else if r.status = .bad then 92 else 84

/-- The command loop's work, against the potential: what it does is paid for by the potential, 200 for each bit it
reads, 30 for each byte it adds, a round for each byte its refills take, and its end. -/
theorem runCmdW_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hm : m.ndirect ≤ 120) (hH : HdrRel H m) : ∀ (N : Nat) (n : USize) (st : Cmd) (p : Phase) (pos : USize), n.toNat = N →
      Rel w k.toNat m st p → CInv w p → pos.toNat ≤ stop.toNat → ∀ F, ∃ c q st' pos', Rel w k.toNat m st' q ∧ CInv w q ∧
        OutStep p q st st' ∧ PendLe st st' ∧ pos.toNat ≤ pos'.toNat ∧ pos'.toNat ≤ stop.toNat ∧
        ReachN (cStep w m) c p (stateBits st a pos stop F) q (stateBits st' a pos' stop F) ∧
        runCmdW H k a stop hs n st pos + cpot q + 200 * (stateBits st' a pos' stop F).length + (stop.toNat - pos'.toNat) ≤
          cpot p + 200 * (stateBits st a pos stop F).length + (stop.toNat - pos.toNat) + 30 * (q.out.length - p.out.length) +
            cmdEnd (runCmd H k a stop hs n st pos) ∧
        ((runCmd H k a stop hs n st pos).status ≠ .bad → st' = runCmd H k a stop hs n st pos ∧ pos' = (runCmd H k a stop hs n st pos).pos) ∧
        ((runCmd H k a stop hs n st pos).status = .bad → (runCmd H k a stop hs n st pos).WinSame st' ∧
          pos'.toNat ≤ (runCmd H k a stop hs n st pos).pos.toNat) ∧
        ((runCmd H k a stop hs n st pos).status = .done → ∃ s, q = .command s ∧ s.remaining = 0) ∧
        ((runCmd H k a stop hs n st pos).status = .next → n.toNat ≤ c) := by
  intro N
  induction N with
  | zero =>
    intro n st p pos hN hrel hci hp F
    have hz : n = 0 := usize_zero hN
    have e : runCmd H k a stop hs n st pos = markStep st pos .next := by rw [runCmd, dite_eq_left hz]
    rw [e]
    refine ⟨0, p, markStep st pos .next, pos, hrel.mark _ _, hci, ⟨[], rfl, rfl⟩, PendLe.keep rfl rfl, Nat.le_refl _, hp, .refl _ _, ?_,
      fun _ => ⟨rfl, rfl⟩, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun _ => by omega⟩
    rw [runCmdW, dite_eq_left hz]
    show 1 + cpot p + 200 * (stateBits st a pos stop F).length + (stop.toNat - pos.toNat) ≤ _ + cmdEnd (markStep st pos .next)
    have : cmdEnd (markStep st pos .next) = 1 := rfl
    omega
  | succ N ih =>
    intro n st p pos hN hrel hci hp F
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hk := hrel.k24
    have hok := stepCmd_ok (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) (hs := hs) hH hrel hp
    have hsteps : runCmdW H k a stop hs n st pos = stepCmdW H k a stop hs st pos + 1 + match (stepCmd H k a stop hs st pos).status with
        | .next => runCmdW H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos
        | _ => 0 := by
      rw [runCmdW, dite_eq_right hn]
      -- in a module this `match` is a matcher of its own, not `runCmdW`'s, so `rw`'s closing `rfl` doesn't see it
      rfl
    have hrun : runCmd H k a stop hs n st pos = match (stepCmd H k a stop hs st pos).status with
        | .next => runCmd H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos
        | _ => stepCmd H k a stop hs st pos := by
      rw [runCmd, dite_eq_right hn]
      rfl
    rw [hsteps, hrun]
    cases hst : (stepCmd H k a stop hs st pos).status
    case next =>
      obtain ⟨p1, hR1, o1, hci1, h2, h1, hj1⟩ := stepCmd_pot (hs := hs) hm hH hrel hci hp hst
      obtain ⟨n1, hn1, hr1, hw1⟩ := hj1 F
      obtain ⟨c2, q, st', pos', hq, hciq, o2, l2, g1, g2, hr2, g3, g4, gb, g5, g6⟩ :=
        ih (n - USize.ofNat 1) _ p1 _ (by omega) hR1 hci1 h2 F
      have ho1 : p.out.length ≤ p1.out.length := by
        obtain ⟨l, e1, -⟩ := o1
        rw [e1, List.length_append]
        omega
      have ho2 : p1.out.length ≤ q.out.length := by
        obtain ⟨l, e1, -⟩ := o2
        rw [e1, List.length_append]
        omega
      refine ⟨n1 + c2, q, st', pos', hq, hciq, o1.trans o2, (stepCmd_pendLe H k a stop hs st pos).trans l2, by omega, g2,
        hr1.trans hr2, ?_, g4, gb, g5, fun h => by have := g6 h; omega⟩
      show stepCmdW H k a stop hs st pos + 1 + runCmdW H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos)
        (stepCmd H k a stop hs st pos).pos + cpot q + 200 * (stateBits st' a pos' stop F).length + (stop.toNat - pos'.toNat) ≤
        _ + cmdEnd (runCmd H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos)
      omega
    case needsInput =>
      obtain ⟨b1, _, p', hR', _, _, _, hout, hj, _⟩ := hok.needsInput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
        (by rw [hst]; decide) (by rw [hst]; decide) (by rw [b1]; exact hp) (by rw [b1]; exact Nat.le_refl _) hl2 hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hst]; rfl
      refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, by rw [b1]; exact hp,
        by rw [b1]; exact Nat.le_refl _, hc0, ?_,
        fun _ => ⟨rfl, rfl⟩, (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide)),
        (fun h => absurd (hst.symm.trans h) (by decide))⟩
      show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p' + _ + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
      omega
    case needsOutput =>
      obtain ⟨p', hR', b1, b2, _, _, _, hout, hj⟩ := hok.needsOutput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
        (by rw [hst]; decide) (by rw [hst]; decide) b1 b2 hl2 hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hst]; rfl
      refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, b1, b2, hc0, ?_, fun _ => ⟨rfl, rfl⟩,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide)),
        (fun h => absurd (hst.symm.trans h) (by decide))⟩
      show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p' + _ + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
      omega
    case done =>
      obtain ⟨s, hR', b1, b2, _, h0, hout, hj⟩ := hok.done hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : (Phase.command s).out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
        (by rw [hst]; decide) (by rw [hst]; decide) b1 b2 hl2 hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hst]; rfl
      exact ⟨c0, .command s, _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, b1, b2, hc0, by
          show stepCmdW H k a stop hs st pos + 1 + 0 + cpot (.command s) + _ + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
          omega,
        fun _ => ⟨rfl, rfl⟩, (fun h => absurd (hst.symm.trans h) (by decide)), fun _ => ⟨s, rfl, h0⟩,
        (fun h => absurd (hst.symm.trans h) (by decide))⟩
    case bad =>
      have hw := badRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hk hp hrel.wf hst
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 92 := by unfold cmdEnd; rw [hst]; rfl
      exact ⟨0, p, st, pos, hrel, hci, ⟨[], rfl, rfl⟩, PendLe.rfl' _, Nat.le_refl _, hp, .refl _ _, by
          show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p + _ + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
          omega,
        fun e => absurd hst e,
        fun _ => ⟨stepCmd_badWin hst, (stepCmd_bad (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) hH hrel hp hst).1⟩,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩

end Brotli.Decoder
