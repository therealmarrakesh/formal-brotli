import Brotli.Decoder.WorkHdr
import Brotli.Decoder.Work

/-!
# The work of a meta-block's commands

Each function here mirrors the command loop's step or helper of the same name without its `W`, branch by branch, and
counts the rounds of its loops. A step's work is a constant, ten for each byte it adds to the window, and for a step that
begins a dictionary word, the word's building.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

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
    let l := v &&& 63
    if hl : l ≤ rc then
      let byte := (v >>> 8).toUInt8
      have hl63 : l.toNat < 64 := by
        have : (v &&& 63).toNat = v.toNat % 64 := by
          rw [UInt64.toNat_and]
          exact Nat.and_two_pow_sub_one_eq_mod v.toNat 6
        show (v &&& 63).toNat < 64
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

/-- The literal loop's work: ten for each literal it writes, and eleven. -/
theorem literalRunW_le {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    literalRunW C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp +
      10 * (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤
      10 * N + 11 := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [literalRunW, dite_eq_left hz, literalRun, dite_eq_left hz]
    show 1 + 10 * (0 : USize).toNat ≤ _
    rw [show (0 : USize).toNat = 0 from rfl]
    omega
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hR := refillW_le (word := word) (count := count) hs hp
    rw [literalRunW, dite_eq_right hn, literalRun, dite_eq_right hn]
    dsimp only
    split
    · rw [Nat.add_assoc]
      refine Nat.le_trans (Nat.add_le_add_left (ih _ _ _ _ _ _ _ _ _ _ _ _ ?_) _) ?_
      · rw [hpred]
        omega
      · omega
    · show refillW word count a pos stop hs + 1 + 10 * n.toNat ≤ _
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

/-- A dictionary word's building: at most 93 rounds. -/
theorem dictBuildW_le (clen wordId : UInt64) (h : dictValid clen wordId) : dictBuildW clen wordId h ≤ 93 := by
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
    applyDistanceW st d ≤ 1 + (if (applyDistance st pos dc d).status = .next ∧ (applyDistance st pos dc d).tag ≠ .word then 0 else 94) ∧
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

theorem literalsW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepLiteralsW H k a stop hs st pos ≤ 12 + 10 * addedW st.pend (stepLiterals H k a stop hs st pos) := by
  unfold addedW
  unfold stepLiteralsW stepLiterals
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    omega
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases hc : st.lCount = 0
  · rw [ite_eq_left hc]
    omega
  rw [ite_eq_right hc, ite_eq_right hc]
  by_cases hr : room k st.cap ≤ st.pend
  · rw [ite_eq_left hr]
    omega
  rw [ite_eq_right hr, ite_eq_right hr]
  have h1 := room_lt hr
  have h2 := room_le (cap := st.cap) hk
  have h3 : (2 : Nat) ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  unfold literalsRunW literalsRun
  split
  · split
    · dsimp only
      have hrun' : (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize.toNat ≤
          (room k st.cap).toNat - st.pend.toNat := by
        have hm1 := umin_toNat st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)
        have hm2 := umin_toNat st.lCount (room k st.cap - st.pend).toUInt64
        have hs : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
        have h4 : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
        rw [USize.toNat_toUInt64, hs] at hm2
        rw [word_toUSize (by rw [hm1, hm2]; omega), hm1, hm2]
        omega
      generalize (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize = run at hrun' ⊢
      have key : ∀ (W : Nat) (L : LitRun), W + 10 * L.left.toNat ≤ 10 * run.toNat + 11 → L.left.toNat ≤ run.toNat →
          W + 1 ≤ 12 + 10 * (if (finishLiterals (clearRing st) L run (ringSize k)).status = .bad then 0
            else (finishLiterals (clearRing st) L run (ringSize k)).pend.toNat - st.pend.toNat) := by
        intro W L hW hL
        have hnb : (finishLiterals (clearRing st) L run (ringSize k)).status ≠ .bad := by
          unfold finishLiterals
          dsimp only
          split <;> exact fun e => StepStatus.noConfusion e
        rw [ite_eq_right hnb]
        show W + 1 ≤ 12 + 10 * (((clearRing st).pend + (run - L.left)).toNat - st.pend.toNat)
        have hsub : (run - L.left).toNat = run.toNat - L.left.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hL)
        rw [show (clearRing st).pend = st.pend from rfl, pend_add (by rw [hsub]; omega), hsub]
        omega
      exact key _ _ (literalRunW_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
        (literalRun_left_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl)
    · dsimp only
      omega
  · omega

/-- The word cost a step may have: none when it goes on to anything but a word's bytes. -/
def wordCost (t : Tag) (r : Cmd) : Nat := if r.status = .next ∧ ¬ (r.tag = .word ∧ t ≠ .word) then 0 else 95

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
                ¬ ((applyDistance st' pos (wordSym v) d).tag = .word ∧ st.tag ≠ .word) then 0 else 95) - 1) ∧
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

/-- A command loop step's work, once the buffer is refilled: twelve, ten for each byte it adds to the window, and a
dictionary word's building when it begins one or stops having added no byte. -/
theorem stepAtW_le {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize}
    (hk : k.toNat ≤ 24) : stepAtW H k a stop hs st pos ≤
      12 + 10 * addedW st.pend (stepAt H k a stop hs st pos) + wcost st.pend st.tag (stepAt H k a stop hs st pos) := by
  unfold stepAtW stepAt
  cases ht : st.tag with
  | command => dsimp only; omega
  | insertCopy => dsimp only; omega
  | copyLength => dsimp only; omega
  | literals => have := literalsW_le (H := H) (a := a) (hs := hs) (st := st) (pos := pos) hk; dsimp only; omega
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
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) : stepCmdW H k a stop hs st pos ≤
      21 + 10 * addedW st.pend (stepCmd H k a stop hs st pos) + wcost st.pend st.tag (stepCmd H k a stop hs st pos) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepCmdW stepCmd
  rw [dite_eq_left hp', dite_eq_left hp']
  dsimp only
  have h1 := refillW_le (word := st.word) (count := st.count) hs hp
  have h2 := stepAtW_le (H := H) (a := a) (hs := hs)
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count })
    (pos := (refill st.word st.count a pos stop hs hp).pos) hk
  dsimp only at h2
  exact Nat.le_trans (Nat.add_le_add_left h2 _) (by omega)

/-! ### Pausing for output

The command loop pauses for output only when its room is used up. -/

/-- A command loop step, once the buffer is refilled, pauses for output only with no room left. -/
theorem stepAt_full {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} :
    (stepAt H k a stop hs st pos).status = .needsOutput →
      room k (stepAt H k a stop hs st pos).cap ≤ (stepAt H k a stop hs st pos).pend := by
  unfold stepAt
  cases ht : st.tag <;> dsimp only
  · unfold stepCommand markStep clearSeen
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepInsertCopy insertStep markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepCopyLength markStep
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)))
  · unfold stepLiterals literalsRun finishLiterals markStep clearSeen clearRing
    try dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => StepStatus.noConfusion e)) | (intro _; assumption))
  · unfold stepDistance applyDistance applyWord applyBuilt markStep clearSeen
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

/-- The potential of a command's place. -/
def cpot (p : Phase) : Nat := 22 * crank p + (if 2 ≤ crank p then 95 else 0)

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

theorem cpot_le (p : Phase) : cpot p ≤ 271 := by
  have := crank_le p
  unfold cpot
  split <;> omega

/-- A command loop step that goes on, against the potential: what it does is paid by the potential, 366 for each bit it
reads and 281 for each byte it adds. -/
theorem stepCmd_pot {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hm : m.ndirect ≤ 120) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st p) (hci : CInv w p) (hp : pos.toNat ≤ stop.toNat) (hn : (stepCmd H k a stop hs st pos).status = .next) :
    ∃ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' ∧ OutStep p p' st (stepCmd H k a stop hs st pos) ∧ CInv w p' ∧
      (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧ pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧
      ∀ F, ∃ n, 1 ≤ n ∧ ReachN (cStep w m) n p (stateBits st a pos stop F) p'
        (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F) ∧
        stepCmdW H k a stop hs st pos + 1 + cpot p' + 366 * (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F).length ≤
          cpot p + 366 * (stateBits st a pos stop F).length + 281 * (p'.out.length - p.out.length) := by
  obtain ⟨p', hR, hout, h2, h1, hj⟩ := stepCmd_count (hs := hs) hH hrel hp hn
  have hk := hrel.k24
  have hW := stepCmdW_le (H := H) (a := a) (hs := hs) (st := st) hk hp
  obtain ⟨l, hl1, hl2⟩ := hout
  refine ⟨p', hR, ⟨l, hl1, hl2⟩, ?_, h2, h1, fun F => ?_⟩
  · obtain ⟨n, hn1, hr⟩ := hj []
    exact (creach hm hr hci).1
  obtain ⟨n, hn1, hr⟩ := hj F
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hp1 := c4 hn1
  refine ⟨n, hn1, hr, ?_⟩
  have hq8 := crank_le p'
  have hp8 := crank_le p
  have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
  unfold addedW at hW
  rw [ite_eq_right (by rw [hn]; exact fun e => StepStatus.noConfusion e), hl2] at hW
  generalize (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F).length = cb at c1 c3 ⊢
  generalize (stateBits st a pos stop F).length = bb at c1 c3 ⊢
  have hx : p'.out.length - p.out.length = l.length := by omega
  rw [hx] at c3 ⊢
  have hWo : wordCost st.tag (stepCmd H k a stop hs st pos) ≤ 95 := by unfold wordCost; split <;> omega
  have hWc : wcost st.pend st.tag (stepCmd H k a stop hs st pos) ≤ 95 := by
    unfold wcost
    split
    · exact hWo
    · omega
  unfold cpot
  by_cases hmv : cb = bb ∧ l.length = 0
  · have hlt : crank p' + n ≤ crank p := by
      rw [hmv.1, hmv.2] at c3
      omega
    have hpe : (stepCmd H k a stop hs st pos).pend = st.pend := USize.toNat_inj.mp (by rw [hl2, hmv.2]; rfl)
    have hwc : wcost st.pend st.tag (stepCmd H k a stop hs st pos) = wordCost st.tag (stepCmd H k a stop hs st pos) := by
      unfold wcost
      rw [ite_eq_left hpe]
    rw [hwc] at hW
    by_cases hwd : (stepCmd H k a stop hs st pos).tag = .word ∧ st.tag ≠ .word
    · obtain ⟨s, pending, rfl⟩ := hR.word_of hwd.1
      have h1' : crank (.word s pending) = 1 := by
        cases pending with
        | nil =>
          have : crank (Phase.word s []) = 8 := rfl
          omega
        | cons => rfl
      rw [h1'] at hlt ⊢
      split <;> split <;> omega
    · have h0 : wordCost st.tag (stepCmd H k a stop hs st pos) = 0 := by
        unfold wordCost
        exact ite_eq_left ⟨hn, hwd⟩
      split <;> split <;> omega
  · by_cases hl0 : l.length = 0
    · split <;> split <;> omega
    · have hpe : (stepCmd H k a stop hs st pos).pend ≠ st.pend := fun e => by
        rw [e] at hl2
        omega
      have hwc : wcost st.pend st.tag (stepCmd H k a stop hs st pos) = 0 := by
        unfold wcost
        rw [ite_eq_right hpe]
      rw [hwc] at hW
      split <;> split <;> omega

/-- A round that stops the command loop: its work, and the potential of where it stops, are paid for by the potential,
366 for each bit it reads, 281 for each byte it adds, and 117. -/
theorem stopRound_pay {w : Nat} {m : MetaBlockHeader} {H : Hdr} {k : USize} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {st : Cmd} {pos : USize} {p q : Phase} {c0 L : Nat} {bs c : List Bool} (hm : m.ndirect ≤ 120)
    (hk : k.toNat ≤ 24) (hp : pos.toNat ≤ stop.toNat) (hL : (stepCmd H k a stop hs st pos).status ≠ .bad →
      (stepCmd H k a stop hs st pos).pend.toNat = st.pend.toNat + L) (hci : CInv w p)
    (hr : ReachN (cStep w m) c0 p bs q c) (hlo : q.out.length = L + p.out.length) :
    stepCmdW H k a stop hs st pos + 1 + cpot q + 366 * c.length ≤ cpot p + 366 * bs.length + 281 * L + 117 := by
  have hW := stepCmdW_le (H := H) (a := a) (hs := hs) (st := st) hk hp
  have hc : wcost st.pend st.tag (stepCmd H k a stop hs st pos) ≤ 95 := by
    unfold wcost wordCost
    repeat' split
    all_goals omega
  have hA : addedW st.pend (stepCmd H k a stop hs st pos) ≤ L := by
    unfold addedW
    split
    · omega
    · rename_i hb
      rw [hL hb]
      omega
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hq8 := crank_le q
  have hp8 := crank_le p
  rw [hlo] at c3
  cases c0 with
  | zero =>
    obtain ⟨e1, e2⟩ := reachN_zero hr
    subst e1
    subst e2
    omega
  | succ c0 =>
    have hp1 := c4 (by omega)
    unfold cpot
    split <;> split <;> omega

/-- The end of the command loop's work: one when its budget runs out, and 117 for a round that stops it. -/
def cmdEnd (r : Cmd) : Nat := if r.status = .next then 1 else 117

/-- The command loop's work, against the potential: what it does is paid for by the potential, 366 for each bit it
reads, 281 for each byte it adds, and its end. -/
theorem runCmdW_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hm : m.ndirect ≤ 120) (hH : HdrRel H m) : ∀ (N : Nat) (n : USize) (st : Cmd) (p : Phase) (pos : USize), n.toNat = N →
      Rel w k.toNat m st p → CInv w p → pos.toNat ≤ stop.toNat → ∀ F, ∃ c q st' pos', Rel w k.toNat m st' q ∧ CInv w q ∧
        OutStep p q st st' ∧ PendLe st st' ∧ pos.toNat ≤ pos'.toNat ∧ pos'.toNat ≤ stop.toNat ∧
        ReachN (cStep w m) c p (stateBits st a pos stop F) q (stateBits st' a pos' stop F) ∧
        runCmdW H k a stop hs n st pos + cpot q + 366 * (stateBits st' a pos' stop F).length ≤
          cpot p + 366 * (stateBits st a pos stop F).length + 281 * (q.out.length - p.out.length) +
            cmdEnd (runCmd H k a stop hs n st pos) ∧
        ((runCmd H k a stop hs n st pos).status ≠ .bad → st' = runCmd H k a stop hs n st pos ∧ pos' = (runCmd H k a stop hs n st pos).pos) ∧
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
      fun _ => ⟨rfl, rfl⟩, fun h => StepStatus.noConfusion h, fun _ => by omega⟩
    rw [runCmdW, dite_eq_left hz]
    show 1 + cpot p + 366 * (stateBits st a pos stop F).length ≤ _ + cmdEnd (markStep st pos .next)
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
      obtain ⟨c2, q, st', pos', hq, hciq, o2, l2, g1, g2, hr2, g3, g4, g5, g6⟩ :=
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
        hr1.trans hr2, ?_, g4, g5, fun h => by have := g6 h; omega⟩
      show stepCmdW H k a stop hs st pos + 1 + runCmdW H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos)
        (stepCmd H k a stop hs st pos).pos + cpot q + 366 * (stateBits st' a pos' stop F).length ≤
        _ + cmdEnd (runCmd H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos)
      omega
    case needsInput =>
      obtain ⟨b1, _, p', hR', _, _, _, hout, hj, _⟩ := hok.needsInput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hk hp (fun _ => hl2) hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 117 := by unfold cmdEnd; rw [hst]; rfl
      refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, by rw [b1]; exact hp,
        by rw [b1]; exact Nat.le_refl _, hc0, ?_,
        fun _ => ⟨rfl, rfl⟩, (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩
      show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p' + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
      omega
    case needsOutput =>
      obtain ⟨p', hR', b1, b2, _, _, _, hout, hj⟩ := hok.needsOutput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hk hp (fun _ => hl2) hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 117 := by unfold cmdEnd; rw [hst]; rfl
      refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, b1, b2, hc0, ?_, fun _ => ⟨rfl, rfl⟩,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩
      show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p' + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
      omega
    case done =>
      obtain ⟨s, hR', b1, b2, _, h0, hout, hj⟩ := hok.done hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
      obtain ⟨l, hl1, hl2⟩ := hout
      have hlo : (Phase.command s).out.length = l.length + p.out.length := by rw [hl1, List.length_append]
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hk hp (fun _ => hl2) hci hc0 hlo
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 117 := by unfold cmdEnd; rw [hst]; rfl
      exact ⟨c0, .command s, _, _, hR', hci', ⟨l, hl1, hl2⟩, stepCmd_pendLe H k a stop hs st pos, b1, b2, hc0, by
          show stepCmdW H k a stop hs st pos + 1 + 0 + cpot (.command s) + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
          omega,
        fun _ => ⟨rfl, rfl⟩, fun _ => ⟨s, rfl, h0⟩,
        (fun h => absurd (hst.symm.trans h) (by decide))⟩
    case bad =>
      have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) (L := 0) hm hk hp (fun h => absurd hst h)
        hci (.refl p (stateBits st a pos stop F)) (by omega)
      have he : cmdEnd (stepCmd H k a stop hs st pos) = 117 := by unfold cmdEnd; rw [hst]; rfl
      exact ⟨0, p, st, pos, hrel, hci, ⟨[], rfl, rfl⟩, PendLe.rfl' _, Nat.le_refl _, hp, .refl _ _, by
          show stepCmdW H k a stop hs st pos + 1 + 0 + cpot p + _ ≤ _ + cmdEnd (stepCmd H k a stop hs st pos)
          omega,
        fun e => absurd hst e,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩

end Brotli.Decoder
