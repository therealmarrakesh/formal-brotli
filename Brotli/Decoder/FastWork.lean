module

public import Brotli.Decoder.FastRun
public import Brotli.Decoder.WorkCmd

@[expose] public section

/-!
# The work of the command loop with the fast loop

Each function here mirrors the function of the same name without its `W`, branch by branch: a round each, and a copy by
its bytes. The fast loop's rounds are paid for by the bytes it writes (`fastLoop_work`), four a byte, with four more for
the round that leaves it; an entry into the fast loop that writes nothing costs two rounds, which the step that leads to
it holds (`cpot`).
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The work of `fastLoop`: a round each, and a copy's bytes. -/
def fastLoopW (H : Hdr) (kk : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (cap : USize)
    (T : ByteArray) (np : UInt64) (x : CmdExt) (flags : Flags) (mask size cap16 pB wB posLim : USize)
    (rEnd bEnd tb : UInt64) (modeOff lRow pairBase iRow iFb dRow s0 : USize)
    (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0) (X : XInv H x)
    (W : FWin H T kk mask size cap16 posLim stop pairBase np)
    (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (opos : USize)
    (iCount lCount dCount d01 d23 code ilen clen lits m : UInt64) (p1 p2 : UInt8)
    (S : FSt kk stop posLim word count pos ring m) : Nat :=
  if _hn : n = 0 then 1
  else
  have hk := W.k24
  have hmk := W.mask
  if hm0 : m ≠ 0 then
    have hm1 : 1 ≤ m.toNat := by
      have : m.toNat ≠ 0 := fun e => hm0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
      omega
    if hp : 2 ≤ m ∧ pairBase ≠ USize.ofNat 4294967295 then
      have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hp.1
      fillK a stop hs word count pos 15 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let e := row32 T pairBase (W.pair hp.2) C.size32 word'
      if (e >>> 8) &&& 255 = 2 then
        let l := e &&& 15
        have hl : l.toNat < 16 := and15_lt e
        have hc15 : 15 ≤ count'.toNat := hf.enough
        let b1 := (e >>> 16).toUInt8
        let b2 := (e >>> 24).toUInt8
        let r1 := wput ring opos mask hk hmk S.size b1
        let r2 := wput r1 (opos + USize.ofNat 1) mask hk hmk (wput_size ring opos mask hk hmk S.size b1) b2
        1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
          iFb dRow s0 C X W (n - USize.ofNat 1) (word' >>> l) (count' - l) pos' r2 (opos + USize.ofNat 2) iCount lCount
          dCount d01 d23 code ilen clen lits (m - 2) b2 b1
          ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
            lit_margin (j := 2) S.margin hm2 (by decide) hf.acct (by show l.toNat ≤ 15 * 2; omega) (by omega)⟩
      else
        let v := litT C p1 p2 word'
        let l := v &&& 15
        have hl : l.toNat < 16 := and15_lt v
        have hc15 : 15 ≤ count'.toNat := hf.enough
        let b := (v >>> 4).toUInt8
        1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
          iFb dRow s0 C X W (n - USize.ofNat 1) (word' >>> l) (count' - l) pos' (wput ring opos mask hk hmk S.size b)
          (opos + USize.ofNat 1) iCount lCount dCount d01 d23 code ilen clen lits (m - 1) b p1
          ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
            lit_margin (j := 1) S.margin hm1 (by decide) hf.acct (by show l.toNat ≤ 15 * 1; omega) (by omega)⟩
    else if hm2' : 2 ≤ m then
      have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hm2'
      fillK a stop hs word count pos 30 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let v := litT C p1 p2 word'
      let l := v &&& 15
      have hl : l.toNat < 16 := and15_lt v
      let b1 := (v >>> 4).toUInt8
      let w1 := word' >>> l
      let v2 := litT C b1 p1 w1
      let l2 := v2 &&& 15
      have hl2 : l2.toNat < 16 := and15_lt v2
      have hc30 : 30 ≤ count'.toNat := hf.enough
      let b2 := (v2 >>> 4).toUInt8
      let r1 := wput ring opos mask hk hmk S.size b1
      let r2 := wput r1 (opos + USize.ofNat 1) mask hk hmk (wput_size ring opos mask hk hmk S.size b1) b2
      1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
        iFb dRow s0 C X W (n - USize.ofNat 1) (w1 >>> l2) (count' - l - l2) pos' r2 (opos + USize.ofNat 2) iCount lCount
        dCount d01 d23 code ilen clen lits (m - 2) b2 b1
        ⟨drop2_wf (a := l) (b := l2) hf.wf (by omega) (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _, by
          intro _
          have hacct := hf.acct
          have hmar := S.margin (by omega)
          have h2 : (2 : UInt64).toNat = 2 := rfl
          have e1 : (count' - l).toNat = count'.toNat - l.toNat := u64_sub_le (by omega)
          have e2 : (count' - l - l2).toNat = count'.toNat - l.toNat - l2.toNat := by
            rw [u64_sub_le (by rw [e1]; omega), e1]
          have e3 : (m - 2).toNat = m.toNat - 2 := by rw [u64_sub_le (by rw [h2]; omega), h2]
          rw [e2, e3]
          omega⟩
    else
      fillK a stop hs word count pos 15 S.wf (by decide) S.posStop (fill_margin W.lim S.margin hm1 (by decide))
        fun word' count' pos' hf =>
      let v := litT C p1 p2 word'
      let l := v &&& 15
      have hl : l.toNat < 16 := and15_lt v
      have hc15 : 15 ≤ count'.toNat := hf.enough
      let b := (v >>> 4).toUInt8
      1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
        iFb dRow s0 C X W (n - USize.ofNat 1) (word' >>> l) (count' - l) pos' (wput ring opos mask hk hmk S.size b)
        (opos + USize.ofNat 1) iCount lCount dCount d01 d23 code ilen clen lits (m - 1) b p1
        ⟨drop1_wf hf.wf (by omega) (by omega), hf.posStop, wput_size _ _ _ hk hmk _ _,
          lit_margin (j := 1) S.margin hm1 (by decide) hf.acct (by show l.toNat ≤ 15 * 1; omega) (by omega)⟩
  else if lits ≠ 0 then
    if hcl : lCount = 0 ∨ posLim < pos then 1
    else
      let m' := umin (umin lits lCount) 16
      have hm' : m'.toNat ≤ 16 := by
        rw [umin_toNat, umin_toNat]
        exact Nat.le_trans (Nat.min_le_right _ _) (by decide)
      have hpl : pos.toNat ≤ posLim.toNat := Nat.le_of_not_lt fun h => hcl (Or.inr (USize.lt_iff_toNat_lt.mpr h))
      1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
        iFb dRow s0 C X W (n - USize.ofNat 1) word count pos ring opos iCount (lCount - m') dCount d01 d23 code ilen clen
        (lits - m') m' p1 p2 ⟨S.wf, S.posStop, S.size, fun _ => by omega⟩
  else
    if hd2 : posLim < pos ∨ (128 ≤ code ∧ dCount = 0) then 1
    else
    have hpl : pos.toNat ≤ posLim.toNat := Nat.le_of_not_lt fun h => hd2 (Or.inl (USize.lt_iff_toNat_lt.mpr h))
    have hlim := W.lim
    fillK a stop hs word count pos 40 S.wf (by decide) S.posStop (fun _ => by omega) fun word1 count1 pos1 hf1 =>
    let d0 := d01 &&& 0xFFFFFFFF
    distK C np word1 count1 clen d0 (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) hf1.wf
      fun ok2 word2x count2x dcode dx hok2 =>
    let d := if code < 128 then d0 else dx
    let written := usmin cap16 (opos + wB)
    if hbad : (¬ code < 128 ∧ ok2 = false) ∨ d = 0 ∨ written.toUInt64 < d then 1
    else
    have hw2 : (BitBuffer.mk (if code < 128 then word1 else word2x) (if code < 128 then count1 else count2x)).Wf := by
      by_cases hc : code < 128
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact hf1.wf
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact hok2 (by cases h : ok2 with
          | false => exact absurd (Or.inl ⟨hc, h⟩) hbad
          | true => rfl)
    have hd : d.toUSize.toNat + 16 ≤ 2 ^ kk.toNat := by
      have h1 : ¬ written.toUInt64 < d := fun h => hbad (Or.inr (Or.inr h))
      have h2 : written.toNat ≤ 2 ^ kk.toNat - 16 := by
        show (usmin cap16 (opos + wB)).toNat ≤ _
        rw [usmin_toNat, W.cap16]
        omega
      have h3 : d.toNat ≤ written.toNat := by
        have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h1)
        rwa [USize.toNat_toUInt64] at this
      have h16 : 16 ≤ 2 ^ kk.toNat := W.k16
      have h24 : 2 ^ kk.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
      rw [word_toUSize (by omega)]
      omega
    let dCount' := if code < 128 then dCount else dCount - 1
    let push := !(decide (code < 128)) && dcode != 0
    let n01 := if push then d ||| (d01 <<< 32) else d01
    let n23 := if push then (d01 >>> 32) ||| (d23 <<< 32) else d23
    let ring' := copyF ring (opos &&& mask) d.toUSize clen.toUSize mask size hk hmk W.size S.size (mask_lt hmk) hd
    have hsz' : ring'.size = 2 ^ kk.toNat := copyF_size _ _ _ _ _ _ hk hmk W.size S.size _ hd
    let opos' := opos + clen.toUSize
    let q1 := wget ring' (opos' - USize.ofNat 1) mask hmk hsz'
    let q2 := wget ring' (opos' - USize.ofNat 2) mask hmk hsz'
    if iCount = 0 then 1 + clen.toNat
    else
    have hp1 : pos1.toNat + 8 ≤ stop.toNat := by
      have := hf1.acct
      have : count1.toNat ≤ 64 := hf1.wf.count_le
      omega
    fillK a stop hs (if code < 128 then word1 else word2x) (if code < 128 then count1 else count2x) pos1 40 hw2
      (by decide) hf1.posStop (fun _ => hp1) fun word3 count3 pos3 hf3 =>
    icK C word3 count3 hf3.wf fun ok1 word4 count4 code' ilen' clen' hok1 =>
    if h1 : ok1 = false ∨ bEnd < opos'.toUInt64 + ilen' + clen' then 1 + clen.toNat
    else
      1 + clen.toNat + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow
        pairBase iRow iFb dRow s0 C X W (n - USize.ofNat 1) word4 count4 pos3 ring' opos' (iCount - 1) lCount dCount' n01
        n23 code' ilen' clen' ilen' 0 q1 q2
        ⟨hok1 (by cases h : ok1 with
          | false => exact absurd (Or.inl h) h1
          | true => rfl), hf3.posStop, hsz', fun h => absurd rfl h⟩
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred _hn
    have := usize_ne _hn
    omega

/-- The work of `fastEnter`: the fast loop's, the entry counted with the loop's first round. -/
def fastEnterW (H : Hdr) (kk : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (cap n : USize)
    (word count : UInt64) (ring : ByteArray) (wpos pend written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags) (x : CmdExt) (tag : Tag) (lits bEnd : UInt64) (pos : USize)
    (hinv : KInv H kk stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos) (hm : pos.toNat + 40 ≤ stop.toNat) : Nat :=
  have hT : TabOk H.arena H.litBase H.lMap H.icBase H.dBase H.dMap H.lTriv H.nL.toNat H.nI.toNat H.nD.toNat
      H.treesL.toNat H.treesD.toNat H.npostfix H.ndirect H.tabF0.toNat := by
    obtain ⟨m, hm⟩ := hinv.hdr
    exact hm.tab
  let l0 := H.tabF0 + (H.nI.toUSize <<< USize.ofNat 11)
  let d0 := l0 + (H.nL.toUSize <<< USize.ofNat 8)
  let s0 := d0 + (H.nD.toUSize <<< USize.ofNat 4)
  have hr := rows_toNat hinv.hdr hinv.lCur hinv.iCur hinv.dCur
  have hmodes : x.lCur.toUSize.toNat < H.modes.size := by rw [cur_usize hinv.lCur, H.modesSize]; exact hinv.lCur
  let modeOff := ((H.modes.uget x.lCur.toUSize hmodes).toUInt64 <<< 9).toUSize
  have hx := pairIdx_toNat hinv.hdr hinv.lCur
  let pv := load32 H.arena (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2) +
    (x.lCur.toUSize <<< USize.ofNat 2)) (by rw [hx.1]; exact hx.2) hT.size32
  let pairBase := if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize
  have hpair : pairBase ≠ USize.ofNat 4294967295 → pairBase.toNat + 1024 ≤ H.arena.size := by
    intro hne
    by_cases hv : pv = 4294967295
    · exact absurd (by show (if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize) = _; rw [ite_eq_left hv]) hne
    · have hpv : pv.toNat = leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 := by
        show (load32 _ _ _ _).toNat = _
        rw [load32_toNat, hx.1]
      have hpv' : leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 ≠ 4294967295 := fun e =>
        hv (UInt64.toNat_inj.mp (by rw [hpv, e]; rfl))
      have hp := (hT.pix _ hinv.lCur hpv').2.1
      show (if pv = 4294967295 then USize.ofNat 4294967295 else pv.toUSize).toNat + 1024 ≤ _
      rw [ite_eq_right hv, word_toUSize (by rw [hpv]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), hpv]
      omega
  have h40 : (USize.ofNat 40).toNat = 40 := fastLit (by decide)
  have h16 : (USize.ofNat 16).toNat = 16 := fastLit (by decide)
  fastLoopW H kk a stop hs cap H.arena H.npostfix x flags (ringMask kk) (ringSize kk) (ringSize kk - USize.ofNat 16)
    (pend - wpos) (written - wpos) (stop - USize.ofNat 40) (remaining + wpos.toUInt64) bEnd (trivBase H x.lCur hinv.lCur)
    modeOff (l0 + (x.lCur.toUSize <<< USize.ofNat 8)) pairBase (H.tabF0 + (x.iCur.toUSize <<< USize.ofNat 11))
    (((s0 + USize.ofNat 4160) >>> USize.ofNat 2) + x.iCur.toUSize) (d0 + (x.dCur.toUSize <<< USize.ofNat 4)) s0
    ⟨hinv.hdr, rfl, hinv.lCur, hinv.iCur, hinv.dCur, rfl,
      by rw [modeOff_toNat (H.modesLt _ hmodes), uget_toNat, cur_usize hinv.lCur], hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2⟩
    ⟨hinv.iPrev, hinv.lPrev, hinv.dPrev⟩
    ⟨hinv.k24, hinv.k16, ringMask_toNat hinv.k24, ringSize_toNat hinv.k24,
      by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h16, ringSize_toNat hinv.k24]; exact hinv.k16)),
        h16, ringSize_toNat hinv.k24],
      by rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h40]; omega)), h40]; omega, hpair, rfl⟩
    n word count pos ring wpos iCount lCount dCount (x.d0 ||| (x.d1 <<< 32)) (x.d2 ||| (x.d3 <<< 32)) x.code x.ilen x.clen
    lits 0 p1 p2 ⟨hinv.wf, hinv.pos, hinv.size, fun h => absurd rfl h⟩

open Classical in
/-- The work of `runCmdKF`: a round, and in it an entry into the fast loop, which counts the fast loop's work, or a step
of the step machine. -/
noncomputable def runCmdKFW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize)
    (fresh : Bool) :
    (word count : UInt64) → (ring : ByteArray) → (wpos pend cap written : USize) → (p1 p2 : UInt8) →
    (remaining iCount lCount dCount : UInt64) → (flags : Flags) →
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64) →
    (wordBuf : ByteArray) → (wordPos : USize) → (tag : Tag) → (left : UInt64) → (pos : USize) →
    KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag pos →
    Nat :=
  if _hn : n = 0 then
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 1
  else
    fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv =>
    let lits : UInt64 := if tag = .literals then left else 0
    let rm := room k cap
    let roomLeft : UInt64 := if rm ≤ pend then 0 else (rm - pend).toUInt64
    let ahead := umin remaining roomLeft
    let bEnd := wpos.toUInt64 + ahead
    if hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
        lits ≤ ahead ∧ clen ≤ ahead - lits then
      have hm : pos.toNat + 40 ≤ stop.toNat := by
        have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
        rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
        have := hinv.pos
        omega
      1 + fastEnterW H k a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags
          ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
            wordPos⟩ tag lits bEnd pos hinv hm +
        match fastEnter H k a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags
            ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
              wordPos⟩ tag lits bEnd pos hinv hm with
        | ⟨⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
            ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
              wordPos⟩, tag, left, pos, _⟩, h⟩ =>
          runCmdKFW H k a stop hs (n - USize.ofNat 1) false word count ring wpos pend cap written p1 p2 remaining iCount
            lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
            wordPos tag left pos h
    else
      stepCmdW H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
        iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next)
        pos + 1 +
      kcase (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
          if h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
              wordPos tag pos then
            runCmdKFW H k a stop hs (n - USize.ofNat 1) true word count ring wpos pend cap written p1 p2 remaining
              iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase
              dist wordBuf wordPos tag left pos h
          else 0)
        (fun _ => 0)
        (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
          .next) pos)
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred _hn
    have := usize_ne _hn
    omega

/-- The work of `runCmdF`: the record's fields, then the loop on them. -/
noncomputable def runCmdFW (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize)
    (st : Cmd) (pos : USize) (h : CmdInv H k stop st pos) : Nat :=
  match st, h with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
      ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
      tag, left, _, _⟩, h =>
    runCmdKFW H k a stop hs n true word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
      iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h

end Brotli.Decoder
