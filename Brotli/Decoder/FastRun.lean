module

public import Brotli.Decoder.FastProof
public import Brotli.Decoder.Positions

@[expose] public section

/-!
# The command loop with the fast loop does the spec's work

`runCmdKF` runs the fast loop (`FastLoop.lean`) where a command's literals or its distance are next and the chunk and
the room allow it, and the step machine's steps otherwise. Entering the fast loop is a move (`fastEnter_ok`, from
`fastLoop_ok`), and a step is `stepCmd` (through `kstep_eq`), so a property of runs holds of the loop if it goes back
over moves and over steps (`runCmdKF_rec`, from a record `runCmdF_rec`); the loop is a run (`runCmdF_ok`). The scratch
record a literal run builds its result in changes nothing (`runCmdKF_cell`), which lets a step's continuation be taken
as one on the fields alone.
-/

namespace Brotli.Decoder

open Brotli.Spec

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray}
  {stop : USize} {p : Phase} {st r : Cmd} {pos : USize}

/-- A move of nothing between two records with the same bits, position and bytes waiting. -/
theorem MoveOk.same (hrel : Rel w k m r p) (hw : r.word = st.word) (hc : r.count = st.count) (hpe : r.pend = st.pend)
    (hp : r.pos = pos) (hs : pos.toNat ≤ stop.toNat) : MoveOk w k m K a stop p st pos p r := by
  have e : ∀ F, stateBits r a r.pos stop F = stateBits st a pos stop F := fun F => by
    unfold stateBits
    rw [hw, hc, hp]
  exact ⟨hrel, by rw [hp]; exact Nat.le_refl _, by rw [hp]; exact hs, fun F => by rw [e F], ⟨[], rfl, by rw [hpe]; rfl⟩,
    fun F => by rw [e F]; exact Reach.refl _ _⟩

theorem exists_move_trans {p0 : Phase} {st0 : Cmd} (m0 : MoveOk w k m K a stop p st pos p0 st0)
    (h : ∃ p', MoveOk w k m K a stop p0 st0 st0.pos p' r) : ∃ p', MoveOk w k m K a stop p st pos p' r :=
  let ⟨p', m1⟩ := h
  ⟨p', m0.trans m1⟩

theorem exists_move_trans' {p0 : Phase} {st0 : Cmd} {Q R : Cmd → Prop} (m0 : MoveOk w k m K a stop p st pos p0 st0)
    (hq : Q r → R r) (h : ∃ p', MoveOk w k m K a stop p0 st0 st0.pos p' r ∧ Q r) :
    ∃ p', MoveOk w k m K a stop p st pos p' r ∧ R r :=
  let ⟨p', m1, q⟩ := h
  ⟨p', m0.trans m1, hq q⟩

end

theorem mask_small {x kk : USize} (hk : kk.toNat ≤ 24) (hx : x.toNat < 2 ^ kk.toNat) : x &&& ringMask kk = x :=
  USize.toNat_inj.mp (by rw [USize.toNat_and, ringMask_toNat hk, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx])

theorem and_mask32 {x : UInt64} (hx : x.toNat < 2 ^ 32) : x &&& 0xFFFFFFFF = x :=
  UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hx])

/-- Into the fast loop from the step machine's record at a command's literals or its distance: a move to whatever the
loop leaves with. The command's literals and copy fit what is ahead (the room and the meta-block). -/
theorem fastEnter_ok {α : Type} {w : Nat} {mH : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w mH s bs >>= fun (s1, b) => K s1 b)
    {H : Hdr} {kk : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {cap : USize}
    {word count : UInt64} {ring : ByteArray} {wpos pend written : USize} {p1 p2 : UInt8}
    {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag} {left lits bEnd : UInt64}
    {pos : USize}
    (hinv : KInv H kk stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos) (hm : pos.toNat + 40 ≤ stop.toNat) (hH : HdrRel H mH) {p : Phase}
    (hrel : Rel w kk.toNat mH ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount,
      flags, x, tag, left, pos, .next⟩ p)
    (htag : tag = .literals ∨ tag = .distance) (hlits : lits = if tag = .literals then left else 0)
    (hbE : bEnd = wpos.toUInt64 + umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64))
    (hl : lits ≤ umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64))
    (hcl : x.clen ≤ umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64) - lits) :
    ∃ p', MoveOk w kk.toNat mH K a stop p ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount,
      lCount, dCount, flags, x, tag, left, pos, .next⟩ pos p'
      (fastEnter H kk a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags x tag
        lits bEnd pos hinv hm).val ∧
      (fastEnter H kk a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags x tag
        lits bEnd pos hinv hm).val.cap = cap ∧
      (fastEnter H kk a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags x tag
        lits bEnd pos hinv hm).val.pend.toNat ≤ max pend.toNat (room kk cap).toNat := by
  generalize hA : umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64) = A at hbE hl hcl
  have hk := hinv.k24
  have h16 := hinv.k16
  have hwp := hinv.wpos
  have hwr := hinv.written
  have hR : 2 ^ kk.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hCx : ∃ out rem ds ic lit dist, Core w kk.toNat mH ⟨word, count, ring, wpos, pend, cap, written, p1, p2,
      remaining, iCount, lCount, dCount, flags, x, tag, left, pos, .next⟩ out rem ds ic lit dist := by
    rcases htag with ht | ht
    · obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hrel.literals_of ht
      exact ⟨_, _, _, _, _, _, hrel.1⟩
    · obtain ⟨_, _, _, rfl⟩ := hrel.distance_of ht
      exact ⟨_, _, _, _, _, _, hrel.1⟩
  obtain ⟨_, _, ds, _, _, _, hC⟩ := hCx
  have hpL : pend.toNat + 16 ≤ 2 ^ kk.toNat := hC.pendLe
  have hd0 : x.d0.toNat < 2 ^ 32 := by rw [← hC.d0]; exact hC.dsLt.1
  have hd1 : x.d1.toNat < 2 ^ 32 := by rw [← hC.d1]; exact hC.dsLt.2.1
  have hd2 : x.d2.toNat < 2 ^ 32 := by rw [← hC.d2]; exact hC.dsLt.2.2.1
  have hd3 : x.d3.toNat < 2 ^ 32 := by rw [← hC.d3]; exact hC.dsLt.2.2.2
  have hAN : A.toNat ≤ remaining.toNat ∧ pend.toNat + A.toNat + 16 ≤ 2 ^ kk.toNat := by
    rw [← hA, umin_toNat]
    have hrl := room_le16 (cap := cap) hk h16
    split
    · rw [h0]
      omega
    · rename_i h
      have h' : pend.toNat < (room kk cap).toNat := Nat.lt_of_not_le fun e => h (USize.le_iff_toNat_le.mpr e)
      rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
      omega
  have hAm : pend.toNat + A.toNat ≤ max pend.toNat (room kk cap).toNat := by
    rw [← hA, umin_toNat]
    split
    · rw [h0]
      omega
    · rename_i h
      have h' : pend.toNat < (room kk cap).toNat := Nat.lt_of_not_le fun e => h (USize.le_iff_toNat_le.mpr e)
      rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
      omega
  have hlN : lits.toNat ≤ A.toNat := UInt64.le_iff_toNat_le.mp hl
  have hcN : x.clen.toNat ≤ A.toNat - lits.toNat := by
    have := UInt64.le_iff_toNat_le.mp hcl
    rwa [u64_sub_le hlN] at this
  have hbN : bEnd.toNat = wpos.toNat + A.toNat := by
    rw [hbE, u64_add_small (by rw [USize.toNat_toUInt64]; omega), USize.toNat_toUInt64]
  have hl0 : (lits + 0).toNat = lits.toNat := by rw [UInt64.add_zero]
  have N0 : FNum wpos (pend - wpos) (written - wpos) (remaining + wpos.toUInt64) bEnd kk.toNat
      ((lits + 0).toNat + x.clen.toNat) := by
    have e2 : (wpos + (pend - wpos)).toNat = pend.toNat := by rw [USize.add_comm, USize.sub_add_cancel]
    have e3 : (wpos + (written - wpos)).toNat = written.toNat := by rw [USize.add_comm, USize.sub_add_cancel]
    have e4 : (remaining + wpos.toUInt64 - wpos.toUInt64).toNat = remaining.toNat := by rw [UInt64.add_sub_cancel]
    exact ⟨by rw [hl0]; omega, by rw [e4]; omega, by omega, by rw [e2]; omega, by rw [e3]; omega⟩
  have e0 : fabs word count ring wpos (ringMask kk) (pend - wpos) cap (ringSize kk - USize.ofNat 16) (written - wpos)
      (remaining + wpos.toUInt64) iCount lCount dCount flags x (x.d0 ||| (x.d1 <<< 32)) (x.d2 ||| (x.d3 <<< 32)) x.code
      x.ilen x.clen lits 0 p1 p2 pos = ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount,
      dCount, flags, x, if (0 : UInt64) = 0 ∧ lits = 0 then .distance else .literals, lits, pos, .next⟩ := by
    obtain ⟨g1, g2⟩ := or_shl32 (a := x.d0) (b := x.d1) hd0
    obtain ⟨g3, g4⟩ := or_shl32 (a := x.d2) (b := x.d3) hd2
    have f2 : wpos + (pend - wpos) = pend := by rw [USize.add_comm, USize.sub_add_cancel]
    have f3 : usmin (ringSize kk - USize.ofNat 16) (wpos + (written - wpos)) = written := by
      rw [USize.add_comm, USize.sub_add_cancel]
      apply USize.toNat_inj.mp
      rw [usmin_toNat, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr
        (by rw [fastLit (by decide), ringSize_toNat hk]; exact h16)), fastLit (by decide), ringSize_toNat hk]
      omega
    unfold fabs fexit
    rw [mask_small hk hwp, f2, f3, UInt64.add_sub_cancel, UInt64.add_zero, UInt64.add_zero, g1, g2, g3, g4,
      and_mask32 hd1, and_mask32 hd3]
  have key : ∃ p0, MoveOk w kk.toNat mH K a stop p ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining,
      iCount, lCount, dCount, flags, x, tag, left, pos, .next⟩ pos p0
      (fabs word count ring wpos (ringMask kk) (pend - wpos) cap (ringSize kk - USize.ofNat 16) (written - wpos)
        (remaining + wpos.toUInt64) iCount lCount dCount flags x (x.d0 ||| (x.d1 <<< 32)) (x.d2 ||| (x.d3 <<< 32))
        x.code x.ilen x.clen lits 0 p1 p2 pos) := by
    rw [e0]
    rcases htag with ht | ht
    · subst ht
      rw [ite_eq_left rfl] at hlits
      subst hlits
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hrel.literals_of rfl
      by_cases hz : lits = 0
      · rw [ite_eq_left ⟨rfl, hz⟩]
        exact litEnd_move (K := K) (stop := stop) (pos := pos) hH hrel hz hinv.pos hs
      · rw [ite_eq_right (fun h => hz h.2)]
        exact ⟨_, MoveOk.refl hrel rfl hinv.pos⟩
    · subst ht
      rw [ite_eq_right (by decide)] at hlits
      subst hlits
      rw [ite_eq_left ⟨rfl, rfl⟩]
      obtain ⟨_, _, _, rfl⟩ := hrel.distance_of rfl
      obtain ⟨hC', h1, h2, h3, h4⟩ := hrel
      exact ⟨_, MoveOk.same ⟨{ hC' with }, h1, h2, h3, h4⟩ rfl rfl rfl rfl hinv.pos⟩
  obtain ⟨p0, m0⟩ := key
  unfold fastEnter
  dsimp only
  refine exists_move_trans' (Q := FFrame cap (pend - wpos) bEnd wpos)
    (R := fun r => r.cap = cap ∧ r.pend.toNat ≤ max pend.toNat (room kk cap).toNat) m0 ?_ ?_
  · intro ⟨fc, o, g1, g2, g3⟩
    refine ⟨fc, ?_⟩
    rw [g3]
    have e : o + (pend - wpos) = (o - wpos) + pend := by
      conv => rhs; rw [← USize.sub_add_cancel pend wpos]
      rw [← USize.add_assoc, USize.add_comm (o - wpos) (pend - wpos), USize.add_assoc, USize.sub_add_cancel,
        USize.add_comm]
    have hd : (o - wpos).toNat = o.toNat - wpos.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr g1)
    rw [e, fastAdd (by omega), hd]
    omega
  refine fastLoop_ok hK hH rfl rfl ?_ _ _ word count pos ring wpos iCount lCount dCount _ _ _ _ _ lits 0 p1 p2
    _ rfl rfl N0 (by have := lCount.toNat_lt; omega) (by omega) p0 m0.rel
  intro hne
  have hT := hH.tab
  have hx := pairIdx_toNat ⟨mH, hH⟩ hinv.lCur
  by_cases hv : load32 H.arena (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2) +
      (x.lCur.toUSize <<< USize.ofNat 2)) (by rw [hx.1]; exact hx.2) hT.size32 = 4294967295
  · rw [ite_eq_left hv] at hne
    exact absurd rfl hne
  · rw [ite_eq_right hv]
    have hpvN : (load32 H.arena (USize.ofNat H.arena.size - (H.nL.toUSize <<< USize.ofNat 2) +
        (x.lCur.toUSize <<< USize.ofNat 2)) (by rw [hx.1]; exact hx.2) hT.size32).toNat =
        leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 := by
      rw [load32_toNat, hx.1]
    have hpv' : leAt H.arena (H.arena.size - 4 * H.nL.toNat + 4 * x.lCur.toNat) 4 ≠ 4294967295 := fun e =>
      hv (UInt64.toNat_inj.mp (by rw [hpvN, e]; rfl))
    obtain ⟨h1, _, h3⟩ := hT.pix _ hinv.lCur hpv'
    refine ⟨h1, fun j hj => ?_⟩
    rw [word_toUSize (by rw [hpvN]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), hpvN]
    exact h3 j hj

open Classical in
/-- The command loop with the fast loop gives what doesn't depend on the scratch record it runs in. -/
theorem runCmdKF_cell (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (N : Nat) (n : USize), n.toNat = N → ∀ (fresh : Bool) (c c' : RunOut) (word count : UInt64) (ring : ByteArray)
      (wpos pend cap written : USize) (p1 p2 : UInt8) (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize)
      (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos
        tag pos),
      runCmdKF H k a stop hs n fresh c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
          hinv =
        runCmdKF H k a stop hs n fresh c' word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
          hinv := by
  intro N
  induction N with
  | zero =>
    intro n hn fresh c c' word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv
    rw [runCmdKF, dite_eq_left (usize_zero hn)]
  | succ N ih =>
    intro n hn fresh c c' word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv
    have hn0 : n ≠ 0 := fun e => by
      rw [e, show (0 : USize).toNat = 0 from rfl] at hn
      omega
    have hnN : (n - USize.ofNat 1).toNat = N := by rw [usize_pred hn0]; omega
    rw [runCmdKF, dite_eq_right hn0]
    dsimp only
    by_cases hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
        (if tag = .literals then left else 0) ≤
          umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) ∧
        clen ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) -
          (if tag = .literals then left else 0)
    · rw [dite_eq_left hf, dite_eq_left hf]
      have hm : pos.toNat + 40 ≤ stop.toNat := by
        have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
        rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
        have := hinv.pos
        omega
      generalize fastEnter H k a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount
        flags ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩ tag (if tag = .literals then left else 0)
        (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)) pos hinv hm = r
      obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩, _, _, _,
        _⟩, _⟩ := r
      apply ih _ hnN
    · rw [dite_eq_right hf, dite_eq_right hf]
      have hc : Drops H k stop
          (fun c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
            runCmdKF H k a stop hs (n - USize.ofNat 1) true c word count ring wpos pend cap written p1 p2 remaining iCount
              lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
              wordBuf wordPos tag left pos h)
          (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
            if h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
                wordPos tag pos then
              runCmdKF H k a stop hs (n - USize.ofNat 1) true c word count ring wpos pend cap written p1 p2 remaining
                iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase
                dist wordBuf wordPos tag left pos h
            else mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
              lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) :=
        fun c1 word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h => by
          dsimp only
          rw [dite_eq_left h]
          apply ih _ hnN
      rw [kstep_eq (sp := pos) (ss := .next) (hcont := hc), kstep_eq (sp := pos) (ss := .next) (hcont := hc)]

/-! ### Induction over the command loop with the fast loop

A property of a run, with the fuel left and whether the fast loop may be entered, from a place, a record and a position
to a result, holds of `runCmdKF` if it holds where the fuel ends, goes back over a move of the fast loop (which leaves the
loop not fresh), holds of a step that stops, and goes back over a step that goes on. -/

open Classical in
theorem runCmdKF_rec {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (Q : Nat → Bool → Phase → Cmd → USize → Cmd → Prop)
    (hzero : ∀ fresh p st, Rel w k.toNat m st p → st.status = .next → st.pos.toNat ≤ stop.toNat →
      Q 0 fresh p st st.pos st)
    (hmove : ∀ N p st pos p' r R, Rel w k.toNat m st p → r.cap = st.cap →
      r.pend.toNat ≤ max st.pend.toNat (room k st.cap).toNat → MoveOk w k.toNat m K a stop p st pos p' r →
      Q N false p' r r.pos R → Q (N + 1) true p st pos R)
    (hstop : ∀ N fresh p st pos, Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (stepCmd H k a stop hs st pos).status ≠ .next → Q (N + 1) fresh p st pos (stepCmd H k a stop hs st pos))
    (hnext : ∀ N fresh p st pos R, Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (stepCmd H k a stop hs st pos).status = .next →
      (∀ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' →
        Q N true p' (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos R) → Q (N + 1) fresh p st pos R) :
    ∀ (N : Nat) (n : USize), n.toNat = N → ∀ (fresh : Bool) (cell : RunOut) (word count : UInt64) (ring : ByteArray)
      (wpos pend cap written : USize) (p1 p2 : UInt8) (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize)
      (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos
        tag pos) (p : Phase),
      Rel w k.toNat m (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
        lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) p →
      Q N fresh p (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
          lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) pos
        (runCmdKF H k a stop hs n fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
          flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left
          pos hinv) := by
  intro N
  induction N with
  | zero =>
    intro n hn fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv p hrel
    rw [runCmdKF, dite_eq_left (usize_zero hn)]
    exact hzero fresh p _ hrel rfl hinv.pos
  | succ N ih =>
    intro n hn fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv p hrel
    have hn0 : n ≠ 0 := fun e => by
      rw [e, show (0 : USize).toNat = 0 from rfl] at hn
      omega
    have hnN : (n - USize.ofNat 1).toNat = N := by rw [usize_pred hn0]; omega
    rw [runCmdKF, dite_eq_right hn0]
    dsimp only
    by_cases hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
        (if tag = .literals then left else 0) ≤
          umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) ∧
        clen ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) -
          (if tag = .literals then left else 0)
    · rw [dite_eq_left hf]
      have hm : pos.toNat + 40 ≤ stop.toNat := by
        have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
        rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
        have := hinv.pos
        omega
      obtain ⟨p', mv, fc, fp⟩ := fastEnter_ok (hs := hs) (cap := cap) (pend := pend) (p1 := p1) (p2 := p2)
        (remaining := remaining) (iCount := iCount) (lCount := lCount) (dCount := dCount) (flags := flags)
        (x := ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩) (left := left) hK hinv hm hH hrel hf.2.1 rfl rfl hf.2.2.2.1 hf.2.2.2.2
      generalize fastEnter H k a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount
        flags ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩ tag (if tag = .literals then left else 0)
        (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)) pos hinv hm = r
        at mv fc fp
      obtain ⟨⟨word', count', ring', wpos', pend', cap', written', q1, q2, remaining', iCount', lCount', dCount', flags',
        ⟨iCur', iPrev', lCur', lPrev', dCur', dPrev', e0, e1, e2, e3, code', ilen', clen', copyBits', copyBase', dist',
          wordBuf', wordPos'⟩, tag', left', pos', ss'⟩, h'⟩ := r
      have hR := mv.rel.mark pos' .next
      have hfr : fresh = true := hf.1
      subst hfr
      exact hmove N p _ pos p' (mkCmd word' count' ring' wpos' pend' cap' written' q1 q2 remaining' iCount' lCount'
          dCount' flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen' copyBits' copyBase' dist'
          wordBuf' wordPos' tag' left' pos' .next) _ hrel fc fp (mv.trans (MoveOk.same (st := mkCmd word' count' ring' wpos' pend' cap' written' q1 q2
          remaining' iCount' lCount' dCount' flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen'
          copyBits' copyBase' dist' wordBuf' wordPos' tag' left' pos' ss') hR rfl rfl rfl rfl mv.posStop))
        (ih _ hnN false cell word' count' ring' wpos' pend' cap' written' q1 q2 remaining' iCount' lCount' dCount' flags'
          iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen' copyBits' copyBase' dist' wordBuf'
          wordPos' tag' left' pos' h' p' hR)
    · rw [dite_eq_right hf]
      have hc : Drops H k stop
          (fun c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
            runCmdKF H k a stop hs (n - USize.ofNat 1) true c word count ring wpos pend cap written p1 p2 remaining iCount
              lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
              wordBuf wordPos tag left pos h)
          (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
            if h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
                wordPos tag pos then
              runCmdKF H k a stop hs (n - USize.ofNat 1) true cell word count ring wpos pend cap written p1 p2 remaining
                iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase
                dist wordBuf wordPos tag left pos h
            else mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
              lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) :=
        fun c1 word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h => by
          dsimp only
          rw [dite_eq_left h]
          apply runCmdKF_cell H k a stop hs _ _ rfl
      rw [kstep_eq (sp := pos) (ss := .next) (hcont := hc)]
      by_cases hst : (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          tag left pos .next) pos).status = .next
      · have hstep := stepCmd_ok (hs := hs) (K := commandsFrom w m) (a := a) (fun _ bs h0 => commandsFrom_step bs h0) hH
          hrel hinv.pos
        obtain ⟨_, _, _, h2, -⟩ := hstep.next hst
        refine hnext N fresh p _ pos _ hrel hinv.pos hst fun p' hR => ?_
        generalize stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
          flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag
          left pos .next) pos = r at hst h2 hR
        obtain ⟨word', count', ring', wpos', pend', cap', written', q1, q2, remaining', iCount', lCount', dCount', flags',
          ⟨iCur', iPrev', lCur', lPrev', dCur', dPrev', e0, e1, e2, e3, code', ilen', clen', copyBits', copyBase', dist',
            wordBuf', wordPos'⟩, tag', left', pos', ss'⟩ := r
        have hs' : ss' = .next := hst
        subst hs'
        have hI := KInv.of_rel hH hR h2
        unfold kcase
        dsimp only
        rw [ite_eq_left rfl, dite_eq_left hI]
        exact ih _ hnN true cell word' count' ring' wpos' pend' cap' written' q1 q2 remaining' iCount' lCount' dCount'
          flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen' copyBits' copyBase' dist' wordBuf'
          wordPos' tag' left' pos' hI p' hR
      · unfold kcase
        rw [ite_eq_right hst]
        exact hstop N fresh p _ pos hrel hinv.pos hst

/-- Induction over the command loop with the fast loop, from a record: as `runCmdKF_rec`, with the record taken to the
loop's fields first, the same place, bits and bytes waiting. -/
theorem runCmdF_rec {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (Q : Nat → Bool → Phase → Cmd → USize → Cmd → Prop)
    (hzero : ∀ fresh p st, Rel w k.toNat m st p → st.status = .next → st.pos.toNat ≤ stop.toNat →
      Q 0 fresh p st st.pos st)
    (hmove : ∀ N p st pos p' r R, Rel w k.toNat m st p → r.cap = st.cap →
      r.pend.toNat ≤ max st.pend.toNat (room k st.cap).toNat → MoveOk w k.toNat m K a stop p st pos p' r →
      Q N false p' r r.pos R → Q (N + 1) true p st pos R)
    (hstop : ∀ N fresh p st pos, Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (stepCmd H k a stop hs st pos).status ≠ .next → Q (N + 1) fresh p st pos (stepCmd H k a stop hs st pos))
    (hnext : ∀ N fresh p st pos R, Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      (stepCmd H k a stop hs st pos).status = .next →
      (∀ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' →
        Q N true p' (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos R) → Q (N + 1) fresh p st pos R)
    (hentry : ∀ N fresh p st pos r R, Rel w k.toNat m st p → MoveOk w k.toNat m K a stop p st pos p r →
      r.pend = st.pend → (∀ F, stateBits r a r.pos stop F = stateBits st a pos stop F) → r.cap = st.cap →
      Q N fresh p r r.pos R → Q N fresh p st pos R)
    (n : USize) {p : Phase} {st : Cmd} {pos : USize} (hrel : Rel w k.toNat m st p) (h : CmdInv H k stop st pos) :
    Q n.toNat true p st pos (runCmdF H k a stop hs n st pos h) := by
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, sp, ss⟩ := st
  have hR := hrel.mark pos .next
  exact hentry _ true p _ pos _ _ hrel (MoveOk.same (st := ⟨word, count, ring, wpos, pend, cap, written, p1, p2,
      remaining, iCount, lCount, dCount, flags, ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen,
        copyBits, copyBase, dist, wordBuf, wordPos⟩, tag, left, sp, ss⟩) hR rfl rfl rfl rfl h.pos) rfl (fun _ => rfl) rfl
    (runCmdKF_rec hK hH Q hzero hmove hstop hnext _ n rfl true _ word count ring wpos pend cap written p1 p2 remaining
      iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
      wordBuf wordPos tag left pos h p hR)

/-- The command loop with the fast loop, from a record, does what steps together must. -/
theorem runCmdF_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (n : USize) {p : Phase} {st : Cmd} {pos : USize} (hrel : Rel w k.toNat m st p) (h : CmdInv H k stop st pos) :
    RunOk w k.toNat m K a stop p st pos (runCmdF H k a stop hs n st pos h) :=
  runCmdF_rec hK hH (fun _ _ p st pos R => RunOk w k.toNat m K a stop p st pos R)
    (fun _ _ _ hrel hs hp => (MoveOk.refl hrel rfl hp).toRun hs)
    (fun _ _ _ _ _ _ _ _ _ _ mv h2 => mv.then h2)
    (fun _ _ _ _ _ hrel hp _ => (stepCmd_ok hK hH hrel hp).toRun)
    (fun _ _ _ _ _ _ hrel hp hst ih => by
      obtain ⟨p', hR, h1, h2, h3, _, h4, h5⟩ := (stepCmd_ok (hs := hs) hK hH hrel hp).next hst
      exact RunOk.trans h1 h3 h4 h5 (ih p' hR))
    (fun _ _ _ _ _ _ _ _ mv _ _ _ h2 => mv.then h2)
    n hrel h

/-- The command loop with the fast loop, when it rejects, decides at the last of its steps: from a place the reading in
order reaches, on the bits that step held and the bytes its refill took, whatever follows them. -/
theorem runCmdF_bad {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (n : USize) {p : Phase} {st : Cmd} {pos : USize} (hrel : Rel w k.toNat m st p) (h : CmdInv H k stop st pos) :
    (runCmdF H k a stop hs n st pos h).status = .bad →
      ∃ (p1 : Phase) (st1 : Cmd) (pos1 : USize), pos.toNat ≤ pos1.toNat ∧
        pos1.toNat ≤ (runCmdF H k a stop hs n st pos h).pos.toNat ∧
        (runCmdF H k a stop hs n st pos h).pos.toNat ≤ stop.toNat ∧
        8 * (runCmdF H k a stop hs n st pos h).pos.toNat + st1.count.toNat ≤ 8 * pos1.toNat + 64 ∧
        (∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p1 (stateBits st1 a pos1 stop F)) ∧
        ∀ F, rest w m K p1 (stateBits st1 a pos1 (runCmdF H k a stop hs n st pos h).pos F) = none :=
  have back : ∀ (p : Phase) (st : Cmd) (pos : USize) (p' : Phase) (r R : Cmd), MoveOk w k.toNat m K a stop p st pos p' r →
      (R.status = .bad → ∃ (p1 : Phase) (st1 : Cmd) (pos1 : USize), r.pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ R.pos.toNat ∧
        R.pos.toNat ≤ stop.toNat ∧ 8 * R.pos.toNat + st1.count.toNat ≤ 8 * pos1.toNat + 64 ∧
        (∀ F, Reach (cStep w m) p' (stateBits r a r.pos stop F) p1 (stateBits st1 a pos1 stop F)) ∧
        ∀ F, rest w m K p1 (stateBits st1 a pos1 R.pos F) = none) →
      (R.status = .bad → ∃ (p1 : Phase) (st1 : Cmd) (pos1 : USize), pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ R.pos.toNat ∧
        R.pos.toNat ≤ stop.toNat ∧ 8 * R.pos.toNat + st1.count.toNat ≤ 8 * pos1.toNat + 64 ∧
        (∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p1 (stateBits st1 a pos1 stop F)) ∧
        ∀ F, rest w m K p1 (stateBits st1 a pos1 R.pos F) = none) := fun _ _ _ _ _ _ mv ih hb => by
    obtain ⟨p1, st1, pos1, g1, g2, g3, g4, g5, g6⟩ := ih hb
    exact ⟨p1, st1, pos1, Nat.le_trans mv.posLe g1, g2, g3, g4, fun F => (mv.reach F).trans (g5 F), g6⟩
  runCmdF_rec hK hH (fun _ _ p st pos R => R.status = .bad →
      ∃ (p1 : Phase) (st1 : Cmd) (pos1 : USize), pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ R.pos.toNat ∧
        R.pos.toNat ≤ stop.toNat ∧ 8 * R.pos.toNat + st1.count.toNat ≤ 8 * pos1.toNat + 64 ∧
        (∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p1 (stateBits st1 a pos1 stop F)) ∧
        ∀ F, rest w m K p1 (stateBits st1 a pos1 R.pos F) = none)
    (fun _ _ _ _ hs _ hb => absurd (hs.symm.trans hb) (fun e => StepStatus.noConfusion e))
    (fun _ p st pos p' r R _ _ _ mv ih => back p st pos p' r R mv ih)
    (fun _ _ p st pos hrel hp _ hb => by
      obtain ⟨g1, g2, g3, g4⟩ := stepCmd_bad (hs := hs) hK hH hrel hp hb
      exact ⟨p, st, pos, Nat.le_refl _, g1, g2, g3, fun _ => .refl _ _, g4⟩)
    (fun _ _ _ _ _ _ hrel hp hst ih hb => by
      obtain ⟨p', hR, h1, _, _, _, _, h5⟩ := (stepCmd_ok (hs := hs) hK hH hrel hp).next hst
      obtain ⟨p1, st1, pos1, g1, g2, g3, g4, g5, g6⟩ := ih p' hR hb
      exact ⟨p1, st1, pos1, Nat.le_trans h1 g1, g2, g3, g4, fun F => (h5 F).trans (g5 F), g6⟩)
    (fun _ _ p st pos r R _ mv _ _ _ ih => back p st pos p r R mv ih)
    n hrel h

/-- The command loop with the fast loop, when it rejects, leaves the window and the bytes waiting of a state at a place. -/
theorem runCmdF_badWin {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (n : USize) {p : Phase} {st : Cmd} {pos : USize} (hrel : Rel w k.toNat m st p) (h : CmdInv H k stop st pos) :
    (runCmdF H k a stop hs n st pos h).status = .bad →
      ∃ (p1 : Phase) (st1 : Cmd), Rel w k.toNat m st1 p1 ∧ (runCmdF H k a stop hs n st pos h).WinSame st1 :=
  runCmdF_rec hK hH
    (fun _ _ _ _ _ R => R.status = .bad → ∃ (p1 : Phase) (st1 : Cmd), Rel w k.toNat m st1 p1 ∧ R.WinSame st1)
    (fun _ _ _ _ hs _ hb => absurd (hs.symm.trans hb) (fun e => StepStatus.noConfusion e))
    (fun _ _ _ _ _ _ _ _ _ _ _ ih hb => ih hb)
    (fun _ _ p st _ hrel _ _ hb => ⟨p, st, hrel, stepCmd_badWin hb⟩)
    (fun _ _ _ _ _ _ hrel hp hst ih hb => by
      obtain ⟨p', hR, -⟩ := (stepCmd_ok (hs := hs) hK hH hrel hp).next hst
      exact ih p' hR hb)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ ih hb => ih hb)
    n hrel h

end Brotli.Decoder
