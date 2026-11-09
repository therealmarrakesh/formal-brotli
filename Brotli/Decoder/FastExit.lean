module

public import Brotli.Decoder.FastProof

@[expose] public section

/-!
# Where the fast loop leaves

`FXit`: every state the fast loop leaves with is at an unmasked window position `o`, from where the loop was entered to
`bEnd`; its write position, bytes waiting, bytes written, cap and what remains of the meta-block are `fexit`'s at `o`,
and its two context bytes the window's two before `o` (`fastLoop_exit`, `fastEnter_exit`). The command loop that
carries only the bytes waiting (`LoopY.lean`) works out the window's fields from these.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- What a state the fast loop leaves with is, for a window position `o` from `lo` to `bEnd`, unmasked. -/
def FXit (mask pB cap cap16 wB : USize) (rEnd bEnd : UInt64) (lo : USize) (r : Cmd) : Prop :=
  ∃ o : USize, lo.toNat ≤ o.toNat ∧ o.toNat ≤ bEnd.toNat ∧ r.wpos = o &&& mask ∧ r.pend = o + pB ∧ r.cap = cap ∧
    r.written = usmin cap16 (o + wB) ∧ r.p1 = rbyte r.ring (o - USize.ofNat 1) mask ∧
    r.p2 = rbyte r.ring (o - USize.ofNat 2) mask ∧ r.remaining = rEnd - o.toUInt64

theorem FXit.mono {mask pB cap cap16 wB : USize} {rEnd bEnd : UInt64} {lo lo' : USize} {r : Cmd}
    (h : FXit mask pB cap cap16 wB rEnd bEnd lo' r) (hl : lo.toNat ≤ lo'.toNat) :
    FXit mask pB cap cap16 wB rEnd bEnd lo r :=
  let ⟨o, h1, h2⟩ := h
  ⟨o, Nat.le_trans hl h1, h2⟩

theorem fexitP_exit {H : Hdr} {T : ByteArray} {kk stop mask size cap16 posLim pairBase : USize} {np tb : UInt64}
    {x : CmdExt} {modeOff lRow iRow iFb dRow : USize} {C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow}
    {X : XInv H x} {W : FWin H T kk mask size cap16 posLim stop pairBase np} {word count : UInt64} {ring : ByteArray}
    {o pB cap wB : USize} {rEnd : UInt64} {iCount lCount dCount : UInt64} {flags : Flags} {d01 d23 code ilen clen : UInt64}
    {tag : Tag} {left : UInt64} {pos : USize} {hw : (BitBuffer.mk word count).Wf} {hp : pos.toNat ≤ stop.toNat}
    {hsz : ring.size = 2 ^ kk.toNat} {ht : tag = .literals ∨ tag = .distance ∨ tag = .command}
    {hm1 hm2 : mask.toNat = 2 ^ kk.toNat - 1} {hs1 hs2 : ring.size = 2 ^ kk.toNat} {lo : USize} {bEnd : UInt64}
    (h1 : lo.toNat ≤ o.toNat) (h2 : o.toNat ≤ bEnd.toNat) :
    FXit mask pB cap cap16 wB rEnd bEnd lo (fexitP C X W word count ring o pB cap wB rEnd iCount lCount dCount flags
      d01 d23 code ilen clen (wget ring (o - USize.ofNat 1) mask hm1 hs1) (wget ring (o - USize.ofNat 2) mask hm2 hs2)
      tag left pos hw hp hsz ht).1 :=
  ⟨o, h1, h2, rfl, rfl, rfl, rfl, wget_wbyte (hm := hm1) (hs := hs1), wget_wbyte (hm := hm2) (hs := hs2), rfl⟩

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow : USize}

theorem fillK_P {α : Type} {P : α → Prop} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {word count : UInt64} {pos : USize} {thr : UInt64} {hw : (BitBuffer.mk word count).Wf} {ht : thr.toNat ≤ 56}
    {hp : pos.toNat ≤ stop.toNat} {hm : count.toNat < thr.toNat → pos.toNat + 8 ≤ stop.toNat}
    {k : (w c : UInt64) → (p : USize) → FillOk a stop word count pos thr.toNat w c p → α}
    (h : ∀ w c p hf, P (k w c p hf)) : P (fillK a stop hs word count pos thr hw ht hp hm k) := by
  unfold fillK
  split
  · exact h _ _ _ _
  · exact h _ _ _ _

theorem distK_P {α : Type} {P : α → Prop} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow)
    {np word count clen d01 d23 : UInt64} {hw : (BitBuffer.mk word count).Wf}
    {k : (ok : Bool) → (w c dcode d : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α}
    (h : ∀ ok w c dcode d hk, P (k ok w c dcode d hk)) : P (distK C np word count clen d01 d23 hw k) := by
  unfold distK
  dsimp only
  split <;> exact h _ _ _ _ _ _

theorem icFb_P {α : Type} {P : α → Prop} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow)
    {word count : UInt64} {hw : (BitBuffer.mk word count).Wf}
    {k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α}
    (h : ∀ (v : UInt64) (hc : (wordSym v).toNat < 704) hk, v = lookupT T (icFbBase C) word C.icIn C.lim C.size32 →
      P (k (decide (wordBits v + rowBits (insertRow (wordSym v) hc) + rowBits (copyRow (wordSym v) hc) ≤ count))
          (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) >>> rowBits (copyRow (wordSym v) hc))
          (count - wordBits v - rowBits (insertRow (wordSym v) hc) - rowBits (copyRow (wordSym v) hc))
          (codeClass (wordSym v))
          (rowBase (insertRow (wordSym v) hc) +
            ((word >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc))))
          (rowBase (copyRow (wordSym v) hc) + (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
            maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc)))) hk)) :
    P (icFb C word count hw k) :=
  h _ (C.icSym word) _ rfl

end

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- Every state the fast loop leaves with is at a window position from where it was to `bEnd`, with `fexit`'s fields
there and the window's context bytes. -/
theorem fastLoop_exit {H : Hdr} {kk : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {cap : USize}
    {T : ByteArray} {np : UInt64} {x : CmdExt} {flags : Flags} {mask size cap16 pB wB posLim : USize}
    {rEnd bEnd tb : UInt64} {modeOff lRow pairBase iRow iFb dRow : USize}
    {C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow} {X : XInv H x}
    {W : FWin H T kk mask size cap16 posLim stop pairBase np} :
    ∀ (I L : Nat) (word count : UInt64) (pos : USize) (ring : ByteArray) (opos : USize)
      (iCount lCount dCount d01 d23 code ilen clen lits m : UInt64) (p1 p2 : UInt8)
      (S : FSt kk stop posLim word count pos ring m), iCount.toNat = I → 17 * lits.toNat + m.toNat = L →
      opos.toNat + ((lits + m).toNat + clen.toNat) ≤ bEnd.toNat → bEnd.toNat < 2 ^ 30 →
      lits.toNat + m.toNat < 2 ^ 30 →
      FXit mask pB cap cap16 wB rEnd bEnd opos (fastLoop H kk a stop hs cap (fun _ => false) T np x flags mask size
          cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb dRow C X W word count pos ring opos iCount
          lCount dCount d01 d23 code ilen clen lits m p1 p2 S).1 := by
  intro I
  induction I using Nat.strongRecOn with
  | ind I ihI =>
  intro L
  induction L using Nat.strongRecOn with
  | ind L ih =>
    intro word count pos ring opos iCount lCount dCount d01 d23 code ilen clen lits m p1 p2 S hI hL hA hB hlm
    rw [fastLoop]
    dsimp only
    have hk := W.k24
    by_cases hm0 : m ≠ 0
    · rw [dite_eq_left hm0]
      have hm1 : 1 ≤ m.toNat := by
        have : m.toNat ≠ 0 := fun e => hm0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        omega
      have hLN : (lits + m).toNat = lits.toNat + m.toNat := u64_add_small (by omega)
      have next : ∀ (j : UInt64), 1 ≤ j.toNat → j.toNat ≤ m.toNat → ∀ (jU : USize), jU.toNat = j.toNat →
          ∀ (word' count' : UInt64) (pos' : USize) (ring' : ByteArray) (q1 q2 : UInt8)
          (S' : FSt kk stop posLim word' count' pos' ring' (m - j)),
          FXit mask pB cap cap16 wB rEnd bEnd opos (fastLoop H kk a stop hs cap (fun _ => false) T np x flags mask size
              cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow iFb dRow C X W word' count' pos' ring'
              (opos + jU) iCount lCount dCount d01 d23 code ilen clen lits (m - j) q1 q2 S').1 := by
        intro j hj1 hjm jU hjU word' count' pos' ring' q1 q2 S'
        have hjN : (m - j).toNat = m.toNat - j.toNat := u64_sub_le hjm
        have hlN : (lits + (m - j)).toNat = lits.toNat + (m.toNat - j.toNat) := by
          rw [u64_add_small (by omega), hjN]
        have ho : (opos + jU).toNat = opos.toNat + j.toNat := by rw [fastAdd (by omega), hjU]
        refine (ih _ (by rw [← hL, hjN]; omega) word' count' pos' ring' (opos + jU) iCount lCount dCount d01 d23
          code ilen clen lits (m - j) q1 q2 S' hI rfl (by rw [ho, hlN]; omega) hB (by rw [hjN]; omega)).mono ?_
        rw [ho]
        omega
      by_cases hp : 2 ≤ m ∧ pairBase ≠ USize.ofNat 4294967295
      · rw [dite_eq_left hp]
        have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hp.1
        refine fillK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) ?_
        intro word' count' pos' hf
        by_cases h2 : (row32 T pairBase (W.pair hp.2) C.size32 word' >>> 8) &&& 255 = 2
        · rw [ite_eq_left h2]
          exact next 2 (by decide) hm2 (USize.ofNat 2) (fastLit (by decide)) _ _ _ _ _ _ _
        · rw [ite_eq_right h2]
          exact next 1 (by decide) hm1 (USize.ofNat 1) (fastLit (by decide)) _ _ _ _ _ _ _
      · rw [dite_eq_right hp]
        by_cases hm2' : 2 ≤ m
        · rw [dite_eq_left hm2']
          have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hm2'
          refine fillK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) ?_
          intro word' count' pos' hf
          exact next 2 (by decide) hm2 (USize.ofNat 2) (fastLit (by decide)) _ _ _ _ _ _ _
        · rw [dite_eq_right hm2']
          refine fillK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) ?_
          intro word' count' pos' hf
          exact next 1 (by decide) hm1 (USize.ofNat 1) (fastLit (by decide)) _ _ _ _ _ _ _
    rw [dite_eq_right hm0]
    have hm : m = 0 := Decidable.of_not_not hm0
    subst hm
    have h0 : (0 : UInt64).toNat = 0 := rfl
    by_cases hl : lits ≠ 0
    · rw [dite_eq_left hl]
      by_cases hcl' : lCount = 0 ∨ posLim < pos
      · rw [dite_eq_left hcl']
        exact fexitP_exit (Nat.le_refl _) (by omega)
      · rw [dite_eq_right hcl']
        have hc0 : lCount ≠ 0 := fun h => hcl' (Or.inl h)
        have hlN : lits.toNat ≠ 0 := fun h => hl (UInt64.toNat_inj.mp h)
        have hcN : lCount.toNat ≠ 0 := fun h => hc0 (UInt64.toNat_inj.mp h)
        have hmv : (umin (umin lits lCount) 16).toNat = min (min lits.toNat lCount.toNat) 16 := by
          rw [umin_toNat, umin_toNat]
          rfl
        have e2 : (lits - umin (umin lits lCount) 16).toNat = lits.toNat - (umin (umin lits lCount) 16).toNat :=
          u64_sub_le (by omega)
        rw [UInt64.add_zero] at hA
        exact ih _ (by rw [← hL, e2]; omega) word count pos ring opos iCount (lCount - umin (umin lits lCount) 16) dCount
          d01 d23 code ilen clen (lits - umin (umin lits lCount) 16) (umin (umin lits lCount) 16)
          (wget ring (opos - USize.ofNat 1) mask W.mask S.size) (wget ring (opos - USize.ofNat 2) mask W.mask S.size) _
          hI rfl (by rw [UInt64.sub_add_cancel]; exact hA) hB (by rw [e2]; omega)
    · rw [dite_eq_right hl]
      have hl0 : lits = 0 := Decidable.of_not_not hl
      subst hl0
      rw [UInt64.add_zero] at hA
      by_cases hd2 : posLim < pos ∨ (128 ≤ code ∧ dCount = 0)
      · rw [dite_eq_left hd2]
        exact fexitP_exit (Nat.le_refl _) (by omega)
      · rw [dite_eq_right hd2]
        refine fillK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) ?_
        intro word1 count1 pos1 hf1
        rw [dite_eq_right (show ¬ (false = true) from Bool.false_ne_true)]
        refine distK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) C ?_
        intro ok2 word2x count2x dcode dx hok2
        have hcU : clen.toUSize.toNat = clen.toNat := word_toUSize (by omega)
        have hoN : (opos + clen.toUSize).toNat = opos.toNat + clen.toNat := by
          rw [fastAdd (by omega), hcU]
        by_cases hbad : (¬ code < 128 ∧ ok2 = false) ∨ (if code < 128 then d01 &&& 0xFFFFFFFF else dx) = 0 ∨
            (usmin cap16 (opos + wB)).toUInt64 < (if code < 128 then d01 &&& 0xFFFFFFFF else dx)
        · rw [dite_eq_left hbad]
          exact fexitP_exit (Nat.le_refl _) (by omega)
        · rw [dite_eq_right hbad]
          by_cases hi : iCount = 0
          · rw [dite_eq_left hi]
            exact fexitP_exit (by omega) (by omega)
          · rw [dite_eq_right hi]
            refine fillK_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) ?_
            intro word3 count3 pos3 hf3
            rw [icK_fb]
            refine icFb_P (P := fun r => FXit mask pB cap cap16 wB rEnd bEnd opos (Subtype.val r)) C ?_
            intro vi hcv hkv hvi
            have hIL := len_bound C (x := word3) (a := wordBits vi) (b := rowBits (insertRow (wordSym vi) hcv))
              (base := rowBase (insertRow (wordSym vi) hcv))
              (by have := and15_lt vi; exact Nat.lt_trans this (by decide))
              (insertRow_bits24 hcv) (by rw [(insertRow_fields hcv).2]; exact (cmdRow_small hcv).2.1)
            have hCL := len_bound C (x := word3 >>> wordBits vi) (a := rowBits (insertRow (wordSym vi) hcv))
              (b := rowBits (copyRow (wordSym vi) hcv)) (base := rowBase (copyRow (wordSym vi) hcv))
              (by have := insertRow_bits24 hcv; omega) (copyRow_bits hcv)
              (by rw [(copyRow_fields hcv).2]; have := (cmdRow_small hcv).2.2.2; omega)
            have hoU : (opos + clen.toUSize).toUInt64.toNat = opos.toNat + clen.toNat := by
              rw [USize.toNat_toUInt64, hoN]
            by_cases h1 : decide (wordBits vi + rowBits (insertRow (wordSym vi) hcv) +
                rowBits (copyRow (wordSym vi) hcv) ≤ count3) = false ∨ bEnd < (opos + clen.toUSize).toUInt64 +
                (rowBase (insertRow (wordSym vi) hcv) +
                  ((word3 >>> wordBits vi) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym vi) hcv)))) +
                (rowBase (copyRow (wordSym vi) hcv) +
                  (((word3 >>> wordBits vi) >>> rowBits (insertRow (wordSym vi) hcv))
                  &&& maskT T C.big C.size32 (rowBits (copyRow (wordSym vi) hcv))))
            · rw [dite_eq_left h1]
              exact fexitP_exit (by omega) (by omega)
            · rw [dite_eq_right h1]
              have hadm := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp (fun h => h1 (Or.inr h)))
              rw [u64_add_small (by rw [u64_add_small (by omega), hoU]; omega), u64_add_small (by omega), hoU] at hadm
              refine (ihI _ (by rw [← hI]; exact icount_dec hi) _ _ _ pos3 _ (opos + clen.toUSize) (iCount - 1)
                lCount _ _ _ _ _ _ _ 0 _ _ _ rfl rfl (by rw [hoN, UInt64.add_zero]; omega) hB
                (by rw [h0]; omega)).mono (by omega)

/-- Every state the fast loop leaves with, from the step machine's state, is at a window position from `wpos` to
`bEnd`. -/
theorem fastEnter_exit {H : Hdr} {kk : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {cap : USize}
    {word count : UInt64} {ring : ByteArray} {wpos pend written : USize} {p1 p2 : UInt8}
    {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag} {lits bEnd : UInt64}
    {pos : USize} {hinv : KInv H kk stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev
      x.copyBits x.dist x.wordBuf x.wordPos tag pos} {hm : pos.toNat + 40 ≤ stop.toNat}
    (hA : wpos.toNat + (lits.toNat + x.clen.toNat) ≤ bEnd.toNat) (hB : bEnd.toNat < 2 ^ 30) :
    FXit (ringMask kk) (pend - wpos) cap (ringSize kk - USize.ofNat 16) (written - wpos) (remaining + wpos.toUInt64)
      bEnd wpos (fastEnter H kk a stop hs cap word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags
        x tag lits bEnd pos hinv hm).1 := by
  unfold fastEnter
  rw [fastLoopS_eq]
  unfold fastLoopF
  exact fastLoop_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl (by rw [UInt64.add_zero]; exact hA) hB
    (by have : (0 : UInt64).toNat = 0 := rfl; omega)

/-- A state the fast loop leaves with, entered from the window's fields the bytes waiting stand for, has such fields:
it is at `o`, so its bytes waiting stand for `o` plus what the step machine's position was past its window position. -/
theorem win_fast {k cap pB pend : USize} {remaining bEnd : UInt64} {r : Cmd} (hk : k.toNat ≤ 24)
    (h16 : 16 ≤ 2 ^ k.toNat) (hJ : (pend - pB).toNat ≤ 2 ^ 25 + pend.toNat) (h2 : 2 ≤ (yWr k pB pend).toNat)
    (hbe : bEnd.toNat ≤ (yWpos k pB pend).toNat +
      (if room k cap ≤ pend then 0 else (room k cap).toNat - pend.toNat))
    (hX : FXit (ringMask k) (pend - yWpos k pB pend) cap (ringSize k - USize.ofNat 16) (yWr k pB pend - yWpos k pB pend)
      (remaining + (yWpos k pB pend).toUInt64) bEnd (yWpos k pB pend) r) :
    WinY k cap pB r.ring r.wpos r.pend r.cap r.written r.p1 r.p2 := by
  obtain ⟨o, ho1, ho2, ew, ep, ec, ewr, e1, e2, -⟩ := hX
  have hmk := ringMask_toNat hk
  have hR := room_le16 (cap := cap) hk h16
  have h24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hc := cap16_toNat hk h16
  unfold WinY
  simp only [yWpos, yWr] at h2 hbe ho1 ewr ep ⊢
  obtain ⟨O, hO⟩ : ∃ O, pend - pB = O := ⟨_, rfl⟩
  rw [hO] at h2 hbe ho1 ewr ep hJ
  have hw0 : (O &&& ringMask k).toNat ≤ O.toNat := by rw [umask_mod hmk]; exact Nat.mod_le _ _
  have hw0' : (O &&& ringMask k).toNat < 2 ^ k.toNat := mask_lt hmk
  have hm2 := usmin_toNat (ringSize k - USize.ofNat 16) O
  have G1 : r.pend - pB = o + (O - (O &&& ringMask k)) := by
    rw [ep, ← hO]
    simp only [USize.sub_eq_add_neg]
    ac_rfl
  have G2 : o + (O - (O &&& ringMask k)) = O + (o - (O &&& ringMask k)) := by
    simp only [USize.sub_eq_add_neg]
    ac_rfl
  have G3 : r.pend = pend + (o - (O &&& ringMask k)) := by
    rw [ep]
    simp only [USize.sub_eq_add_neg]
    ac_rfl
  have hδ : (o - (O &&& ringMask k)).toNat = o.toNat - (O &&& ringMask k).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr ho1)
  have hδb : o.toNat - (O &&& ringMask k).toNat ≤ 2 ^ 24 := by split at hbe <;> omega
  -- the sums, as numbers: nothing wraps, since the loop wrote only while the room was ahead of `pend`
  have QP : (O + (o - (O &&& ringMask k))).toNat = O.toNat + (o.toNat - (O &&& ringMask k).toNat) ∧
      (pend + (o - (O &&& ringMask k))).toNat = pend.toNat + (o.toNat - (O &&& ringMask k).toNat) := by
    by_cases hz : o.toNat - (O &&& ringMask k).toNat = 0
    · have e0 : o - (O &&& ringMask k) = 0 := usize_zero (by rw [hδ]; exact hz)
      rw [e0, USize.add_zero, USize.add_zero, hz]
      exact ⟨rfl, rfl⟩
    · have hrp : ¬ room k cap ≤ pend := fun h => by rw [ite_eq_left h] at hbe; omega
      rw [ite_eq_right hrp] at hbe
      have hp := room_lt hrp
      exact ⟨by rw [fastAdd (by rw [hδ]; omega), hδ], by rw [fastAdd (by rw [hδ]; omega), hδ]⟩
  obtain ⟨Q, P⟩ := QP
  have hO2 : 2 ≤ O.toNat := by rw [hm2] at h2; omega
  have W1 : (o + (usmin (ringSize k - USize.ofNat 16) O - (O &&& ringMask k))).toNat =
      min (ringSize k - USize.ofNat 16).toNat O.toNat + (o.toNat - (O &&& ringMask k).toNat) := by
    rw [show o + (usmin (ringSize k - USize.ofNat 16) O - (O &&& ringMask k)) =
        usmin (ringSize k - USize.ofNat 16) O + (o - (O &&& ringMask k)) by simp only [USize.sub_eq_add_neg]; ac_rfl,
      fastAdd (by rw [hm2, hδ, hc]; omega), hm2, hδ]
  have hback : ∀ j : USize, j.toNat ≤ 2 → 1 ≤ j.toNat →
      rbyte r.ring (o - j) (ringMask k) = backB r.ring (ringMask k) (r.pend - pB) j := by
    intro j hj1 hj2
    unfold backB
    rw [ite_eq_left (USize.le_iff_toNat_le.mpr (by rw [G1, G2, Q]; omega))]
    apply rbyte_congr
    rw [G1, show o + (O - (O &&& ringMask k)) - j = o - j + (O - (O &&& ringMask k)) by
      simp only [USize.sub_eq_add_neg]; ac_rfl, mask_add_hi hk hmk]
  refine ⟨ec.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ew, G1, mask_add_hi hk hmk]
  · apply USize.toNat_inj.mp
    rw [ewr, usmin_toNat, usmin_toNat, W1, G1, G2, Q, hc]
    omega
  · rw [e1]
    exact hback _ (by rw [one_toNat']; omega) (by rw [one_toNat']; omega)
  · rw [e2]
    exact hback _ (by rw [two_toNat']; omega) (by rw [two_toNat']; omega)
  · rw [G1, G2, Q, G3, P]
    omega

end Brotli.Decoder
