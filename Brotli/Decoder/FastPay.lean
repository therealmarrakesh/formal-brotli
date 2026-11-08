module

public import Brotli.Decoder.FastWork

@[expose] public section

/-!
# The fast loop's work is paid for by the bytes it writes

`fastLoopW` against `fastLoop`, in lockstep: the two take the same branches, and their reads through `fillK`, `distK` and
`icK` pass the same values on (`fillK_rel`, `distK_rel`, `icFb_rel`). The bound (`fastLoop_work`, as `FW`): four for each
byte the loop writes, and two (one among a segment's literals) for the rounds that write nothing.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The loops' reads, in lockstep -/

theorem fillK_rel {α β : Type} {R : α → β → Prop} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {word count : UInt64} {pos : USize} {thr : UInt64} {hw hw' : (BitBuffer.mk word count).Wf} {ht ht' : thr.toNat ≤ 56}
    {hp hp' : pos.toNat ≤ stop.toNat} {hm hm' : count.toNat < thr.toNat → pos.toNat + 8 ≤ stop.toNat}
    {k1 : (w c : UInt64) → (p : USize) → FillOk a stop word count pos thr.toNat w c p → α}
    {k2 : (w c : UInt64) → (p : USize) → FillOk a stop word count pos thr.toNat w c p → β}
    (h : ∀ w c p hf, R (k1 w c p hf) (k2 w c p hf)) :
    R (fillK a stop hs word count pos thr hw ht hp hm k1) (fillK a stop hs word count pos thr hw' ht' hp' hm' k2) := by
  unfold fillK
  split
  · exact h _ _ _ _
  · exact h _ _ _ _

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow : USize}

theorem distK_rel {α β : Type} {R : α → β → Prop} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow)
    {np word count clen d01 d23 : UInt64} {hw hw' : (BitBuffer.mk word count).Wf}
    {k1 : (ok : Bool) → (w c dcode d : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α}
    {k2 : (ok : Bool) → (w c dcode d : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → β}
    (h : ∀ ok w c dcode d hk hk', R (k1 ok w c dcode d hk) (k2 ok w c dcode d hk')) :
    R (distK C np word count clen d01 d23 hw k1) (distK C np word count clen d01 d23 hw' k2) := by
  unfold distK
  dsimp only
  split <;> exact h _ _ _ _ _ _ _

theorem icFb_rel {α β : Type} {R : α → β → Prop} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow)
    {word count : UInt64} {hw hw' : (BitBuffer.mk word count).Wf}
    {k1 : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α}
    {k2 : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → β}
    (h : ∀ (v : UInt64) (hc : (wordSym v).toNat < 704) hk hk', v = lookupT T (icFbBase C) word C.icIn C.lim C.size32 →
      R (k1 (decide (wordBits v + rowBits (insertRow (wordSym v) hc) + rowBits (copyRow (wordSym v) hc) ≤ count))
          (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) >>> rowBits (copyRow (wordSym v) hc))
          (count - wordBits v - rowBits (insertRow (wordSym v) hc) - rowBits (copyRow (wordSym v) hc))
          (codeClass (wordSym v))
          (rowBase (insertRow (wordSym v) hc) +
            ((word >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc))))
          (rowBase (copyRow (wordSym v) hc) + (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
            maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc)))) hk)
        (k2 (decide (wordBits v + rowBits (insertRow (wordSym v) hc) + rowBits (copyRow (wordSym v) hc) ≤ count))
          (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) >>> rowBits (copyRow (wordSym v) hc))
          (count - wordBits v - rowBits (insertRow (wordSym v) hc) - rowBits (copyRow (wordSym v) hc))
          (codeClass (wordSym v))
          (rowBase (insertRow (wordSym v) hc) +
            ((word >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc))))
          (rowBase (copyRow (wordSym v) hc) + (((word >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
            maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc)))) hk')) :
    R (icFb C word count hw k1) (icFb C word count hw' k2) :=
  h _ (C.icSym word) _ _ rfl

end

/-! ### The fast loop's work -/

/-- What the fast loop's work is paid by: the bytes it writes, from the window position `opos` it is at to the one it
leaves at, `o`, four a byte, and two (one among a segment's literals) for the rounds that write nothing. -/
def FW (pB : USize) (bEnd : UInt64) (opos : USize) (m : UInt64) (r : Cmd) (wv : Nat) : Prop :=
  ∃ o : USize, r.pend = o + pB ∧ opos.toNat ≤ o.toNat ∧ o.toNat ≤ bEnd.toNat ∧
    wv + 4 * opos.toNat ≤ 4 * o.toNat + (if m = 0 then 2 else 1)

theorem FW.exit {pB : USize} {bEnd : UInt64} {opos : USize} {m : UInt64} {r : Cmd} (hp : r.pend = opos + pB)
    (hb : opos.toNat ≤ bEnd.toNat) : FW pB bEnd opos m r 1 :=
  ⟨opos, hp, Nat.le_refl _, hb, by split <;> omega⟩

/-- A round of literals, then the loop. -/
theorem FW.lit {pB : USize} {bEnd : UInt64} {opos opos' : USize} {m j : UInt64} {r : Cmd} {wv : Nat}
    (h : FW pB bEnd opos' (m - j) r wv) (ho : opos'.toNat = opos.toNat + j.toNat) (hj : 1 ≤ j.toNat)
    (hjm : j.toNat ≤ m.toNat) : FW pB bEnd opos m r (1 + wv) := by
  obtain ⟨o, h1, h2, h3, h4⟩ := h
  have hm : m ≠ 0 := fun e => by rw [e] at hjm; have : (0 : UInt64).toNat = 0 := rfl; omega
  refine ⟨o, h1, by omega, h3, ?_⟩
  rw [ite_eq_right hm]
  split at h4 <;> omega

/-- A segment's start, then the loop. -/
theorem FW.seg {pB : USize} {bEnd : UInt64} {opos : USize} {m' : UInt64} {r : Cmd} {wv : Nat}
    (h : FW pB bEnd opos m' r wv) (hm : m' ≠ 0) : FW pB bEnd opos 0 r (1 + wv) := by
  obtain ⟨o, h1, h2, h3, h4⟩ := h
  refine ⟨o, h1, h2, h3, ?_⟩
  rw [ite_eq_right hm] at h4
  rw [ite_eq_left rfl]
  omega

/-- A command's distance and copy, then the loop. -/
theorem FW.copy {pB : USize} {bEnd : UInt64} {opos opos' : USize} {c : Nat} {m : UInt64} {r : Cmd} {wv : Nat}
    (h : FW pB bEnd opos' 0 r wv) (ho : opos'.toNat = opos.toNat + c) (hc : 1 ≤ c) :
    FW pB bEnd opos m r (1 + c + wv) := by
  obtain ⟨o, h1, h2, h3, h4⟩ := h
  refine ⟨o, h1, by omega, h3, ?_⟩
  rw [ite_eq_left rfl] at h4
  split <;> omega

/-- A length's extra bits are below `2 ^ 24`. -/
theorem extra_lt {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow : USize}
    (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow) {x a b : UInt64} (ha : a.toNat < 64)
    (hb : b.toNat ≤ 24) : ((x >>> a) &&& maskT T C.big C.size32 b).toNat < 16777216 := by
  have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
  rw [C.maskT_eq (by omega), shr_mask_toNat _ _ _ ha (by omega)]
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (h24 ▸ Nat.pow_le_pow_right (by decide) hb)

/-- A command's distance and copy, then out of the loop. -/
theorem FW.copyExit {pB : USize} {bEnd : UInt64} {opos o : USize} {c : Nat} {m : UInt64} {r : Cmd}
    (hp : r.pend = o + pB) (ho : o.toNat = opos.toNat + c) (hb : o.toNat ≤ bEnd.toNat) :
    FW pB bEnd opos m r (1 + c) :=
  ⟨o, hp, by omega, hb, by split <;> omega⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The fast loop's work is paid for by the bytes it writes. -/
theorem fastLoop_work {H : Hdr} {kk : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {cap : USize}
    {T : ByteArray} {np : UInt64} {x : CmdExt} {flags : Flags} {mask size cap16 pB wB posLim : USize}
    {rEnd bEnd tb : UInt64} {modeOff lRow pairBase iRow iFb dRow : USize}
    {C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow} {X : XInv H x}
    {W : FWin H T kk mask size cap16 posLim stop pairBase np} :
    ∀ (I L : Nat) (word count : UInt64) (pos : USize) (ring : ByteArray) (opos : USize)
      (iCount lCount dCount d01 d23 code ilen clen lits m : UInt64) (p1 p2 : UInt8)
      (S : FSt kk stop posLim word count pos ring m), iCount.toNat = I → 17 * lits.toNat + m.toNat = L →
      FNum opos pB wB rEnd bEnd kk.toNat ((lits + m).toNat + clen.toNat) →
      lCount.toNat + m.toNat < 2 ^ 64 → lits.toNat + m.toNat < 2 ^ 30 → 1 ≤ clen.toNat →
      FW pB bEnd opos m (fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow
          pairBase iRow iFb dRow C X W word count pos ring opos iCount lCount dCount d01 d23 code ilen clen lits m p1 p2
          S).1
        (fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase iRow
          iFb dRow C X W word count pos ring opos iCount lCount dCount d01 d23 code ilen clen lits m p1 p2 S) := by
  intro I
  induction I using Nat.strongRecOn with
  | ind I ihI =>
  intro L
  induction L using Nat.strongRecOn with
  | ind L ih =>
    intro word count pos ring opos iCount lCount dCount d01 d23 code ilen clen lits m p1 p2 S hI hL N0 hLm hlm hcl
    rw [fastLoop, fastLoopW]
    dsimp only
    have hk := W.k24
    have hah := N0.ahead
    have hbe := N0.small
    by_cases hm0 : m ≠ 0
    · rw [dite_eq_left hm0, dite_eq_left hm0]
      have hm1 : 1 ≤ m.toNat := by
        have : m.toNat ≠ 0 := fun e => hm0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        omega
      have hLN : (lits + m).toNat = lits.toNat + m.toNat := u64_add_small (by omega)
      have next : ∀ (j : UInt64), 1 ≤ j.toNat → j.toNat ≤ m.toNat → ∀ (jU : USize), jU.toNat = j.toNat →
          ∀ (word' count' : UInt64) (pos' : USize) (ring' : ByteArray) (q1 q2 : UInt8)
          (S' : FSt kk stop posLim word' count' pos' ring' (m - j)),
          FW pB bEnd opos m (fastLoop H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff
              lRow pairBase iRow iFb dRow C X W word' count' pos' ring' (opos + jU) iCount lCount
              dCount d01 d23 code ilen clen lits (m - j) q1 q2 S').1
            (1 + fastLoopW H kk a stop hs cap T np x flags mask size cap16 pB wB posLim rEnd bEnd tb modeOff lRow pairBase
              iRow iFb dRow C X W word' count' pos' ring' (opos + jU) iCount lCount dCount d01 d23
              code ilen clen lits (m - j) q1 q2 S') := by
        intro j hj1 hjm jU hjU word' count' pos' ring' q1 q2 S'
        have hjN : (m - j).toNat = m.toNat - j.toNat := u64_sub_le hjm
        have hlN : (lits + (m - j)).toNat = lits.toNat + (m.toNat - j.toNat) := by
          rw [u64_add_small (by omega), hjN]
        refine FW.lit (ih _ (by rw [← hL, hjN]; omega) word' count' pos' ring' (opos + jU) iCount lCount dCount d01 d23
          code ilen clen lits (m - j) q1 q2 S' hI rfl (N0.adv hk (n := jU) (by omega) (by rw [hlN, hjU]; omega))
          (by rw [hjN]; omega) (by rw [hjN]; omega) hcl) ?_ hj1 hjm
        rw [fastAdd (by omega), hjU]
      by_cases hp : 2 ≤ m ∧ pairBase ≠ USize.ofNat 4294967295
      · rw [dite_eq_left hp, dite_eq_left hp]
        have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hp.1
        refine fillK_rel (R := fun r w => FW pB bEnd opos m (Subtype.val r) w) ?_
        intro word' count' pos' hf
        by_cases h2 : (row32 T pairBase (W.pair hp.2) C.size32 word' >>> 8) &&& 255 = 2
        · rw [ite_eq_left h2, ite_eq_left h2]
          exact next 2 (by decide) hm2 (USize.ofNat 2) (fastLit (by decide)) _ _ _ _ _ _ _
        · rw [ite_eq_right h2, ite_eq_right h2]
          exact next 1 (by decide) hm1 (USize.ofNat 1) (fastLit (by decide)) _ _ _ _ _ _ _
      · rw [dite_eq_right hp, dite_eq_right hp]
        by_cases hm2' : 2 ≤ m
        · rw [dite_eq_left hm2', dite_eq_left hm2']
          have hm2 : 2 ≤ m.toNat := UInt64.le_iff_toNat_le.mp hm2'
          refine fillK_rel (R := fun r w => FW pB bEnd opos m (Subtype.val r) w) ?_
          intro word' count' pos' hf
          exact next 2 (by decide) hm2 (USize.ofNat 2) (fastLit (by decide)) _ _ _ _ _ _ _
        · rw [dite_eq_right hm2', dite_eq_right hm2']
          refine fillK_rel (R := fun r w => FW pB bEnd opos m (Subtype.val r) w) ?_
          intro word' count' pos' hf
          exact next 1 (by decide) hm1 (USize.ofNat 1) (fastLit (by decide)) _ _ _ _ _ _ _
    rw [dite_eq_right hm0, dite_eq_right hm0]
    have hm : m = 0 := Decidable.of_not_not hm0
    subst hm
    by_cases hl : lits ≠ 0
    · rw [dite_eq_left hl, dite_eq_left hl]
      by_cases hcl' : lCount = 0 ∨ posLim < pos
      · rw [dite_eq_left hcl', dite_eq_left hcl']
        exact FW.exit rfl (Nat.le_trans (Nat.le_add_right _ _) N0.ahead)
      · rw [dite_eq_right hcl', dite_eq_right hcl']
        have hc0 : lCount ≠ 0 := fun h => hcl' (Or.inl h)
        have hlN : lits.toNat ≠ 0 := fun h => hl (UInt64.toNat_inj.mp h)
        have hcN : lCount.toNat ≠ 0 := fun h => hc0 (UInt64.toNat_inj.mp h)
        have hmv : (umin (umin lits lCount) 16).toNat = min (min lits.toNat lCount.toNat) 16 := by
          rw [umin_toNat, umin_toNat]
          rfl
        have e1 : (lCount - umin (umin lits lCount) 16).toNat = lCount.toNat - (umin (umin lits lCount) 16).toNat :=
          u64_sub_le (by omega)
        have e2 : (lits - umin (umin lits lCount) 16).toNat = lits.toNat - (umin (umin lits lCount) 16).toNat :=
          u64_sub_le (by omega)
        have hm' : umin (umin lits lCount) 16 ≠ 0 := fun h => by
          have := congrArg UInt64.toNat h
          rw [hmv] at this
          have : (0 : UInt64).toNat = 0 := rfl
          omega
        exact FW.seg (ih _ (by rw [← hL, e2]; have : (0 : UInt64).toNat = 0 := rfl; omega) word count pos ring opos
          iCount (lCount - umin (umin lits lCount) 16) dCount d01 d23 code ilen clen (lits - umin (umin lits lCount) 16)
          (umin (umin lits lCount) 16) (wget ring (opos - USize.ofNat 1) mask W.mask S.size)
          (wget ring (opos - USize.ofNat 2) mask W.mask S.size) _ hI rfl
          (by rw [UInt64.sub_add_cancel]; rw [UInt64.add_zero] at N0; exact N0)
          (by rw [e1]; have := lCount.toNat_lt; omega) (by rw [e2]; have : (0 : UInt64).toNat = 0 := rfl; omega) hcl) hm'
    · rw [dite_eq_right hl, dite_eq_right hl]
      have hl0 : lits = 0 := Decidable.of_not_not hl
      subst hl0
      rw [UInt64.add_zero] at N0
      by_cases hd2 : posLim < pos ∨ (128 ≤ code ∧ dCount = 0)
      · rw [dite_eq_left hd2, dite_eq_left hd2]
        exact FW.exit rfl (Nat.le_trans (Nat.le_add_right _ _) N0.ahead)
      · rw [dite_eq_right hd2, dite_eq_right hd2]
        refine fillK_rel (R := fun r w => FW pB bEnd opos 0 (Subtype.val r) w) ?_
        intro word1 count1 pos1 hf1
        refine distK_rel (R := fun r w => FW pB bEnd opos 0 (Subtype.val r) w) C ?_
        intro ok2 word2x count2x dcode dx hok2 hok2'
        have h0 : (0 : UInt64).toNat = 0 := rfl
        have N1 : FNum opos pB wB rEnd bEnd kk.toNat clen.toNat := by
          have := N0
          rwa [show (0 : UInt64).toNat + clen.toNat = clen.toNat from Nat.zero_add _] at this
        have hah1 := N1.ahead
        have hcU : clen.toUSize.toNat = clen.toNat := word_toUSize (by omega)
        have hoN : (opos + clen.toUSize).toNat = opos.toNat + clen.toNat := by
          rw [fastAdd (by omega), hcU]
        by_cases hbad : (¬ code < 128 ∧ ok2 = false) ∨ (if code < 128 then d01 &&& 0xFFFFFFFF else dx) = 0 ∨
            (usmin cap16 (opos + wB)).toUInt64 < (if code < 128 then d01 &&& 0xFFFFFFFF else dx)
        · rw [dite_eq_left hbad, dite_eq_left hbad]
          exact FW.exit rfl (Nat.le_trans (Nat.le_add_right _ _) N0.ahead)
        · rw [dite_eq_right hbad, dite_eq_right hbad]
          by_cases hi : iCount = 0
          · rw [dite_eq_left hi, dite_eq_left hi]
            exact FW.copyExit rfl hoN (by omega)
          · rw [dite_eq_right hi, dite_eq_right hi]
            refine fillK_rel (R := fun r w => FW pB bEnd opos 0 (Subtype.val r) w) ?_
            intro word3 count3 pos3 hf3
            rw [icK_fb, icK_fb]
            refine icFb_rel (R := fun r w => FW pB bEnd opos 0 (Subtype.val r) w) C ?_
            intro vi hcv hkv hkv' hvi
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
            · rw [dite_eq_left h1, dite_eq_left h1]
              exact FW.copyExit rfl hoN (by omega)
            · rw [dite_eq_right h1, dite_eq_right h1]
              have hadm := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp (fun h => h1 (Or.inr h)))
              rw [u64_add_small (by rw [u64_add_small (by omega), hoU]; omega), u64_add_small (by omega), hoU] at hadm
              have hc2 : 2 ≤ (rowBase (copyRow (wordSym vi) hcv)).toNat := by
                rw [(copyRow_fields hcv).2]; exact cmdRow_copy2 hcv
              have hcl2 : 1 ≤ (rowBase (copyRow (wordSym vi) hcv) +
                  (((word3 >>> wordBits vi) >>> rowBits (insertRow (wordSym vi) hcv))
                  &&& maskT T C.big C.size32 (rowBits (copyRow (wordSym vi) hcv)))).toNat := by
                have hx := extra_lt C (x := word3 >>> wordBits vi) (a := rowBits (insertRow (wordSym vi) hcv))
                  (b := rowBits (copyRow (wordSym vi) hcv)) (by have := insertRow_bits24 hcv; omega) (copyRow_bits hcv)
                have hb := (cmdRow_small hcv).2.2.2
                rw [← (copyRow_fields hcv).2] at hb
                rw [u64_add_small (by omega)]
                omega
              refine FW.copy (ihI _ (by rw [← hI]; exact icount_dec hi) _ _ _ pos3 _ (opos + clen.toUSize) (iCount - 1)
                lCount _ _ _ _ _ _ _ 0 _ _ _ rfl rfl (N0.adv hk (n := clen.toUSize) (by rw [hcU]; omega) (by rw [hcU, UInt64.add_zero]; omega))
                (by rw [h0]; have := lCount.toNat_lt; omega) (by rw [h0]; omega) hcl2) hoN hcl

end Brotli.Decoder
