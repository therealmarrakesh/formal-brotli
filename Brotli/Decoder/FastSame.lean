module

public import Brotli.Decoder.FastPay

@[expose] public section

/-!
# The fast loop depends only on the unread bytes

Two runs of the fast loop on chunks with the same unread bytes, from the same state but for the position, take the same
branches (the margin's test agrees, `lim_iff`) and read the same bits (`fillK_same`, from `fill_same`), so they leave
with the same state but for the position, at positions with the same unread bytes (`fastLoop_same`, `fastEnter_same`).
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- `fillK` over two chunks with the same unread bytes passes the same buffer, and positions with the same unread bytes,
on. -/
theorem fillK_same {α β : Type} {R : α → β → Prop} {a1 a2 : ByteArray} {e1 e2 : USize} {hs1 : e1.toNat ≤ a1.size}
    {hs2 : e2.toNat ≤ a2.size} {word count : UInt64} {p1 p2 : USize} {thr : UInt64}
    {hw1 hw2 : (BitBuffer.mk word count).Wf} {ht1 ht2 : thr.toNat ≤ 56}
    {hp1 : p1.toNat ≤ e1.toNat} {hp2 : p2.toNat ≤ e2.toNat}
    {hm1 : count.toNat < thr.toNat → p1.toNat + 8 ≤ e1.toNat} {hm2 : count.toNat < thr.toNat → p2.toNat + 8 ≤ e2.toNat}
    {k1 : (w c : UInt64) → (p : USize) → FillOk a1 e1 word count p1 thr.toNat w c p → α}
    {k2 : (w c : UInt64) → (p : USize) → FillOk a2 e2 word count p2 thr.toNat w c p → β}
    (h : Same a1 e1 a2 e2 p1 p2)
    (hk : ∀ w1 c1 q1 hf1 w2 c2 q2 hf2, w1 = w2 → c1 = c2 → Same a1 e1 a2 e2 q1 q2 → R (k1 w1 c1 q1 hf1) (k2 w2 c2 q2 hf2)) :
    R (fillK a1 e1 hs1 word count p1 thr hw1 ht1 hp1 hm1 k1) (fillK a2 e2 hs2 word count p2 thr hw2 ht2 hp2 hm2 k2) := by
  unfold fillK
  by_cases hc : count < thr
  · rw [dite_eq_left hc, dite_eq_left hc]
    have hm := hm1 (UInt64.lt_iff_toNat_lt.mp hc)
    obtain ⟨e, hS⟩ := fill_same (b := ⟨word, count⟩) h hm hw1.count_le (by omega)
      (by have := e1.toNat_lt_size; omega) (by have := hm2 (UInt64.lt_iff_toNat_lt.mp hc); omega)
      (by have := hm2 (UInt64.lt_iff_toNat_lt.mp hc); have := e2.toNat_lt_size; omega)
    exact hk _ _ _ _ _ _ _ _ (congrArg BitBuffer.word e) (congrArg BitBuffer.count e) hS
  · rw [dite_eq_right hc, dite_eq_right hc]
    exact hk _ _ _ _ _ _ _ _ rfl rfl h

/-- Two command loop states the same but for their positions, which have the same unread bytes. -/
def FSame (a1 : ByteArray) (e1 : USize) (a2 : ByteArray) (e2 : USize) (r1 r2 : Cmd) : Prop :=
  { r1 with pos := 0 } = { r2 with pos := 0 } ∧ Same a1 e1 a2 e2 r1.pos r2.pos

/-- The margin's test agrees on positions with the same unread bytes. -/
theorem lim_iff {a1 a2 : ByteArray} {e1 e2 l1 l2 p1 p2 : USize} (h1 : l1.toNat + 40 = e1.toNat)
    (h2 : l2.toNat + 40 = e2.toNat) (h : Same a1 e1 a2 e2 p1 p2) : l1 < p1 ↔ l2 < p2 := by
  obtain ⟨_, _, h3, h4, h5, _⟩ := h
  rw [USize.lt_iff_toNat_lt, USize.lt_iff_toNat_lt]
  omega

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The fast loop depends only on the unread bytes. -/
theorem fastLoop_same {H : Hdr} {kk : USize} {a1 a2 : ByteArray} {e1 e2 : USize} {hs1 : e1.toNat ≤ a1.size}
    {hs2 : e2.toNat ≤ a2.size} {cap : USize} {T : ByteArray} {np : UInt64} {x : CmdExt} {flags : Flags}
    {mask size cap16 pB wB l1 l2 : USize} {rEnd bEnd tb : UInt64} {modeOff lRow pairBase iRow iFb dRow : USize}
    {C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow} {X : XInv H x}
    {W1 : FWin H T kk mask size cap16 l1 e1 pairBase np} {W2 : FWin H T kk mask size cap16 l2 e2 pairBase np} :
    ∀ (I L : Nat) (word count : UInt64) (p1 p2 : USize) (ring : ByteArray) (opos : USize)
      (iCount lCount dCount d01 d23 code ilen clen lits m : UInt64) (b1 b2 : UInt8)
      (S1 : FSt kk e1 l1 word count p1 ring m) (S2 : FSt kk e2 l2 word count p2 ring m),
      iCount.toNat = I → 17 * lits.toNat + m.toNat = L → Same a1 e1 a2 e2 p1 p2 →
      FSame a1 e1 a2 e2
        (fastLoop H kk a1 e1 hs1 cap T np x flags mask size cap16 pB wB l1 rEnd bEnd tb modeOff lRow pairBase iRow iFb
          dRow C X W1 word count p1 ring opos iCount lCount dCount d01 d23 code ilen clen lits m b1 b2 S1).1
        (fastLoop H kk a2 e2 hs2 cap T np x flags mask size cap16 pB wB l2 rEnd bEnd tb modeOff lRow pairBase iRow iFb
          dRow C X W2 word count p2 ring opos iCount lCount dCount d01 d23 code ilen clen lits m b1 b2 S2).1 := by
  intro I
  induction I using Nat.strongRecOn with
  | ind I ihI =>
  intro L
  induction L using Nat.strongRecOn with
  | ind L ih =>
    intro word count p1 p2 ring opos iCount lCount dCount d01 d23 code ilen clen lits m b1 b2 S1 S2 hI hL h
    rw [fastLoop, fastLoop]
    dsimp only
    have hlim := lim_iff W1.lim W2.lim h
    by_cases hm0 : m ≠ 0
    · rw [dite_eq_left hm0, dite_eq_left hm0]
      by_cases hp : 2 ≤ m ∧ pairBase ≠ USize.ofNat 4294967295
      · rw [dite_eq_left hp, dite_eq_left hp]
        refine fillK_same (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) h ?_
        intro w1 c1 q1 hf1 w2 c2 q2 hf2 ew ec hS
        subst ew ec
        by_cases h2 : (row32 T pairBase (W1.pair hp.2) C.size32 w1 >>> 8) &&& 255 = 2
        · rw [ite_eq_left h2, ite_eq_left h2]
          exact ih _ (by rw [← hL]; exact lit_dec2 _ hp.1) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI rfl hS
        · rw [ite_eq_right h2, ite_eq_right h2]
          exact ih _ (by rw [← hL]; exact lit_dec1 _ hm0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI rfl hS
      · rw [dite_eq_right hp, dite_eq_right hp]
        by_cases hm2' : 2 ≤ m
        · rw [dite_eq_left hm2', dite_eq_left hm2']
          refine fillK_same (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) h ?_
          intro w1 c1 q1 hf1 w2 c2 q2 hf2 ew ec hS
          subst ew ec
          exact ih _ (by rw [← hL]; exact lit_dec2 _ hm2') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI rfl hS
        · rw [dite_eq_right hm2', dite_eq_right hm2']
          refine fillK_same (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) h ?_
          intro w1 c1 q1 hf1 w2 c2 q2 hf2 ew ec hS
          subst ew ec
          exact ih _ (by rw [← hL]; exact lit_dec1 _ hm0) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI rfl hS
    rw [dite_eq_right hm0, dite_eq_right hm0]
    by_cases hl : lits ≠ 0
    · rw [dite_eq_left hl, dite_eq_left hl]
      by_cases hcl : lCount = 0 ∨ l1 < p1
      · have hcl2 : lCount = 0 ∨ l2 < p2 := hcl.imp id hlim.mp
        rw [dite_eq_left hcl, dite_eq_left hcl2]
        exact ⟨rfl, h⟩
      · have hcl2 : ¬ (lCount = 0 ∨ l2 < p2) := fun e => hcl (e.imp id hlim.mpr)
        rw [dite_eq_right hcl, dite_eq_right hcl2]
        exact ih _ (by
            rw [← hL]
            exact seg_dec (by rw [Decidable.of_not_not hm0]; rfl) (fun e => hl (UInt64.toNat_inj.mp (by rw [e]; rfl)))
              (fun e => hcl (Or.inl (UInt64.toNat_inj.mp (by rw [e]; rfl)))))
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hI rfl h
    · rw [dite_eq_right hl, dite_eq_right hl]
      by_cases hd2 : l1 < p1 ∨ (128 ≤ code ∧ dCount = 0)
      · have hd2' : l2 < p2 ∨ (128 ≤ code ∧ dCount = 0) := hd2.imp hlim.mp id
        rw [dite_eq_left hd2, dite_eq_left hd2']
        exact ⟨rfl, h⟩
      · have hd2' : ¬ (l2 < p2 ∨ (128 ≤ code ∧ dCount = 0)) := fun e => hd2 (e.imp hlim.mpr id)
        rw [dite_eq_right hd2, dite_eq_right hd2']
        refine fillK_same (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) h ?_
        intro w1 c1 q1 hf1 w2 c2 q2 hf2 ew ec hS
        subst ew ec
        refine distK_rel (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) C ?_
        intro ok2 word2x count2x dcode dx hok2 hok2'
        by_cases hbad : (¬ code < 128 ∧ ok2 = false) ∨ (if code < 128 then d01 &&& 0xFFFFFFFF else dx) = 0 ∨
            (usmin cap16 (opos + wB)).toUInt64 < (if code < 128 then d01 &&& 0xFFFFFFFF else dx)
        · rw [dite_eq_left hbad, dite_eq_left hbad]
          exact ⟨rfl, h⟩
        · rw [dite_eq_right hbad, dite_eq_right hbad]
          by_cases hi : iCount = 0
          · rw [dite_eq_left hi, dite_eq_left hi]
            exact ⟨rfl, hS⟩
          · rw [dite_eq_right hi, dite_eq_right hi]
            refine fillK_same (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) hS ?_
            intro w3 c3 r3 hf3 w3' c3' r3' hf3' ew' ec' hS'
            subst ew' ec'
            rw [icK_fb, icK_fb]
            refine icFb_rel (R := fun r1 r2 => FSame a1 e1 a2 e2 (Subtype.val r1) (Subtype.val r2)) C ?_
            intro vi hcv hkv hkv' hvi
            by_cases h1 : decide (wordBits vi + rowBits (insertRow (wordSym vi) hcv) +
                rowBits (copyRow (wordSym vi) hcv) ≤ c3) = false ∨ bEnd < (opos + clen.toUSize).toUInt64 +
                (rowBase (insertRow (wordSym vi) hcv) +
                  ((w3 >>> wordBits vi) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym vi) hcv)))) +
                (rowBase (copyRow (wordSym vi) hcv) +
                  (((w3 >>> wordBits vi) >>> rowBits (insertRow (wordSym vi) hcv))
                  &&& maskT T C.big C.size32 (rowBits (copyRow (wordSym vi) hcv))))
            · rw [dite_eq_left h1, dite_eq_left h1]
              exact ⟨rfl, hS⟩
            · rw [dite_eq_right h1, dite_eq_right h1]
              exact ihI _ (by rw [← hI]; exact icount_dec hi) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl hS'

/-- An entry into the fast loop depends only on the unread bytes. -/
theorem fastEnter_same {H : Hdr} {kk : USize} {a1 a2 : ByteArray} {e1 e2 : USize} {hs1 : e1.toNat ≤ a1.size}
    {hs2 : e2.toNat ≤ a2.size} {cap : USize} {word count : UInt64} {ring : ByteArray} {wpos pend written : USize}
    {b1 b2 : UInt8} {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag}
    {lits bEnd : UInt64} {p1 p2 : USize}
    {hinv1 : KInv H kk e1 word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag p1}
    {hinv2 : KInv H kk e2 word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag p2}
    {hm1 : p1.toNat + 40 ≤ e1.toNat} {hm2 : p2.toNat + 40 ≤ e2.toNat} (h : Same a1 e1 a2 e2 p1 p2) :
    FSame a1 e1 a2 e2
      (fastEnter H kk a1 e1 hs1 cap word count ring wpos pend written b1 b2 remaining iCount lCount dCount flags x tag
        lits bEnd p1 hinv1 hm1).val
      (fastEnter H kk a2 e2 hs2 cap word count ring wpos pend written b1 b2 remaining iCount lCount dCount flags x tag
        lits bEnd p2 hinv2 hm2).val := by
  unfold fastEnter
  dsimp only
  exact fastLoop_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl h

end Brotli.Decoder
