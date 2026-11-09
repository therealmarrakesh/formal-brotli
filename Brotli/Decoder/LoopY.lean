module

public import Brotli.Decoder.FastExit

@[expose] public section

/-!
# The command loop on the bytes waiting, compiled

`runCmdKY` (`LoopK.lean`) is `runCmdKX` with the window position, the bytes written and the context bytes worked out from
the bytes waiting: `runCmdKY_eq` takes the two in lockstep, `kstepX_win` for a step and `win_fast` for the fast loop.
`runCmdFY` enters it from a state whose fields are of that form, which every state the stream reaches is (the bytes
written are the window position, or the window less 16 once it has filled, and the context bytes are the window's two
before the position), and otherwise runs `runCmdFX`; `runCmdF_csimp` makes the compiled code run it.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- An equation with a dependent `if` on its left, case by case, the condition found by unification. -/
theorem dite_cases' {c : Prop} [Decidable c] {β : Type} {t : c → β} {e : ¬ c → β} {r : β} (h1 : ∀ h : c, t h = r)
    (h2 : ∀ h : ¬ c, e h = r) : dite c t e = r := by
  by_cases h : c
  · rw [dite_eq_left h]
    exact h1 h
  · rw [dite_eq_right h]
    exact h2 h

/-- `dite_cases'` for a plain `if`. -/
theorem ite_cases' {c : Prop} [Decidable c] {β : Type} {t e r : β} (h1 : c → t = r) (h2 : ¬ c → e = r) :
    ite c t e = r := by
  by_cases h : c
  · rw [ite_eq_left h]
    exact h1 h
  · rw [ite_eq_right h]
    exact h2 h

/-- What the fast loop is entered with, from the step machine's position: its commands fit `bEnd`, which is within
`2 ^ 30` and no further past the window position than the room ahead of the bytes waiting. -/
theorem fast_bounds {k cap pend wpos : USize} {remaining lits clen : UInt64} (hk : k.toNat ≤ 24)
    (h16 : 16 ≤ 2 ^ k.toNat) (hwp : wpos.toNat < 2 ^ k.toNat)
    (h1 : lits ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64))
    (h2 : clen ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) - lits) :
    wpos.toNat + (lits.toNat + clen.toNat) ≤
        (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)).toNat ∧
      (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)).toNat < 2 ^ 30 ∧
      (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)).toNat ≤
        wpos.toNat + (if room k cap ≤ pend then 0 else (room k cap).toNat - pend.toNat) := by
  have hR := room_le16 (cap := cap) hk h16
  have h24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hA : (umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)).toNat ≤
      (if room k cap ≤ pend then 0 else (room k cap).toNat - pend.toNat) := by
    have h0 : (0 : UInt64).toNat = 0 := rfl
    by_cases hrp : room k cap ≤ pend
    · rw [ite_eq_left hrp, ite_eq_left hrp, umin_toNat, h0]
      omega
    · rw [ite_eq_right hrp, ite_eq_right hrp, umin_toNat, USize.toNat_toUInt64,
        room_sub' (Nat.le_of_lt (room_lt hrp))]
      omega
  generalize umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) = A at h1 h2 hA ⊢
  have hA24 : A.toNat ≤ 2 ^ 24 := by split at hA <;> omega
  have e : (wpos.toUInt64 + A).toNat = wpos.toNat + A.toNat := by
    rw [u64_add_small (by rw [USize.toNat_toUInt64]; omega), USize.toNat_toUInt64]
  have h1' := UInt64.le_iff_toNat_le.mp h1
  have h2' := UInt64.le_iff_toNat_le.mp h2
  rw [u64_sub_le h1'] at h2'
  rw [e]
  exact ⟨by omega, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The loop on the bytes waiting is `runCmdKX` on the fields they stand for. -/
theorem runCmdKY_eq (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (cap pB : USize) :
    ∀ (N : Nat) (n : USize), n.toNat = N → ∀ (fresh : Bool) (cell : RunOut) (word count : UInt64) (ring : ByteArray)
      (pend : USize) (remaining iCount lCount dCount : UInt64) (flags : Flags) (x : CmdExt) (tag : Tag) (left : UInt64)
      (pos : USize) (hinv : KInv H k stop word count ring (yWpos k pB pend) (yWr k pB pend) x.iCur x.iPrev x.lCur
        x.lPrev x.dCur x.dPrev x.copyBits x.dist x.wordBuf x.wordPos tag pos),
      (pend - pB).toNat ≤ 2 ^ 25 + pend.toNat →
      runCmdKY H k a stop hs cap pB n fresh cell word count ring pend remaining iCount lCount dCount flags x tag left pos
        hinv =
      runCmdKX H k a stop hs n fresh cell word count ring (yWpos k pB pend) pend cap (yWr k pB pend)
        (backB ring (ringMask k) (pend - pB) (USize.ofNat 1)) (backB ring (ringMask k) (pend - pB) (USize.ofNat 2))
        remaining iCount lCount dCount flags x tag left pos hinv := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro n hN fresh cell word count ring pend remaining iCount lCount dCount flags x tag left pos hinv hJ
  -- the continuations agree where the fields are the ones the bytes waiting stand for
  have agree : ∀ (m : USize), m.toNat < N → ∀ fr, AgreeW H k stop cap pB
      (fun cell word count ring wpos pend cap' written p1 p2 remaining iCount lCount dCount flags x tag left pos h =>
        runCmdKX H k a stop hs m fr cell word count ring wpos pend cap' written p1 p2 remaining iCount lCount dCount
          flags x tag left pos h)
      (fun cell word count ring _ pend _ _ _ _ remaining iCount lCount dCount flags x tag left pos h =>
        runCmdKY H k a stop hs cap pB m fr cell word count ring pend remaining iCount lCount dCount flags x tag left pos
          (h.rederive pB pend)) := by
    intro m hm fr cell word count ring wpos pend cap' written p1 p2 remaining iCount lCount dCount flags x tag left pos
      h hw
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hJ'⟩ := hw
    exact (ih _ hm m rfl fr cell word count ring pend remaining iCount lCount dCount flags x tag left pos _ hJ').symm
  have hk := hinv.k24
  have h16 := hinv.k16
  by_cases hn : n = 0
  · rw [runCmdKY, runCmdKX, dite_eq_left hn, dite_eq_left hn]
    simp only [mkCmdY, backByte_eq]
  have hlt1 : (n - USize.ofNat 1).toNat < N := by have := usize_pred hn; have := usize_ne hn; omega
  rw [runCmdKY, runCmdKX, dite_eq_right hn, dite_eq_right hn]
  dsimp only
  simp only [backByte_eq]
  by_cases hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
      (if tag = .literals then left else 0) ≤
        umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) ∧
      x.clen ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) -
        (if tag = .literals then left else 0) ∧ USize.ofNat 2 ≤ yWr k pB pend
  · rw [dite_eq_left hf, dite_eq_left hf]
    -- the fast loop: both loops enter it alike, and the state it leaves with has the fields its bytes waiting stand for
    have hm : pos.toNat + 40 ≤ stop.toNat := by
      have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
      rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
      have := hinv.pos
      omega
    obtain ⟨hA, hB, hbe⟩ := fast_bounds hk h16 hinv.wpos hf.2.2.2.1 hf.2.2.2.2.1
    have hX := fastEnter_exit (H := H) (kk := k) (a := a) (stop := stop) (hs := hs) (cap := cap) (pend := pend)
      (p1 := backB ring (ringMask k) (pend - pB) (USize.ofNat 1))
      (p2 := backB ring (ringMask k) (pend - pB) (USize.ofNat 2)) (remaining := remaining) (iCount := iCount)
      (lCount := lCount) (dCount := dCount) (flags := flags) (hinv := hinv) (hm := hm) hA hB
    have h2 : 2 ≤ (yWr k pB pend).toNat := by
      have := USize.le_iff_toNat_le.mp hf.2.2.2.2.2
      rwa [fastLit (by decide)] at this
    have hW := win_fast hk h16 hJ h2 hbe hX
    exact (agree _ hlt1 false _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hW).symm
  rw [dite_eq_right hf, dite_eq_right hf]
  -- a step of the step machine
  have hslow : kstepY H k a stop hs cap pB
        (fun cell word count ring pend remaining iCount lCount dCount flags x tag left pos h =>
          runCmdKY H k a stop hs cap pB (n - USize.ofNat 1) true cell word count ring pend remaining iCount lCount dCount
            flags x tag left pos h)
        (fun c => c) word count ring pend remaining iCount lCount dCount flags x tag left pos cell hinv =
      kstepX H k a stop hs
        (fun cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags x tag left pos h =>
          runCmdKX H k a stop hs (n - USize.ofNat 1) true cell word count ring wpos pend cap written p1 p2 remaining
            iCount lCount dCount flags x tag left pos h)
        (fun c => c) word count ring (yWpos k pB pend) pend cap (yWr k pB pend)
        (backB ring (ringMask k) (pend - pB) (USize.ofNat 1)) (backB ring (ringMask k) (pend - pB) (USize.ofNat 2))
        remaining iCount lCount dCount flags x tag left pos cell hinv := by
    rw [kstepY_eq]
    simp only [backByte_eq]
    refine (kstepX_win (agree _ hlt1 true) ?_).symm
    exact ⟨rfl, rfl, rfl, rfl, rfl, hJ⟩
  cases tag
  case distance =>
    dsimp only
    by_cases hfw : fresh = false ∧ remaining ≠ 0 ∧ ¬ x.code < 128 ∧ dCount ≠ 0 ∧ USize.ofNat 4 ≤ n
    · rw [dite_eq_left hfw, dite_eq_left hfw]
      have hlt4 : (n - USize.ofNat 4).toNat < N := by
        have h4 := USize.le_iff_toNat_le.mp hfw.2.2.2.2
        rw [fastLit (by decide)] at h4
        rw [USize.toNat_sub_of_le _ _ hfw.2.2.2.2, fastLit (by decide)]
        omega
      refine dite_cases' (fun hwb => ?_) (fun hwb => ?_)
      rotate_left
      · rw [dite_eq_right hwb]
        exact hslow
      rw [dite_eq_left hwb]
      try dsimp only
      refine dite_cases' (fun hnb => ?_) (fun hnb => ?_)
      rotate_left
      · rw [dite_eq_right hnb]
        exact hslow
      rw [dite_eq_left hnb]
      try dsimp only
      refine dite_cases' (fun hd0 => ?_) (fun hd0 => ?_)
      · rw [dite_eq_left hd0]
        exact hslow
      rw [dite_eq_right hd0]
      try dsimp only
      refine dite_cases' (fun hwd => ?_) (fun hwd => ?_)
      rotate_left
      · rw [dite_eq_right hwd]
        exact hslow
      rw [dite_eq_left hwd]
      try dsimp only
      refine dite_cases' (fun hdv => ?_) (fun hdv => ?_)
      rotate_left
      · rw [dite_eq_right hdv]
        exact hslow
      rw [dite_eq_left hdv]
      try dsimp only
      refine ite_cases' (fun hrem => ?_) (fun hrem => ?_)
      · rw [ite_eq_left hrem]
        exact hslow
      rw [ite_eq_right hrem]
      try dsimp only
      refine dite_cases' (fun hw0 => ?_) (fun hw0 => ?_)
      · rw [dite_eq_left hw0]
        exact hslow
      rw [dite_eq_right hw0]
      try dsimp only
      refine dite_cases' (fun hrm => ?_) (fun hrm => ?_)
      · rw [dite_eq_left hrm]
        exact hslow
      rw [dite_eq_right hrm]
      try dsimp only
      refine ite_cases' (fun hend => ?_) (fun hend => ?_)
      rotate_left
      · rw [ite_eq_right hend]
        exact hslow
      rw [ite_eq_left hend]
      try dsimp only
      refine (agree _ hlt4 true _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_).symm
      exact win_word h16 ⟨rfl, rfl, rfl, rfl, rfl, hJ⟩ hrm
    · rw [dite_eq_right hfw, dite_eq_right hfw]
      exact hslow
  all_goals exact hslow

/-- `runCmdF` entered on the bytes waiting: the position written next, unmasked, is the window position while the
window has not filled, and a window on once it has; with the context bytes the window's two before it, the loop on the
bytes waiting runs, and otherwise `runCmdFX`. -/
@[inline] def entryO (k wpos written : USize) : USize := if written = wpos then wpos else wpos + ringSize k

def runCmdFY (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) (h : CmdInv H k stop st pos) : Cmd :=
  match st, h with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags, x, tag, left, sp,
      ss⟩, h =>
    let o := entryO k wpos written
    if (written = wpos ∨ written = ringSize k - USize.ofNat 16) ∧ p1 = backByte k ring o (USize.ofNat 1) h.k24 h.size ∧
        p2 = backByte k ring o (USize.ofNat 2) h.k24 h.size then
      runCmdKY H k a stop hs cap (pend - o) n true ⟨word, count, pos, wpos, ByteArray.empty, p1, p2, 0, 0⟩ word count ring
        pend remaining iCount lCount dCount flags x tag left pos (h.rederive (pend - o) pend)
    else
      runCmdFX H k a stop hs n
        ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags, x, tag, left, sp,
          ss⟩ pos h

/-- `runCmdKX` depends on its fields' values, not on how they are written. -/
theorem runCmdKX_congr {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {n : USize}
    {fresh : Bool} {cell : RunOut} {word count : UInt64} {ring : ByteArray} {wpos wpos' pend cap written written' : USize}
    {p1 p1' p2 p2' : UInt8} {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag}
    {left : UInt64} {pos : USize}
    {h : KInv H k stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist x.wordBuf
      x.wordPos tag pos}
    {h' : KInv H k stop word count ring wpos' written' x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos}
    (e1 : wpos = wpos') (e2 : written = written') (e3 : p1 = p1') (e4 : p2 = p2') :
    runCmdKX H k a stop hs n fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags x
        tag left pos h =
      runCmdKX H k a stop hs n fresh cell word count ring wpos' pend cap written' p1' p2' remaining iCount lCount dCount
        flags x tag left pos h' := by
  subst e1 e2 e3 e4
  rfl

/-- Where the state's fields are of that form, the loop on the bytes waiting is `runCmdFX`. -/
theorem runCmdFY_on (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize)
    {word count : UInt64} {ring : ByteArray} {wpos pend cap written : USize} {p1 p2 : UInt8}
    {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag} {left : UInt64} {sp pos : USize}
    {ss : StepStatus}
    (h : KInv H k stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos) (o : USize)
    (hoN : (o.toNat = wpos.toNat ∧ written = wpos) ∨ (o.toNat = wpos.toNat + 2 ^ k.toNat ∧ written ≠ wpos))
    (hwr : written = wpos ∨ written = ringSize k - USize.ofNat 16)
    (he1 : p1 = backByte k ring o (USize.ofNat 1) h.k24 h.size) (he2 : p2 = backByte k ring o (USize.ofNat 2) h.k24 h.size) :
    runCmdKY H k a stop hs cap (pend - o) n true ⟨word, count, pos, wpos, ByteArray.empty, p1, p2, 0, 0⟩ word count ring
        pend remaining iCount lCount dCount flags x tag left pos (h.rederive (pend - o) pend) =
      runCmdFX H k a stop hs n
        ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags, x, tag, left, sp,
          ss⟩ pos h := by
    have hk := h.k24
    have h16 := h.k16
    have hwp : wpos.toNat < 2 ^ k.toNat := h.wpos
    have hwr16 : written.toNat + 16 ≤ 2 ^ k.toNat := h.written
    have h24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have hmk := ringMask_toNat hk
    have eo : pend - (pend - o) = o := by
      calc pend - (pend - o) = (pend - o + o) - (pend - o) := by rw [USize.sub_add_cancel]
        _ = o := by rw [USize.add_comm, USize.add_sub_cancel]
    have hJ : (pend - (pend - o)).toNat ≤ 2 ^ 25 + pend.toNat := by
      rw [eo]
      rcases hoN with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
    unfold runCmdFX
    dsimp only
    rw [runCmdKY_eq H k a stop hs cap (pend - o) _ n rfl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hJ]
    apply runCmdKX_congr
    · -- the window position
      show (pend - (pend - o)) &&& ringMask k = wpos
      rw [eo]
      apply USize.toNat_inj.mp
      rw [umask_mod hmk]
      rcases hoN with ⟨e, _⟩ | ⟨e, _⟩
      · rw [e]
        exact Nat.mod_eq_of_lt hwp
      · rw [e, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt hwp
    · -- the bytes written
      show usmin (ringSize k - USize.ofNat 16) (pend - (pend - o)) = written
      rw [eo]
      apply USize.toNat_inj.mp
      rw [usmin_toNat, cap16_toNat hk h16]
      rcases hoN with ⟨e, hw⟩ | ⟨e, hne⟩
      · have := congrArg USize.toNat hw
        omega
      · rcases hwr with hw | hw
        · exact absurd hw hne
        · have := congrArg USize.toNat hw
          rw [cap16_toNat hk h16] at this
          omega
    · rw [eo, he1, backByte_eq]
    · rw [eo, he2, backByte_eq]

theorem runCmdFY_eq (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) (h : CmdInv H k stop st pos) : runCmdFY H k a stop hs n st pos h = runCmdFX H k a stop hs n st pos h := by
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags, x, tag, left,
    sp, ss⟩ := st
  have hk := h.k24
  have hwp : wpos.toNat < 2 ^ k.toNat := h.wpos
  have hsz := ringSize_toNat hk
  have h24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hoN : ((entryO k wpos written).toNat = wpos.toNat ∧ written = wpos) ∨
      ((entryO k wpos written).toNat = wpos.toNat + 2 ^ k.toNat ∧ written ≠ wpos) := by
    unfold entryO
    by_cases hw : written = wpos
    · rw [ite_eq_left hw]
      exact Or.inl ⟨rfl, hw⟩
    · rw [ite_eq_right hw]
      exact Or.inr ⟨by rw [fastAdd (a := wpos) (b := ringSize k) (by rw [hsz]; omega), hsz], hw⟩
  unfold runCmdFY
  dsimp only
  split
  · rename_i hc
    exact runCmdFY_on H k a stop hs n h _ hoN hc.1 hc.2.1 hc.2.2
  · rfl

/-- `runCmdF` runs as `runCmdFY`, the command loop on the bytes waiting. -/
@[csimp] theorem runCmdF_csimp : @runCmdF = @runCmdFY := by
  funext H k a stop hs n st pos h
  rw [runCmdFY_eq, runCmdF_eqX]

end Brotli.Decoder
