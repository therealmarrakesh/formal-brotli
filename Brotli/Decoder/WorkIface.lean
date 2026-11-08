module

public import Brotli.Decoder.WorkCall
public import Brotli.Decoder.MemAt

@[expose] public section

/-!
# The decoder's work at its interface

A call's work, in the work model, against the potential of where its state stands, with the bits as bytes used.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The work of one call of the decoder: the call's own, for a call `decStep` takes, and one for a call it turns away. -/
def callWork (s : DState) (a : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat) (final : Bool) : Nat :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    callDW a (USize.ofNat stop) hs final (atPos s.val start) (atPos_inv s h.2.1 h.2.2) buf space
  else 1

/-- The window a call allocates: the one its loop allocates, when the call starts with none. -/
def callWin (s : DState) (a : ByteArray) (start stop : Nat) (space : Nat) : Nat :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    winD (atPos s.val start) (runD a (USize.ofNat stop) hs (withCap (atPos s.val start) space)
      ((atPos_inv s h.2.1 h.2.2).withCap space))
  else 0

private theorem arith_pause {W dq ho ph dp hh size u hand po win P0 P1 : Nat} (hu : u ≤ size) (h0 : P0 = size)
    (h1 : P1 = size - u)
    (h : W + dq + 2980 * (ho + (size - u) * 8) + P1 + 32 * ph ≤
      dp + 2980 * (hh + size * 8) + P0 + 34 * hand + 32 * po + win + 96) :
    W + dq + 2980 * ho + 32 * ph ≤ dp + 2980 * hh + 23841 * u + 34 * hand + 32 * po + win + 96 := by
  obtain ⟨d, rfl⟩ : ∃ d, size = u + d := ⟨size - u, by omega⟩
  rw [Nat.add_sub_cancel_left] at h h1
  rw [h0, h1] at h
  have e1 : 2980 * (ho + d * 8) = 2980 * ho + 23840 * d := by
    rw [Nat.mul_add, Nat.mul_comm d 8, ← Nat.mul_assoc]
  have e2 : 2980 * (hh + (u + d) * 8) = 2980 * hh + 23840 * u + 23840 * d := by
    rw [Nat.mul_add, Nat.mul_comm (u + d) 8, ← Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
  have e3 : 23841 * u = 23840 * u + u := by rw [Nat.succ_mul, Nat.mul_comm]
  rw [e1, e2] at h
  rw [e3]
  generalize 2980 * ho = A at h ⊢
  generalize 2980 * hh = B at h ⊢
  generalize 23840 * u = C at h ⊢
  generalize 23840 * d = E at h
  omega

private theorem arith_any {W dp hh s size o hand win P0 P1 : Nat} (h1 : s ≤ o) (h2 : o ≤ s + size) (h3 : P0 = size)
    (h4 : P1 = s + size - o)
    (h : W + 2980 * ((s + size - o) * 8) + P1 ≤ dp + 2980 * (hh + size * 8) + P0 + 34 * hand + win + 136) :
    W ≤ dp + 2980 * hh + 23841 * (o - s) + 34 * hand + win + 136 := by
  obtain ⟨d, rfl⟩ : ∃ d, o = s + d := ⟨o - s, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, size = d + e := ⟨size - d, by omega⟩
  have g1 : s + (d + e) - (s + d) = e := by omega
  rw [g1] at h h4
  rw [h3, h4] at h
  rw [Nat.add_sub_cancel_left]
  have e1 : 2980 * (e * 8) = 23840 * e := by
    rw [Nat.mul_comm e 8, ← Nat.mul_assoc]
  have e2 : 2980 * (hh + (d + e) * 8) = 2980 * hh + 23840 * d + 23840 * e := by
    rw [Nat.mul_add, Nat.mul_comm (d + e) 8, ← Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
  have e3 : 23841 * d = 23840 * d + d := by rw [Nat.succ_mul, Nat.mul_comm]
  rw [e1, e2] at h
  rw [e3]
  generalize 2980 * hh = B at h ⊢
  generalize 23840 * d = C at h ⊢
  generalize 23840 * e = E at h
  generalize 34 * hand = F at h ⊢
  omega

section
variable {x : List UInt8} {R : Run DState} {c : Call}

/-- One call of the decoder, against the potential: a call that pauses is paid for by the potential of where it starts,
2980 for each bit it takes from what its state holds and each of eight for each byte it uses and one more for taking the
byte, 34 for each byte it hands out, 32 for each byte it leaves waiting, the window it allocates and 96, less the
potential and bits where it pauses. Any call is paid for by the potential, 2980 for each bit its state holds, 23841 for
each byte it uses, 34 for each byte it hands out, the window and 136. -/
theorem call_pays (hin : R.read + c.size ≤ x.length) (hfit : c.pre.length + c.size + c.post.length < USize.size) {p : SPhase}
    (hrel : DRel R.state.val p) (hsi : SInv p) (hk : R.state.val.tag ≠ .wbits → 10 ≤ R.state.val.k.toNat) :
    ((R.reply decoder x c).status = .needsInput ∨ (R.reply decoder x c).status = .needsOutput →
      ∃ q, DRel (R.reply decoder x c).state.val q ∧ SInv q ∧
        ((R.reply decoder x c).state.val.tag ≠ .wbits → 10 ≤ (R.reply decoder x c).state.val.k.toNat) ∧
        (R.reply decoder x c).state.val.cmd.pend.toNat ≤ R.state.val.cmd.pend.toNat + 1 ∧
        callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final +
          dpot q (R.reply decoder x c).state.val + 2980 * (R.reply decoder x c).state.val.held.length +
          32 * R.state.val.cmd.pend.toNat ≤
          dpot p R.state.val + 2980 * R.state.val.held.length + 23841 * (R.reply decoder x c).used +
            34 * ((R.reply decoder x c).output.size - c.buf.length) + 32 * (R.reply decoder x c).state.val.cmd.pend.toNat +
            callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space + 96) ∧
    callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final ≤
      dpot p R.state.val + 2980 * R.state.val.held.length + 23841 * (R.reply decoder x c).used +
        34 * ((R.reply decoder x c).output.size - c.buf.length) +
        callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space + 136 := by
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
  obtain ⟨-, C1, C2⟩ := pay_callD (hs := hs) (final := c.final) c.space (atPos R.state.val c.pre.length)
    (atPos_inv R.state hg.2.1 hg.2.2) p c.buf.toByteArray (atPos_rel hrel _) hsi hk
  have eS : callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final =
      callDW (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space := by
    unfold callWork
    rw [dite_eq_left hg]
  have eW : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space =
      winD (atPos R.state.val c.pre.length) (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs
        (withCap (atPos R.state.val c.pre.length) c.space) ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)) := by
    unfold callWin
    rw [dite_eq_left hg]
  have eSt : (R.reply decoder x c).state.val = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).D := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).state.val = _
    unfold decStep
    rw [dite_eq_left hg]
  have eU : (R.reply decoder x c).used = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).pos.toNat - c.pre.length := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).used = _
    unfold decStep
    rw [dite_eq_left hg]
  have eO : (R.reply decoder x c).output = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).buf := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).output = _
    unfold decStep
    rw [dite_eq_left hg]
  have eT : (R.reply decoder x c).status = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).status := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).status = _
    unfold decStep
    rw [dite_eq_left hg]
  rw [eS, eW, eSt, eU, eO, eT]
  have hbl : c.buf.toByteArray.size = c.buf.length := List.size_toByteArray
  rw [hbl] at C1 C2
  have hb0 := bits_at' hin (atPos R.state.val c.pre.length) hpos0 (Nat.zero_le _) hstop []
  have e0 : (atPos R.state.val c.pre.length).held = R.state.val.held := rfl
  have e1 : (atPos R.state.val c.pre.length).cmd.pend = R.state.val.cmd.pend := rfl
  have e2 : dpot p (atPos R.state.val c.pre.length) = dpot p R.state.val := rfl
  have hR : hdrRate = 2980 := rfl
  refine ⟨fun hst => ?_, ?_⟩
  · obtain ⟨q, d1, d2, d3, d4, d5, d6, d7, d8⟩ := C1 hst
    rw [hpos0] at d5
    rw [hstop] at d6
    have i := d8 []
    have hq : (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).pos.toNat =
        c.pre.length + ((callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).pos.toNat - c.pre.length) := by omega
    have hb1 := bits_at' hin (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).D hq (by omega) hstop []
    rw [hb0, hb1, e0, e1, e2, hR] at i
    simp only [List.length_append, bits_length, List.length_drop, take_length hin, List.append_nil] at i
    refine ⟨q, d1, d2, d3, d7, ?_⟩
    exact arith_pause (by omega) (by omega) (by omega) i
  · have i := C2 []
    rw [hb0, e0, e2, hR, hstop] at i
    simp only [List.length_append, bits_length, List.length_drop, take_length hin, List.append_nil] at i
    have hc := callD_ok (hs := hs) (final := c.final) c.space (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) p _
      c.buf.toByteArray (atPos_rel hrel _) rfl
    have h1 := hc.posLe
    have h2 := hc.posStop
    rw [hpos0] at h1
    rw [hstop] at h2
    exact arith_any (by omega) h2 (by omega) (by omega) i

/-- The window a place is read with: none at WBITS and at the stream's end. -/
def placeWin : SPhase → Nat
  | .wbits => 0
  | .mblock w _ => w
  | .skip w _ _ _ => w
  | .raw w _ _ _ => w
  | .hdr w _ _ _ _ _ => w
  | .cmds w _ _ _ => w
  | .ended _ => 0

theorem placeWin_after (w : Nat) (last : Bool) (st : StreamState) : placeWin (afterBlock w last st) ≤ w := by
  unfold afterBlock
  cases last
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- No step of the reading in order past WBITS raises the window a place is read with. -/
theorem sStep_win : ∀ (p : SPhase) (bs : List Bool) (q : SPhase) (c : List Bool), p ≠ .wbits → sStep p bs = .next q c →
    placeWin q ≤ placeWin p
  | .wbits, _, _, _, hp, _ => absurd rfl hp
  | .mblock w st, bs, q, c, _, h => by
    obtain ⟨ms, b, -, e2⟩ := readIn_next' h
    cases ms with
    | lastEmpty =>
      cases e2
      exact Nat.zero_le _
    | metadata last skip =>
      cases hf : readFill b with
      | none => simp only [startPlace, hf] at e2; cases e2
      | some b' =>
        simp only [startPlace, hf] at e2
        cases e2
        exact Nat.le_refl _
    | data last mlen unc =>
      cases unc with
      | true =>
        cases hf : readFill b with
        | none => simp only [startPlace, hf, ↓reduceIte] at e2; cases e2
        | some b' =>
          simp only [startPlace, hf, ↓reduceIte] at e2
          cases e2
          exact Nat.le_refl _
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        exact blockWindow_le w st last mlen
  | .skip w st last 0, bs, q, c, _, h => by
    cases h
    exact placeWin_after w last st
  | .skip w st last (n + 1), bs, q, c, _, h => by
    obtain ⟨v, b, -, e2⟩ := readIn_next' h
    cases e2
    exact Nat.le_refl _
  | .raw w st last 0, bs, q, c, _, h => by
    cases h
    exact placeWin_after w last st
  | .raw w st last (n + 1), bs, q, c, _, h => by
    obtain ⟨v, b, -, e2⟩ := readIn_next' h
    cases e2
    exact Nat.le_refl _
  | .hdr w st last mlen g p, bs, q, c, _, h => by
    cases e : hStep g p bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      exact Nat.le_refl _
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      exact Nat.le_refl _
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .cmds w last m p, bs, q, c, _, h => by
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      exact Nat.le_refl _
    | exit s b =>
      by_cases hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance) = true
      · have h' : sStep (.cmds w last m p) bs = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b := by
          simp only [sStep, e, hc, ↓reduceIte]
        rw [h'] at h
        cases h
        exact placeWin_after _ _ _
      · have h' : sStep (.cmds w last m p) bs = .bad := by
          simp only [sStep, e]
          exact ite_eq_right hc
        rw [h'] at h
        cases h
    | bad =>
      have h' : sStep (.cmds w last m p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.cmds w last m p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .ended st, bs, q, c, _, h => by
    by_cases hm : bs.length % 8 = 0
    · simp only [sStep, hm, ↓reduceIte] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
      | some b =>
        simp only [sStep, hm, ↓reduceIte, e] at h
        cases h
        exact Nat.le_refl _

theorem reach_placeWin {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) (hp : p ≠ .wbits) :
    placeWin q ≤ placeWin p := by
  induction h with
  | refl => exact Nat.le_refl _
  | @next p0 b0 q1 c1 q0 c0 hs r ih =>
    have hq1 : q1 ≠ .wbits := by
      intro e
      subst e
      exact hp (reach_to_wbits (.next hs (.refl _ _))).1
    exact Nat.le_trans (ih hq1) (sStep_win _ _ _ _ hp hs)

/-- A place the reading in order reaches past WBITS is read with at most the window the stream declares. -/
theorem wbits_reach_win {q : SPhase} {bs c : List Bool} (h : Reach sStep .wbits bs q c) (hq : q ≠ .wbits) :
    ∃ v r, readWBITS bs = some (v, r) ∧ placeWin q ≤ windowSize v := by
  cases h with
  | refl => exact absurd rfl hq
  | next hs r =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' hs
    cases e2
    exact ⟨v, _, e1, reach_placeWin r (fun e => SPhase.noConfusion e)⟩

/-- The window a call allocates is at most the one the stream declares: the loop allocates no window larger than the
one its WBITS gives, or than the one its state holds the log size of before it has a window. Zero-filling the window
takes a round for each byte and for each 65536 of them, at most 256. -/
theorem callWin_le {limit : Nat} (h : Reaches decoder limit x R) (ha : R.Allowed x c) :
    callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space ≤ declaredWindow x + 272 := by
  have hin := ha.inside
  have hfit := ha.fits
  obtain ⟨p, hrel, -, hro, hreach, -, -⟩ := (order_inv h).running ha.running
  have hoff := h.offered_le
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
  have eW : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space =
      winD (atPos R.state.val c.pre.length) (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs
        (withCap (atPos R.state.val c.pre.length) c.space) ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)) := by
    unfold callWin
    rw [dite_eq_left hg]
  rw [eW]
  unfold winD
  by_cases hw : (atPos R.state.val c.pre.length).cmd.ring.size = 0 ∧
      (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs (withCap (atPos R.state.val c.pre.length) c.space)
        ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)).cmd.ring.size ≠ 0
  rotate_left
  · rw [ite_eq_right hw]
    exact Nat.zero_le _
  rw [ite_eq_left hw]
  have hr0 : R.state.val.cmd.ring.size = 0 := hw.1
  suffices hK : 2 ^ (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs (withCap (atPos R.state.val c.pre.length) c.space)
      ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)).k.toNat ≤ declaredWindow x + 16 by omega
  by_cases hw0 : R.state.val.tag = .wbits
  · have hp : p = .wbits := by
      cases p <;> first | rfl | exact absurd (hrel.1.symm.trans hw0) (fun e => DTag.noConfusion e)
    subst hp
    have hwf : (BitBuffer.mk (withCap (atPos R.state.val c.pre.length) c.space).cmd.word
        (withCap (atPos R.state.val c.pre.length) c.space).cmd.count).Wf := hrel.2.1
    obtain ⟨hn, hk⟩ := runD_past ⟨withCap (atPos R.state.val c.pre.length) c.space, (atPos_inv R.state hg.2.1 hg.2.2).withCap c.space⟩
      hw0 hwf (by show _ ≠ R.state.val.cmd.ring.size; rw [hr0]; exact hw.2)
    dsimp only at hn hk
    have hpk := Nat.pow_le_pow_right (show 0 < 2 by decide) hk
    have hpp : (withCap (atPos R.state.val c.pre.length) c.space).pos.toNat ≤ (USize.ofNat (c.pre.length + c.size)).toNat := by
      show (atPos R.state.val c.pre.length).pos.toNat ≤ _
      rw [hpos0, hstop]
      omega
    have hk10 := stepDWbits_k hwf hpp hn
    obtain ⟨rest, hr⟩ := stepDWbits_reads (hs := hs) hwf hpp hn (bits ((x.drop R.read).drop c.size))
    have hall : R.state.val.held ++ bits (x.drop R.read) = bits x := by
      have e1 := (reach_to_wbits (hreach (x.drop R.offered))).2
      have e2 : (x.take R.offered).drop R.read ++ x.drop R.offered = x.drop R.read := by
        rw [← List.drop_append_of_le_length (by rw [List.length_take]; omega), List.take_append_drop]
      rw [e2, List.take_append_drop] at e1
      exact e1
    have hb : availBits (withCap (atPos R.state.val c.pre.length) c.space).cmd.word
        (withCap (atPos R.state.val c.pre.length) c.space).cmd.count (R.input x c) (withCap (atPos R.state.val c.pre.length) c.space).pos
        (USize.ofNat (c.pre.length + c.size)) (bits ((x.drop R.read).drop c.size)) = bits x := by
      rw [← Dec.bits_cmd (D := withCap (atPos R.state.val c.pre.length) c.space)
        (by show R.state.val.tag ≠ .hdr; rw [hw0]; exact fun e => DTag.noConfusion e)]
      rw [bits_at' hin (withCap (atPos R.state.val c.pre.length) c.space) (pos := (withCap (atPos R.state.val c.pre.length) c.space).pos)
        hpos0 (Nat.zero_le _) hstop,
        List.drop_zero, List.take_append_drop]
      exact hall
    rw [hb] at hr
    have hd : declaredWindow x = windowSize (stepDWbits (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs
        (withCap (atPos R.state.val c.pre.length) c.space) (withCap (atPos R.state.val c.pre.length) c.space).pos).k.toNat := by
      unfold declaredWindow
      rw [hr]
    unfold windowSize at hd
    rw [Nat.shiftLeft_eq, Nat.one_mul] at hd
    have h16 : 16 ≤ 2 ^ (stepDWbits (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs
        (withCap (atPos R.state.val c.pre.length) c.space) (withCap (atPos R.state.val c.pre.length) c.space).pos).k.toNat :=
      Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk10.1)
    omega
  · -- No window yet past WBITS: the state holds the log size of the window its place is read with.
    have hreachx : Reach sStep .wbits (bits x) p (R.state.val.held ++ bits ((x.take R.offered).drop R.read ++ x.drop R.offered)) := by
      have e := hreach (x.drop R.offered)
      rw [List.take_append_drop] at e
      exact e
    have hpw : p ≠ .wbits := fun e => by rw [e] at hrel; exact hw0 hrel.1
    obtain ⟨v, rv, ev, hle⟩ := wbits_reach_win hreachx hpw
    have hd : declaredWindow x = windowSize v := by
      unfold declaredWindow
      rw [ev]
    have hnr : ∃ w st, NoRing R.state.val w st ∧ placeWin p = w := by
      cases p with
      | wbits => exact absurd rfl hpw
      | mblock w st => exact ⟨w, st, hrel.2.2.noRing hr0, rfl⟩
      | skip w st l n => exact ⟨w, st, hrel.2.2.1.noRing hr0, rfl⟩
      | ended st =>
        exfalso
        apply hw.2
        have he : (withCap (atPos R.state.val c.pre.length) c.space).tag = .ended := hrel.1
        rw [runD, dite_eq_left he]
        exact hr0
      | raw => exact absurd hrel.1 (hrel.noRing hr0).2.2
      | hdr => exact absurd hrel.1 (hrel.noRing hr0).1
      | cmds => exact absurd hrel.1 (hrel.noRing hr0).2.1
    obtain ⟨w, st, hn, hpw'⟩ := hnr
    have hkr := (runD_kr (hs := hs) ⟨withCap (atPos R.state.val c.pre.length) c.space, (atPos_inv R.state hg.2.1 hg.2.2).withCap c.space⟩
      hw0 ⟨hn.k10, hn.k24⟩).2.2.2
    have hpk : 2 ^ (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs (withCap (atPos R.state.val c.pre.length) c.space)
        ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)).k.toNat ≤ 2 ^ R.state.val.k.toNat :=
      Nat.pow_le_pow_right (by decide) hkr
    have hwin := hn.win
    omega

/-- A call from a state that holds a window allocates none. -/
theorem callWin_zero (hin : R.read + c.size ≤ x.length) (hfit : c.pre.length + c.size + c.post.length < USize.size)
    (ht : R.state.val.cmd.ring.size ≠ 0) : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space = 0 := by
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  unfold callWin winD
  rw [dite_eq_left hg]
  exact ite_eq_right (fun h => ht h.1)

/-- A call that allocates a window, or starts with one, pauses with one if it pauses. -/
theorem callWin_ring (hin : R.read + c.size ≤ x.length) (hfit : c.pre.length + c.size + c.post.length < USize.size)
    {p : SPhase} (hrel : DRel R.state.val p)
    (ht : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space ≠ 0 ∨ R.state.val.cmd.ring.size ≠ 0)
    (hst : (R.reply decoder x c).status = .needsInput ∨ (R.reply decoder x c).status = .needsOutput) :
    (R.reply decoder x c).state.val.cmd.ring.size ≠ 0 := by
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have eW : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space =
      winD (atPos R.state.val c.pre.length) (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs
        (withCap (atPos R.state.val c.pre.length) c.space) ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)) := by
    unfold callWin
    rw [dite_eq_left hg]
  have eSt : (R.reply decoder x c).state.val = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).D := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).state.val = _
    unfold decStep
    rw [dite_eq_left hg]
  have eT : (R.reply decoder x c).status = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).status := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).status = _
    unfold decStep
    rw [dite_eq_left hg]
  rw [eSt]
  rw [eT] at hst
  have hr : (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs (withCap (atPos R.state.val c.pre.length) c.space)
      ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)).cmd.ring.size ≠ 0 := by
    rcases ht with ht | ht
    · rw [eW] at ht
      unfold winD at ht
      by_cases hw : (atPos R.state.val c.pre.length).cmd.ring.size = 0 ∧
          (runD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs (withCap (atPos R.state.val c.pre.length) c.space)
            ((atPos_inv R.state hg.2.1 hg.2.2).withCap c.space)).cmd.ring.size ≠ 0
      · exact hw.2
      · rw [ite_eq_right hw] at ht
        exact absurd rfl ht
    · rw [(runD_ring ⟨withCap (atPos R.state.val c.pre.length) c.space, (atPos_inv R.state hg.2.1 hg.2.2).withCap c.space⟩ p
        ((atPos_rel hrel _).withCap _) ht).1]
      exact ht
  exact callD_ring c.space _ _ _ p (atPos_rel hrel _) hr hst

end

end Brotli.Decoder
