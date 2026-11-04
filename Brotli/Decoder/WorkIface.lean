import Brotli.Decoder.WorkCall
import Brotli.Decoder.MemAt

/-!
# The decoder's work at its interface

A call's work, in the work model, against the potential of where its state stands, with the bits as bytes used.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The work of one call of the decoder: the call's own, for a call `decStep` takes, and one for a call it turns away. -/
def callWork (s : DState) (a : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat) (final : Bool) : Nat :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    callDW a (USize.ofNat stop) hs final (atPos s.val start) (atPos_inv s h.2.1 h.2.2) buf space
  else 1

/-- The window a call allocates: WBITS's, when the call starts there and reads it. -/
def callWin (s : DState) (a : ByteArray) (start stop : Nat) (space : Nat) : Nat :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    winD (atPos s.val start) (runD a (USize.ofNat stop) hs (withCap (atPos s.val start) space)
      ((atPos_inv s h.2.1 h.2.2).withCap space))
  else 0

private theorem arith_pause {W dq ho ph dp hh size u hand po win : Nat} (hu : u ≤ size)
    (h : W + dq + 22343 * (ho + (size - u) * 8) + 282 * ph ≤ dp + 22343 * (hh + size * 8) + 284 * hand + 282 * po + win + 280) :
    W + dq + 22343 * ho + 282 * ph ≤ dp + 22343 * hh + 178744 * u + 284 * hand + 282 * po + win + 280 := by
  obtain ⟨d, rfl⟩ : ∃ d, size = u + d := ⟨size - u, by omega⟩
  rw [Nat.add_sub_cancel_left] at h
  have e1 : 22343 * (ho + d * 8) = 22343 * ho + 178744 * d := by
    rw [Nat.mul_add, Nat.mul_comm d 8, ← Nat.mul_assoc]
  have e2 : 22343 * (hh + (u + d) * 8) = 22343 * hh + 178744 * u + 178744 * d := by
    rw [Nat.mul_add, Nat.mul_comm (u + d) 8, ← Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
  rw [e1, e2] at h
  generalize 22343 * ho = A at h ⊢
  generalize 22343 * hh = B at h ⊢
  generalize 178744 * u = C at h ⊢
  generalize 178744 * d = E at h
  omega

private theorem arith_any {W dp hh s size o hand win : Nat} (h1 : s ≤ o) (h2 : o ≤ s + size)
    (h : W + 22343 * ((s + size - o) * 8) ≤ dp + 22343 * (hh + size * 8) + 284 * hand + win + 24042) :
    W ≤ dp + 22343 * hh + 178744 * (o - s) + 284 * hand + win + 24042 := by
  obtain ⟨d, rfl⟩ : ∃ d, o = s + d := ⟨o - s, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, size = d + e := ⟨size - d, by omega⟩
  have g1 : s + (d + e) - (s + d) = e := by omega
  rw [g1] at h
  rw [Nat.add_sub_cancel_left]
  have e1 : 22343 * (e * 8) = 178744 * e := by
    rw [Nat.mul_comm e 8, ← Nat.mul_assoc]
  have e2 : 22343 * (hh + (d + e) * 8) = 22343 * hh + 178744 * d + 178744 * e := by
    rw [Nat.mul_add, Nat.mul_comm (d + e) 8, ← Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
  rw [e1, e2] at h
  generalize 22343 * hh = B at h ⊢
  generalize 178744 * d = C at h ⊢
  generalize 178744 * e = E at h
  generalize 284 * hand = F at h ⊢
  omega

section
variable {x : List UInt8} {R : Run DState} {c : Call}

/-- One call of the decoder, against the potential: a call that pauses is paid for by the potential of where it starts,
22343 for each bit it takes from what its state holds and each of eight for each byte it uses, 284 for each byte it hands
out, 282 for each byte it leaves waiting, the window it allocates and 280, less the potential and bits where it pauses.
Any call is paid for by the potential, 22343 for each bit its state holds and each of eight for each byte it uses, 284 for
each byte it hands out, the window and 24042. -/
theorem call_pays (hin : R.read + c.size ≤ x.length) (hfit : c.pre.length + c.size + c.post.length < USize.size) {p : SPhase}
    (hrel : DRel R.state.val p) (hsi : SInv p) (hk : R.state.val.tag ≠ .wbits → 10 ≤ R.state.val.k.toNat) :
    ((R.reply decoder x c).status = .needsInput ∨ (R.reply decoder x c).status = .needsOutput →
      ∃ q, DRel (R.reply decoder x c).state.val q ∧ SInv q ∧
        ((R.reply decoder x c).state.val.tag ≠ .wbits → 10 ≤ (R.reply decoder x c).state.val.k.toNat) ∧
        (R.reply decoder x c).state.val.cmd.pend.toNat ≤ R.state.val.cmd.pend.toNat + 1 ∧
        callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final +
          dpot q (R.reply decoder x c).state.val + 22343 * (R.reply decoder x c).state.val.held.length +
          282 * R.state.val.cmd.pend.toNat ≤
          dpot p R.state.val + 22343 * R.state.val.held.length + 178744 * (R.reply decoder x c).used +
            284 * ((R.reply decoder x c).output.size - c.buf.length) + 282 * (R.reply decoder x c).state.val.cmd.pend.toNat +
            callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space + 280) ∧
    callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final ≤
      dpot p R.state.val + 22343 * R.state.val.held.length + 178744 * (R.reply decoder x c).used +
        284 * ((R.reply decoder x c).output.size - c.buf.length) +
        callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space + 24042 := by
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
  have hR : hdrRate = 22343 := rfl
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
    exact arith_pause (by omega) i
  · have i := C2 []
    rw [hb0, e0, e2, hR, hstop] at i
    simp only [List.length_append, bits_length, List.length_drop, take_length hin, List.append_nil] at i
    have hc := callD_ok (hs := hs) (final := c.final) c.space (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) p _
      c.buf.toByteArray (atPos_rel hrel _) rfl
    have h1 := hc.posLe
    have h2 := hc.posStop
    rw [hpos0] at h1
    rw [hstop] at h2
    exact arith_any (by omega) h2 i

end

end Brotli.Decoder
