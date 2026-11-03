import Brotli.Decoder.StreamTop
import Brotli.Decoder.Work

/-!
# The decoder's work, call by call

A call's steps, in the work model, are at most a constant times the bits of its chunk that the spec's reading in order
takes and the bytes that reading produces from them, plus two for each byte it hands out, plus a constant.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The steps of one call of the decoder: the call's own, for a call `decStep` takes, and one for a call it turns away. -/
def callSteps (s : DState) (a : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat) (final : Bool) : Nat :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    callDSteps a (USize.ofNat stop) hs final (atPos s.val start) (atPos_inv s h.2.1 h.2.2) buf space
  else 1

/-- A state at a place holds at most 64 bits. -/
theorem DRel.held_le {D : Dec} {p : SPhase} (h : DRel D p) : D.held.length ≤ 64 := by
  have hw : (BitBuffer.mk D.word D.count).Wf := by
    unfold Dec.word Dec.count
    cases p with
    | wbits => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | mblock => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | skip => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | raw => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | hdr => obtain ⟨ht, _, _, _, _, _, hh, _⟩ := h; rw [ht]; exact hh.wf
    | cmds => obtain ⟨ht, _, _, _, hr⟩ := h; rw [ht]; exact hr.wf
    | ended => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
  unfold Dec.held
  rw [BitBuffer.held_length]
  exact hw.count_le

/-- The work bound. A call's steps are at most 35002 for each bit it uses, each byte it hands out and each of 65 more,
plus 35002, plus two for each byte it hands out. A call that rejects or reports the memory limit stands for its whole chunk
and its whole space instead, since it may have decoded bytes it then discarded. -/
theorem decoder_work {limit : Nat} {x : List UInt8} {R : Run DState} {c : Call} (h : Reaches decoder limit x R)
    (ha : R.Allowed x c) :
    ((R.reply decoder x c).status ≠ .rejected → (R.reply decoder x c).status ≠ .memoryLimit →
      callSteps R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final ≤
        35002 * (65 + 8 * (R.reply decoder x c).used + ((R.reply decoder x c).output.size - c.buf.length)) + 35002 +
          2 * ((R.reply decoder x c).output.size - c.buf.length)) ∧
    callSteps R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final ≤
      35002 * (65 + 8 * c.size + c.space + ((R.reply decoder x c).output.size - c.buf.length)) + 35002 +
        2 * ((R.reply decoder x c).output.size - c.buf.length) := by
  have hin := ha.inside
  have hfit := ha.fits
  obtain ⟨p, hrel, hE, -, hreach, -, -⟩ := (order_inv h).running ha.running
  have hsi : SInv p := by
    obtain ⟨n, hn⟩ := (hreach []).count
    exact (steps_le hn trivial).1
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
  obtain ⟨n, q, D', _, f1, f2, hr, f3, f4, f5, f6⟩ := callD_count (hs := hs) (final := c.final) [] c.space (atPos R.state.val c.pre.length)
    (atPos_inv R.state hg.2.1 hg.2.2) p c.buf.toByteArray (atPos_rel hrel _)
  rw [hpos0] at f1
  rw [hstop] at f2
  have hq : D'.pos.toNat = c.pre.length + (D'.pos.toNat - c.pre.length) := by omega
  have hqs : D'.pos.toNat - c.pre.length ≤ c.size := by omega
  rw [bits_at' hin _ hpos0 (Nat.zero_le _) hstop, bits_at' hin _ hq hqs hstop] at hr
  simp only [List.drop_zero, List.append_nil] at hr
  have e0 : (atPos R.state.val c.pre.length).held = R.state.val.held := rfl
  rw [e0] at hr
  obtain ⟨-, -, hpq, hb⟩ := steps_le hr hsi
  simp only [List.length_append, bits_length, List.length_drop, take_length hin] at hb
  have hh := hrel.held_le
  have hst := sstage_le hsi
  have eS : callSteps R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final =
      callDSteps (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space := by
    unfold callSteps
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
  have eU : (R.reply decoder x c).used = (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final
      (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).pos.toNat - c.pre.length := by
    unfold Run.reply
    show (decStep _ _ _ _ _ _ _).used = _
    unfold decStep
    rw [dite_eq_left hg]
  have hbl : c.buf.toByteArray.size = c.buf.length := List.size_toByteArray
  have hkeep : c.buf.length ≤ (R.reply decoder x c).output.size := by
    have := (decoder_truthful.keeps h ha).length_le
    show _ ≤ (R.reply decoder x c).output.data.size
    rw [← Array.length_toList]
    exact this
  rw [eS]
  rw [eO] at hkeep ⊢
  rw [eT, eU]
  refine ⟨fun e1 e2 => ?_, ?_⟩
  · have g5 := f5 e1 e2
    have g4 := f4 (by
      cases hst : (callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length)
        (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space).status with
      | needsInput => exact Or.inl rfl
      | needsOutput => exact Or.inl rfl
      | done => exact Or.inr rfl
      | rejected => exact absurd hst e1
      | memoryLimit => exact absurd hst e2)
    omega
  · omega

end Brotli.Decoder
