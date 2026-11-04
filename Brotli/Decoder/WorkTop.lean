import Brotli.Decoder.WorkIface

/-!
# The decoder's work, call by call

The work of a run's calls, in the work model, is at most 178744 for each byte the calls use (22343 for each bit), 284 for
each byte they hand out, five for each byte of the window the stream declares and 16 more, 562 for each call, and 24042.
A call pays for its work with the potential of where it starts, which it leaves where it pauses for the next call to use.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

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

/-- The runs the decoder reaches on the stream `x`, with the work of their calls in the work model and how many calls
they have had. -/
inductive ReachesW (limit : Nat) (x : List UInt8) : Run DState → Nat → Nat → Prop
  | start : ReachesW limit x (Run.initial decoder limit) 0 0
  | call {R : Run DState} {c : Call} {W n : Nat} : ReachesW limit x R W n → R.Allowed x c →
      ReachesW limit x (R.after decoder x c)
        (W + callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final) (n + 1)

theorem ReachesW.reaches {limit : Nat} {x : List UInt8} {R : Run DState} {W n : Nat} (h : ReachesW limit x R W n) :
    Reaches decoder limit x R := by
  induction h with
  | start => exact .start
  | call _ ha ih => exact .call ih ha

/-- The window a run has paid for: none while it runs at WBITS, and the declared window's after. -/
def winPaid (x : List UInt8) (R : Run DState) : Nat :=
  if R.status.stopped = false ∧ R.state.val.tag = .wbits then 0 else 5 * (declaredWindow x + 16)

theorem stopped_false {s : Status} : s.stopped = false ↔ s = .needsInput ∨ s = .needsOutput := by
  cases s <;> simp [Status.stopped]

theorem after_emitted {x : List UInt8} {R : Run DState} {c : Call} :
    (R.after decoder x c).emitted.length = R.emitted.length + ((R.reply decoder x c).output.size - c.buf.length) := by
  simp only [Run.after, List.length_append, List.length_drop]
  rw [Array.length_toList]
  rfl

private theorem run_step {W cw dp dq h h' r u e hd pd pd' wp wp' cwin n : Nat}
    (hW : W + dp + 22343 * h ≤ 178744 * r + 284 * e + 282 * pd + wp + 280 * n)
    (hc : cw + dq + 22343 * h' + 282 * pd ≤ dp + 22343 * h + 178744 * u + 284 * hd + 282 * pd' + cwin + 280)
    (hw : wp + cwin ≤ wp') :
    W + cw + dq + 22343 * h' ≤ 178744 * (r + u) + 284 * (e + hd) + 282 * pd' + wp' + 280 * (n + 1) := by
  rw [Nat.mul_add 178744, Nat.mul_add 284, Nat.mul_add 280]
  generalize 22343 * h = A at hW hc
  generalize 22343 * h' = A' at hc ⊢
  generalize 178744 * r = B at hW ⊢
  generalize 178744 * u = B' at hc ⊢
  generalize 284 * e = C at hW ⊢
  generalize 284 * hd = C' at hc ⊢
  generalize 282 * pd = P at hW hc
  generalize 282 * pd' = P' at hc ⊢
  generalize 280 * n = N at hW ⊢
  omega

private theorem run_stop {W cw dp h r u e hd pd wp cwin win n : Nat}
    (hW : W + dp + 22343 * h ≤ 178744 * r + 284 * e + 282 * pd + wp + 280 * n)
    (hc : cw ≤ dp + 22343 * h + 178744 * u + 284 * hd + cwin + 24042) (hp : pd ≤ n) (hw : wp + cwin ≤ win) :
    W + cw ≤ 178744 * (r + u) + 284 * (e + hd) + win + 562 * (n + 1) + 24042 := by
  have hP := Nat.mul_le_mul_left 282 hp
  rw [Nat.mul_add 178744, Nat.mul_add 284, Nat.mul_add 562]
  have e1 : 562 * n = 282 * n + 280 * n := by rw [← Nat.add_mul]
  rw [e1]
  generalize 22343 * h = A at hW hc
  generalize 178744 * r = B at hW ⊢
  generalize 178744 * u = B' at hc ⊢
  generalize 284 * e = C at hW ⊢
  generalize 284 * hd = C' at hc ⊢
  generalize 282 * pd = P at hW hP
  generalize 282 * n = P' at hP ⊢
  generalize 280 * n = N at hW ⊢
  omega

private theorem run_now {W dp h r e pd wp win n : Nat}
    (hW : W + dp + 22343 * h ≤ 178744 * r + 284 * e + 282 * pd + wp + 280 * n) (hp : pd ≤ n) (hw : wp ≤ win) :
    W ≤ 178744 * r + 284 * e + win + 562 * n + 24042 := by
  have hP := Nat.mul_le_mul_left 282 hp
  have e1 : 562 * n = 282 * n + 280 * n := by rw [← Nat.add_mul]
  rw [e1]
  generalize 22343 * h = A at hW
  generalize 178744 * r = B at hW ⊢
  generalize 284 * e = C at hW ⊢
  generalize 282 * pd = P at hW hP
  generalize 282 * n = P' at hP ⊢
  generalize 280 * n = N at hW ⊢
  omega

/-- What a run's work leaves to pay: a running state holds a place, the potential and bits of which, with the work so far,
are paid for by the bytes used and handed out, 282 for each byte waiting, which are at most one for each call, the window
paid for and 280 for each call; a run that has stopped has had all its work paid for. -/
theorem work_inv {limit : Nat} {x : List UInt8} {R : Run DState} {W n : Nat} (h : ReachesW limit x R W n) :
    (R.status.stopped = false → ∃ p, DRel R.state.val p ∧ SInv p ∧ (R.state.val.tag ≠ .wbits → 10 ≤ R.state.val.k.toNat) ∧
      R.state.val.cmd.pend.toNat ≤ n ∧
      W + dpot p R.state.val + 22343 * R.state.val.held.length ≤
        178744 * R.read + 284 * R.emitted.length + 282 * R.state.val.cmd.pend.toNat + winPaid x R + 280 * n) ∧
    (R.status.stopped = true → W ≤ 178744 * R.read + 284 * R.emitted.length + 5 * (declaredWindow x + 16) + 562 * n + 24042) := by
  induction h with
  | start =>
    by_cases hl : limit < fixedCost
    · have hI : Run.initial decoder limit = ⟨⟨deadD, _, deadD_rel⟩, .memoryLimit, 0, 0, [], false⟩ := by
        show (⟨(decStart limit).1, (decStart limit).2, 0, 0, [], false⟩ : Run DState) = _
        unfold decStart
        rw [ite_eq_left hl]
      rw [hI]
      exact ⟨fun e => Bool.noConfusion e, fun _ => Nat.zero_le _⟩
    · have hI : Run.initial decoder limit = ⟨⟨liveD limit, _, liveD_rel limit⟩, .needsInput, 0, 0, [], false⟩ := by
        show (⟨(decStart limit).1, (decStart limit).2, 0, 0, [], false⟩ : Run DState) = _
        unfold decStart
        rw [ite_eq_right hl]
      rw [hI]
      refine ⟨fun _ => ⟨.wbits, liveD_rel limit, trivial, fun e => absurd rfl e, Nat.le_of_eq rfl, ?_⟩, fun e => Bool.noConfusion e⟩
      have e1 : dpot .wbits (liveD limit) = 0 := rfl
      have e2 : (liveD limit).held.length = 0 := rfl
      have e3 : (liveD limit).cmd.pend.toNat = 0 := rfl
      dsimp only
      rw [e1, e2, e3]
      omega
  | @call R c W n hR ha ih =>
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨p, hrel, hsi, hk, hpn, hW⟩ := ih.1 ha.running
    obtain ⟨P, G⟩ := call_pays (x := x) (R := R) (c := c) hin hfit hrel hsi hk
    have hle := callWin_le hR.reaches ha
    have em := after_emitted (x := x) (R := R) (c := c)
    have hrd : (R.after decoder x c).read = R.read + (R.reply decoder x c).used := rfl
    have hs1 : (R.after decoder x c).status = (R.reply decoder x c).status := rfl
    have hs2 : (R.after decoder x c).state = (R.reply decoder x c).state := rfl
    have hwR : winPaid x R = if R.state.val.tag = .wbits then 0 else 5 * (declaredWindow x + 16) := by
      unfold winPaid
      by_cases ht : R.state.val.tag = .wbits
      · rw [ite_eq_left ⟨ha.running, ht⟩, ite_eq_left ht]
      · rw [ite_eq_right (fun e => ht e.2), ite_eq_right ht]
    refine ⟨fun hst => ?_, fun hst => ?_⟩
    · rw [hs1] at hst
      have hst' := stopped_false.mp hst
      obtain ⟨q, d1, d2, d3, d4, d5⟩ := P hst'
      have hwq : winPaid x R + callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space ≤
          winPaid x (R.after decoder x c) := by
        have hwR' : winPaid x (R.after decoder x c) =
            if (R.reply decoder x c).state.val.tag = .wbits then 0 else 5 * (declaredWindow x + 16) := by
          unfold winPaid
          rw [hs1, hs2]
          by_cases ht : (R.reply decoder x c).state.val.tag = .wbits
          · rw [ite_eq_left ⟨hst, ht⟩, ite_eq_left ht]
          · rw [ite_eq_right (fun e => ht e.2), ite_eq_right ht]
        rw [hwR, hwR']
        by_cases ht : R.state.val.tag = .wbits
        · rw [ite_eq_left ht]
          by_cases ht' : (R.reply decoder x c).state.val.tag = .wbits
          · rw [ite_eq_left ht']
            by_cases hc : callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space = 0
            · omega
            · exact absurd ht' (callWin_tag hin hfit (Or.inl hc) hst')
          · rw [ite_eq_right ht']
            omega
        · rw [ite_eq_right ht, callWin_zero hin hfit ht, ite_eq_right (callWin_tag hin hfit (Or.inr ht) hst')]
          omega
      refine ⟨q, by rw [hs2]; exact d1, d2, by rw [hs2]; exact d3, by rw [hs2]; omega, ?_⟩
      rw [hs2, hrd, em]
      exact run_step hW d5 hwq
    · have hc := G
      have hwq : winPaid x R + callWin R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.space ≤
          5 * (declaredWindow x + 16) := by
        rw [hwR]
        by_cases ht : R.state.val.tag = .wbits
        · rw [ite_eq_left ht]
          omega
        · rw [ite_eq_right ht, callWin_zero hin hfit ht]
          omega
      rw [hrd, em]
      exact run_stop hW hc hpn hwq

/-- The work bound. The work of a run's calls, in the work model, is at most 178744 for each byte they use, 284 for each
byte they hand out, five for each byte of the window the stream declares and 16 more, 562 for each call, and 24042. -/
theorem decoder_work {limit : Nat} {x : List UInt8} {R : Run DState} {W n : Nat} (h : ReachesW limit x R W n) :
    W ≤ 178744 * R.read + 284 * R.emitted.length + 5 * (declaredWindow x + 16) + 562 * n + 24042 := by
  obtain ⟨I1, I2⟩ := work_inv h
  cases hst : R.status.stopped with
  | true => exact I2 hst
  | false =>
    obtain ⟨p, -, -, -, hpn, hW⟩ := I1 hst
    have hw : winPaid x R ≤ 5 * (declaredWindow x + 16) := by
      unfold winPaid
      split <;> omega
    exact run_now hW hpn hw

end Brotli.Decoder
