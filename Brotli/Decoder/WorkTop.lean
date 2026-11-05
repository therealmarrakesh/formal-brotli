import Brotli.Decoder.WorkIface

/-!
# The decoder's work, call by call

The work of a run's calls, in the work model, is at most 35761 for each byte the calls use (4470 for each bit, and one for taking it), 284 for
each byte they hand out, one for each byte of the window the stream declares and 272 more, 408 for each call, and 408.
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
  if R.status.stopped = false ∧ R.state.val.tag = .wbits then 0 else (declaredWindow x + 272)

theorem stopped_false {s : Status} : s.stopped = false ↔ s = .needsInput ∨ s = .needsOutput := by
  cases s <;> simp [Status.stopped]

theorem after_emitted {x : List UInt8} {R : Run DState} {c : Call} :
    (R.after decoder x c).emitted.length = R.emitted.length + ((R.reply decoder x c).output.size - c.buf.length) := by
  simp only [Run.after, List.length_append, List.length_drop]
  rw [Array.length_toList]
  rfl

private theorem run_step {W cw dp dq h h' r u e hd pd pd' wp wp' cwin n : Nat}
    (hW : W + dp + 4470 * h ≤ 35761 * r + 284 * e + 282 * pd + wp + 126 * n)
    (hc : cw + dq + 4470 * h' + 282 * pd ≤ dp + 4470 * h + 35761 * u + 284 * hd + 282 * pd' + cwin + 126)
    (hw : wp + cwin ≤ wp') :
    W + cw + dq + 4470 * h' ≤ 35761 * (r + u) + 284 * (e + hd) + 282 * pd' + wp' + 126 * (n + 1) := by
  rw [Nat.mul_add 35761, Nat.mul_add 284, Nat.mul_add 126]
  generalize 4470 * h = A at hW hc
  generalize 4470 * h' = A' at hc ⊢
  generalize 35761 * r = B at hW ⊢
  generalize 35761 * u = B' at hc ⊢
  generalize 284 * e = C at hW ⊢
  generalize 284 * hd = C' at hc ⊢
  generalize 282 * pd = P at hW hc
  generalize 282 * pd' = P' at hc ⊢
  generalize 126 * n = N at hW ⊢
  omega

private theorem run_stop {W cw dp h r u e hd pd wp cwin win n : Nat}
    (hW : W + dp + 4470 * h ≤ 35761 * r + 284 * e + 282 * pd + wp + 126 * n)
    (hc : cw ≤ dp + 4470 * h + 35761 * u + 284 * hd + cwin + 408) (hp : pd ≤ n) (hw : wp + cwin ≤ win) :
    W + cw ≤ 35761 * (r + u) + 284 * (e + hd) + win + 408 * (n + 1) + 408 := by
  have hP := Nat.mul_le_mul_left 282 hp
  rw [Nat.mul_add 35761, Nat.mul_add 284, Nat.mul_add 408]
  have e1 : 408 * n = 282 * n + 126 * n := by rw [← Nat.add_mul]
  rw [e1]
  generalize 4470 * h = A at hW hc
  generalize 35761 * r = B at hW ⊢
  generalize 35761 * u = B' at hc ⊢
  generalize 284 * e = C at hW ⊢
  generalize 284 * hd = C' at hc ⊢
  generalize 282 * pd = P at hW hP
  generalize 282 * n = P' at hP ⊢
  generalize 126 * n = N at hW ⊢
  omega

private theorem run_now {W dp h r e pd wp win n : Nat}
    (hW : W + dp + 4470 * h ≤ 35761 * r + 284 * e + 282 * pd + wp + 126 * n) (hp : pd ≤ n) (hw : wp ≤ win) :
    W ≤ 35761 * r + 284 * e + win + 408 * n + 408 := by
  have hP := Nat.mul_le_mul_left 282 hp
  have e1 : 408 * n = 282 * n + 126 * n := by rw [← Nat.add_mul]
  rw [e1]
  generalize 4470 * h = A at hW
  generalize 35761 * r = B at hW ⊢
  generalize 284 * e = C at hW ⊢
  generalize 282 * pd = P at hW hP
  generalize 282 * n = P' at hP ⊢
  generalize 126 * n = N at hW ⊢
  omega

/-- What a run's work leaves to pay: a running state holds a place, the potential and bits of which, with the work so far,
are paid for by the bytes used and handed out, 282 for each byte waiting, which are at most one for each call, the window
paid for and 126 for each call; a run that has stopped has had all its work paid for. -/
theorem work_inv {limit : Nat} {x : List UInt8} {R : Run DState} {W n : Nat} (h : ReachesW limit x R W n) :
    (R.status.stopped = false → ∃ p, DRel R.state.val p ∧ SInv p ∧ (R.state.val.tag ≠ .wbits → 10 ≤ R.state.val.k.toNat) ∧
      R.state.val.cmd.pend.toNat ≤ n ∧
      W + dpot p R.state.val + 4470 * R.state.val.held.length ≤
        35761 * R.read + 284 * R.emitted.length + 282 * R.state.val.cmd.pend.toNat + winPaid x R + 126 * n) ∧
    (R.status.stopped = true → W ≤ 35761 * R.read + 284 * R.emitted.length + (declaredWindow x + 272) + 408 * n + 408) := by
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
    have hwR : winPaid x R = if R.state.val.tag = .wbits then 0 else (declaredWindow x + 272) := by
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
            if (R.reply decoder x c).state.val.tag = .wbits then 0 else (declaredWindow x + 272) := by
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
          (declaredWindow x + 272) := by
        rw [hwR]
        by_cases ht : R.state.val.tag = .wbits
        · rw [ite_eq_left ht]
          omega
        · rw [ite_eq_right ht, callWin_zero hin hfit ht]
          omega
      rw [hrd, em]
      exact run_stop hW hc hpn hwq

/-- The most a state's place holds: a header's place, with what its end costs. -/
theorem dpot_le {D : Dec} {p : SPhase} (hrel : DRel D p) (hsi : SInv p) : dpot p D ≤ 95741 := by
  cases p with
  | hdr w st last mlen g q =>
    obtain ⟨_, _, _, _, _, _, hh, _⟩ := hrel
    have := hpot_le hh hsi.2.1 hsi.2.2
    show hpot g q + hdrEnd + 0 ≤ _
    unfold hdrEnd cmdsEnd roundCost
    omega
  | cmds w last m q =>
    have := cpot_le q
    show cpot q + cmdsEnd + 0 ≤ _
    unfold cmdsEnd roundCost
    omega
  | mblock w st =>
    simp only [dpot, spot, roundCost]
    split <;> omega
  | wbits => simp [dpot, spot]
  | skip => simp [dpot, spot, tailEnd, roundCost]
  | raw => simp [dpot, spot, tailEnd, roundCost]
  | ended => simp [dpot, spot]

/-- The most a call can leave for the next to use: the potential of where it pauses, and 4470 for each bit it holds. -/
def psiMax : Nat := 381821

theorem Reaches.withWork {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) :
    ∃ W n, ReachesW limit x R W n := by
  induction h with
  | start => exact ⟨0, 0, .start⟩
  | call _ ha ih =>
    obtain ⟨W, n, hW⟩ := ih
    exact ⟨_, _, .call hW ha⟩

/-- The potential a running decoder holds is at most `psiMax`. -/
theorem decoder_potential {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R)
    (hs : R.status.stopped = false) :
    ∃ p, DRel R.state.val p ∧ SInv p ∧ dpot p R.state.val + 4470 * R.state.val.held.length ≤ psiMax := by
  obtain ⟨W, n, hW⟩ := h.withWork
  obtain ⟨p, hrel, hsi, -, -, -⟩ := (work_inv hW).1 hs
  have := dpot_le hrel hsi
  have := Nat.mul_le_mul_left 4470 hrel.held_le
  exact ⟨p, hrel, hsi, by unfold psiMax; omega⟩

/-- The work bound for one call. A call's work, in the work model, is at most the potential it starts with, at most
`psiMax`, and 35761 for each byte it uses, 284 for each byte it hands out, one for each byte of the window the stream
declares and 272 more for zero-filling it, and 408. -/
theorem decoder_callWork {limit : Nat} {x : List UInt8} {R : Run DState} {c : Call} (h : Reaches decoder limit x R)
    (ha : R.Allowed x c) :
    callWork R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final ≤
      psiMax + 35761 * (R.reply decoder x c).used + 284 * ((R.reply decoder x c).output.size - c.buf.length) +
        (declaredWindow x + 272) + 408 := by
  obtain ⟨W, n, hW⟩ := h.withWork
  obtain ⟨p, hrel, hsi, hk, -, -⟩ := (work_inv hW).1 ha.running
  have hG := (call_pays (x := x) (R := R) (c := c) ha.inside ha.fits hrel hsi hk).2
  have hwin := callWin_le h ha
  have := dpot_le hrel hsi
  have := Nat.mul_le_mul_left 4470 hrel.held_le
  unfold psiMax
  omega

/-- The work bound. The work of a run's calls, in the work model, is at most 35761 for each byte they use, 284 for each
byte they hand out, one for each byte of the window the stream declares and 272 more for zero-filling it, 408 for each
call, and 408. -/
theorem decoder_work {limit : Nat} {x : List UInt8} {R : Run DState} {W n : Nat} (h : ReachesW limit x R W n) :
    W ≤ 35761 * R.read + 284 * R.emitted.length + (declaredWindow x + 272) + 408 * n + 408 := by
  obtain ⟨I1, I2⟩ := work_inv h
  cases hst : R.status.stopped with
  | true => exact I2 hst
  | false =>
    obtain ⟨p, -, -, -, hpn, hW⟩ := I1 hst
    have hw : winPaid x R ≤ (declaredWindow x + 272) := by
      unfold winPaid
      split <;> omega
    exact run_now hW hpn hw

end Brotli.Decoder
