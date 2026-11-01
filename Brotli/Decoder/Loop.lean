import Brotli.Decoder.StepDistance

/-!
# The command loop

`stepCmd` refills the bit buffer and takes the step for the place the state is at. `stepCmd_ok` is the bridge for the
command loop: under `Rel`, every step keeps the state tied to `rest`, for every future. `runCmd` repeats steps until one
pauses or finishes, and `flushCmd` hands bytes waiting in the window to the caller.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The step for the place a state is at, its buffer refilled. -/
def stepAt (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Cmd :=
  match st.tag with
  | .command => stepCommand H st pos
  | .insertCopy => stepInsertCopy H st pos
  | .copyLength => stepCopyLength st pos
  | .literals => stepLiterals H k a stop hs st pos
  | .distance => stepDistance H st pos
  | .distanceSymbol => stepDistanceSymbol H st pos
  | .copy => stepCopy k st pos
  | .word => stepWord k st pos

/-- One step of the command loop. -/
def stepCmd (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Cmd :=
  if hp : pos ≤ stop then
    let r := refill st.word st.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    stepAt H k a stop hs { st with word := rw, count := rc } rp
  else markStep st pos .bad

/-- The bit buffer's fields don't matter to `Rel`, beyond being well formed. -/
theorem Rel.withBits {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) {word count : UInt64}
    (hw : (BitBuffer.mk word count).Wf) : Rel w k m { st with word := word, count := count } p := by
  cases p with
  | literalSymbol => exact h.elim
  | command =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | insertCopy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | copyLength =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | literals =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | distance =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | distanceSymbol =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | copy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩
  | word =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with wf := hw }, hr⟩

/-- A state's buffer is well formed, whatever place it stands for. -/
theorem Rel.wf {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) :
    (BitBuffer.mk st.word st.count).Wf := by
  cases p with
  | literalSymbol => exact h.elim
  | command => exact h.1.wf
  | insertCopy => exact h.1.wf
  | copyLength => exact h.1.wf
  | literals => exact h.1.wf
  | distance => exact h.1.wf
  | distanceSymbol => exact h.1.wf
  | copy => exact h.1.wf
  | word => exact h.1.wf

/-- The step for a place does its job. -/
theorem stepAt_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k.toNat m K a stop p st pos (stepAt H k a stop hs st pos) := by
  unfold stepAt
  cases p with
  | literalSymbol => exact hrel.elim
  | command =>
    rw [hrel.2.1]
    exact stepCommand_ok hK hH hrel hp hfull
  | insertCopy =>
    rw [hrel.2.1]
    exact stepInsertCopy_ok hH hrel hp hfull
  | copyLength =>
    rw [hrel.2.1]
    exact stepCopyLength_ok hrel hp hfull
  | literals =>
    rw [hrel.2.1]
    exact stepLiterals_ok hH hrel hp hfull
  | distance =>
    rw [hrel.2.1]
    exact stepDistance_ok hH hrel hp hfull
  | distanceSymbol =>
    rw [hrel.2.1]
    exact stepDistanceSymbol_ok hH hrel hp hfull
  | copy =>
    rw [hrel.2.1]
    exact stepCopy_ok hrel hp
  | word =>
    rw [hrel.2.1]
    exact stepWord_ok hrel hp

/-- The bridge for the command loop: from a state that stands for a place in `rest`, every step moves on to a state that
stands for a place with the same future, pauses, finishes, or rejects with the spec. -/
theorem stepCmd_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m K a stop p st pos (stepCmd H k a stop hs st pos) := by
  unfold stepCmd
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hp)]
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  dsimp only
  refine (stepAt_ok hK hH (hrel.withBits h1) h3 h5).refilled (fun F => ?_) h2 h3 rfl
  show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
    (refill st.word st.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F)
  rw [← List.append_assoc, ← List.append_assoc, h4]

/-- A step away from a command's start needs nothing of what follows the command. -/
theorem stepCmd_inside {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize}
    (hne : ∀ s, p ≠ .command s) (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m K a stop p st pos (stepCmd H k a stop hs st pos) := by
  unfold stepCmd
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hp)]
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  dsimp only
  have hat : ∀ {st1 : Cmd} {pos1 : USize}, Rel w k.toNat m st1 p → pos1.toNat ≤ stop.toNat → (56 < st1.count.toNat ∨ pos1 = stop) →
      StepOk w k.toNat m K a stop p st1 pos1 (stepAt H k a stop hs st1 pos1) := by
    intro st1 pos1 hrel1 hp1 hfull
    unfold stepAt
    cases p with
    | literalSymbol => exact hrel1.elim
    | command s => exact absurd rfl (hne s)
    | insertCopy =>
      rw [hrel1.2.1]
      exact stepInsertCopy_ok hH hrel1 hp1 hfull
    | copyLength =>
      rw [hrel1.2.1]
      exact stepCopyLength_ok hrel1 hp1 hfull
    | literals =>
      rw [hrel1.2.1]
      exact stepLiterals_ok hH hrel1 hp1 hfull
    | distance =>
      rw [hrel1.2.1]
      exact stepDistance_ok hH hrel1 hp1 hfull
    | distanceSymbol =>
      rw [hrel1.2.1]
      exact stepDistanceSymbol_ok hH hrel1 hp1 hfull
    | copy =>
      rw [hrel1.2.1]
      exact stepCopy_ok hrel1 hp1
    | word =>
      rw [hrel1.2.1]
      exact stepWord_ok hrel1 hp1
  refine (hat (hrel.withBits h1) h3 h5).refilled (fun F => ?_) h2 h3 rfl
  show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
    (refill st.word st.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F)
  rw [← List.append_assoc, ← List.append_assoc, h4]

/-- A step from a command's start, in terms of its block switch. -/
theorem stepCmd_start {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {s : CommandState} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st (.command s)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepCmd H k a stop hs st pos).status = .next → ∃ ic, Rel w k.toNat m (stepCmd H k a stop hs st pos) (.insertCopy s ic) ∧
      pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧ (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧ s.remaining ≠ 0 ∧
      ∀ F, nextElement m.insertCopy s.insertCopy (stateBits st a pos stop F) =
        some (ic, stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F)) ∧
    ((stepCmd H k a stop hs st pos).status = .needsInput → Rel w k.toNat m (stepCmd H k a stop hs st pos) (.command s) ∧ (stepCmd H k a stop hs st pos).pend = st.pend ∧
      ∀ F, stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F = stateBits st a pos stop F) ∧
    ((stepCmd H k a stop hs st pos).status = .done → Rel w k.toNat m (stepCmd H k a stop hs st pos) (.command s) ∧ s.remaining = 0 ∧
      ∀ F, stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F = stateBits st a pos stop F) ∧
    (stepCmd H k a stop hs st pos).status ≠ .needsOutput := by
  unfold stepCmd
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hp)]
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  dsimp only
  have hrel1 := hrel.withBits h1
  have hb : ∀ F, stateBits { st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count } a
      (refill st.word st.count a pos stop hs hp).pos stop F = stateBits st a pos stop F := by
    intro F
    show (refill st.word st.count a pos stop hs hp).buf.held ++ (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F) =
      (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, h4]
  have hpe : ({ st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count } : Cmd).pend = st.pend := rfl
  generalize ({ st with word := (refill st.word st.count a pos stop hs hp).word, count := (refill st.word st.count a pos stop hs hp).count } : Cmd) = st1 at hrel1 hb hpe ⊢
  have hat : stepAt H k a stop hs st1 (refill st.word st.count a pos stop hs hp).pos = stepCommand H st1 (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepAt
    rw [hrel1.2.1]
  rw [hat]
  obtain ⟨c1, c2, c3, c4⟩ := stepCommand_cases (a := a) (stop := stop) (pos := (refill st.word st.count a pos stop hs hp).pos) hH hrel1
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, c4⟩
  · obtain ⟨ic, r1, r2, r3, r4⟩ := c1 e
    refine ⟨ic, r1, by rw [r2]; exact h2, by rw [r2]; exact h3, r3, fun F => ?_⟩
    rw [← hb F, r4 F]
  · rw [c2 e]
    exact ⟨hrel1.mark _ _, hpe, hb⟩
  · obtain ⟨e1, e2⟩ := c3 e
    rw [e1]
    exact ⟨hrel1.mark _ _, e2, hb⟩

/-- Steps until one pauses or finishes, or `n` have been taken. -/
def runCmd (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd) (pos : USize) : Cmd :=
  if _hn : n = 0 then markStep st pos .next
  else
    let r := stepCmd H k a stop hs st pos
    match r.status with
    | .next => runCmd H k a stop hs (n - USize.ofNat 1) r r.pos
    | _ => r
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-- What steps together must do: what `StepOk` asks of one, apart from how far down the places go. -/
structure RunOk {α : Type} (w k : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (r : Cmd) : Prop where
  next : r.status = .next → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧ OutStep p p' st r
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', Rel w k m r p' ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    rest w m K p' (BitBuffer.mk r.word r.count).held = none ∧ OutStep p p' st r
  needsOutput : r.status = .needsOutput → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    r.pend.toNat = 2 ^ k ∧ OutStep p p' st r
  done : r.status = .done → ∃ s, Rel w k m r (.command s) ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K (.command s) (stateBits r a r.pos stop F)) ∧
    s.remaining = 0 ∧ OutStep p (.command s) st r
  bad : r.status = .bad → ∀ F, rest w m K p (stateBits st a pos stop F) = none

/-- Two moves' bytes together. -/
theorem OutStep.trans {p p1 p2 : Phase} {st r1 r : Cmd} (h1 : OutStep p p1 st r1) (h2 : OutStep p1 p2 r1 r) : OutStep p p2 st r := by
  obtain ⟨l1, a1, b1⟩ := h1
  obtain ⟨l2, a2, b2⟩ := h2
  refine ⟨l2 ++ l1, by rw [a2, a1, List.append_assoc], ?_⟩
  rw [b2, b1, List.length_append]
  omega

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize}
  {p : Phase} {st : Cmd} {pos : USize} {r : Cmd}

/-- One step is a run. -/
theorem StepOk.toRun (h : StepOk w k m K a stop p st pos r) : RunOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', h1, h2, h3, h4, _, h5⟩ := h.next e
    exact ⟨p', h1, h2, h3, h4, h5⟩
  needsInput e := by
    obtain ⟨h1, h2, p', h3, h4, h5, _, h6⟩ := h.needsInput e
    exact ⟨h1, h2, p', h3, h4, h5, h6⟩
  needsOutput e := by
    obtain ⟨p', h1, h2, h3, h4, h5, _, h6⟩ := h.needsOutput e
    exact ⟨p', h1, h2, h3, h4, h5, h6⟩
  done := h.done
  bad := h.bad

/-- Two runs in a row, the first moving on, are one run. -/
theorem RunOk.trans {r1 : Cmd} {p1 : Phase} (hle : pos.toNat ≤ r1.pos.toNat)
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p1 (stateBits r1 a r1.pos stop F)) (ho : OutStep p p1 st r1)
    (h2 : RunOk w k m K a stop p1 r1 r1.pos r) : RunOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', hrel, h3, h4, h5, h6⟩ := h2.next e
    exact ⟨p', hrel, Nat.le_trans hle h3, h4, (fun F => by rw [h]; exact h5 F), ho.trans h6⟩
  needsInput e := by
    obtain ⟨h3, h6, p', hrel, h5, h7, h8⟩ := h2.needsInput e
    exact ⟨h3, Nat.le_trans hle h6, p', hrel, (fun F => by rw [h]; exact h5 F), h7, ho.trans h8⟩
  needsOutput e := by
    obtain ⟨p', hrel, h3, h4, h5, h6, h7⟩ := h2.needsOutput e
    exact ⟨p', hrel, Nat.le_trans hle h3, h4, (fun F => by rw [h]; exact h5 F), h6, ho.trans h7⟩
  done e := by
    obtain ⟨s, hrel, h3, h4, h5, h6, h7⟩ := h2.done e
    exact ⟨s, hrel, Nat.le_trans hle h3, h4, (fun F => by rw [h]; exact h5 F), h6, ho.trans h7⟩
  bad e := fun F => by rw [h]; exact h2.bad e F

end

/-- Any number of steps together does what one step must. -/
theorem runCmd_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m) :
    ∀ (N : Nat) (n : USize) (p : Phase) (st : Cmd) (pos : USize), n.toNat = N → Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      RunOk w k.toNat m K a stop p st pos (runCmd H k a stop hs n st pos) := by
  intro N
  induction N with
  | zero =>
    intro n p st pos hN hrel hp
    rw [runCmd, dite_eq_left (usize_zero hN)]
    exact ⟨fun _ => ⟨p, hrel.mark _ _, Nat.le_refl _, hp, (fun _ => rfl), ⟨[], rfl, rfl⟩⟩, fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e,
      fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e⟩
  | succ N ih =>
    intro n p st pos hN hrel hp
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hstep := stepCmd_ok (hs := hs) (K := K) (a := a) hK hH hrel hp
    rw [runCmd, dite_eq_right hn]
    dsimp only
    generalize stepCmd H k a stop hs st pos = r at hstep
    cases hst : r.status with
    | next =>
      obtain ⟨p', hR, h1, h2, h3, _, h4⟩ := hstep.next hst
      exact RunOk.trans h1 h3 h4 (ih _ p' r r.pos (by omega) hR h2)
    | needsInput => exact hstep.toRun
    | needsOutput => exact hstep.toRun
    | done => exact hstep.toRun
    | bad => exact hstep.toRun

/-- `stepCmd_ok` for the spec's own commands. -/
theorem stepCmd_commands {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st p)
    (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m (commandsFrom w m) a stop p st pos (stepCmd H k a stop hs st pos) :=
  stepCmd_ok (fun _ bs h0 => commandsFrom_step bs h0) hH hrel hp

/-! ### Handing bytes out -/

/-- What flushing returns. -/
structure Flushed where
  st : Cmd
  buf : ByteArray

/-- Adds up to `space` bytes waiting in the window to the caller's buffer, stopping where the ring wraps. -/
def flushCmd (k : USize) (st : Cmd) (buf : ByteArray) (space : USize) : Flushed :=
  if st.pend = 0 ∨ space = 0 then ⟨st, buf⟩
  else
    let start := ringBack st.wpos st.pend (ringMask k) (ringSize k)
    let len := usmin (usmin st.pend space) (ringSize k - start)
    ⟨{ st with pend := st.pend - len }, emitRun st.ring buf start.toNat len.toNat⟩

/-- Fewer bytes waiting keeps a state's place. -/
theorem Rel.withPend {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) {x : USize}
    (hx : x.toNat ≤ st.pend.toNat) : Rel w k m { st with pend := x } p := by
  have up : ∀ {out rem ds ic lit dist}, Core w k m st out rem ds ic lit dist →
      Core w k m { st with pend := x } out rem ds ic lit dist := by
    intro out rem ds ic lit dist hC
    have h1 := hC.pendLe
    have h2 := hC.pendOut
    exact { hC with pendLe := Nat.le_trans hx h1, pendOut := Nat.le_trans hx h2 }
  cases p with
  | literalSymbol => exact h.elim
  | command =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | insertCopy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | copyLength =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | literals =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | distance =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | distanceSymbol =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | copy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩
  | word =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨up hC, hr⟩

/-- A state's window and waiting bytes, for the bytes its place has produced. -/
theorem Rel.window {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) :
    RingOk st.ring k st.wpos.toNat p.out ∧ st.pend.toNat ≤ 2 ^ k ∧ st.pend.toNat ≤ p.out.length ∧ k ≤ 24 := by
  cases p with
  | literalSymbol => exact h.elim
  | command => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | insertCopy => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | copyLength => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | literals => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | distance => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | distanceSymbol => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | copy => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩
  | word => exact ⟨h.1.ring, h.1.pendLe, h.1.pendOut, h.1.k24⟩

/-- What a state's place says of its arrays. -/
theorem Rel.arrays {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) :
    st.ring.size = 2 ^ k ∧ k ≤ 24 ∧ st.seen.size ≤ 768 ∧ st.wordBuf.size ≤ 38 := by
  cases p with
  | literalSymbol => exact h.elim
  | command => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | insertCopy => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | copyLength => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | literals => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | distance => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | distanceSymbol => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | copy => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩
  | word => exact ⟨h.1.ring.size, h.1.k24, Nat.le_of_eq h.1.seenSize, h.1.wordLe⟩

/-- Flushing keeps the state's place, adds the next bytes waiting to the buffer, oldest first, and takes them off those
waiting. It adds at least one byte when one is waiting and there is space. -/
theorem flushCmd_spec {k : USize} {st : Cmd} {out : List Nat} {buf : ByteArray} {space : USize}
    (hring : RingOk st.ring k.toNat st.wpos.toNat out) (hle : st.pend.toNat ≤ 2 ^ k.toNat) (hout : st.pend.toNat ≤ out.length) (hk : k.toNat ≤ 24) :
    let r := flushCmd k st buf space
    ∃ len, len ≤ space.toNat ∧ len ≤ st.pend.toNat ∧ (st.pend.toNat ≠ 0 → space.toNat ≠ 0 → 1 ≤ len) ∧
      r.st.pend.toNat = st.pend.toNat - len ∧ r.st = { st with pend := r.st.pend } ∧
      r.buf.data.toList.map UInt8.toNat =
        buf.data.toList.map UInt8.toNat ++ ((out.take st.pend.toNat).reverse).take len := by
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k.toNat := Nat.two_pow_pos _
  dsimp only
  unfold flushCmd
  dsimp only
  split
  · rename_i hz
    refine ⟨0, Nat.zero_le _, Nat.zero_le _, ?_, rfl, rfl, by simp⟩
    intro h1 h2
    rcases hz with hz | hz
    · exact absurd (by rw [hz]; rfl) h1
    · exact absurd (by rw [hz]; rfl) h2
  · rename_i hz
    have hp0 : st.pend ≠ 0 := fun e => hz (Or.inl e)
    have hs0 : space ≠ 0 := fun e => hz (Or.inr e)
    have hpN := usize_ne hp0
    have hsN := usize_ne hs0
    have hplt := hring.pos_lt
    have hback : (ringBack st.wpos st.pend (ringMask k) (ringSize k)).toNat = ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat :=
      ringBack_toNat hk (ringMask_toNat hk) (ringSize_toNat hk) hplt (by omega) hle
    have hstart : ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat < 2 ^ k.toNat := by
      unfold ringStart
      exact ringIdx_lt hplt (by omega)
    have hroom : (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k)).toNat =
        2 ^ k.toNat - ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hback, ringSize_toNat hk]; omega)), hback, ringSize_toNat hk]
    have hlenN : (usmin (usmin st.pend space) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat =
        min (min st.pend.toNat space.toNat) (2 ^ k.toNat - ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat) := by
      rw [usmin_toNat, usmin_toNat, hroom]
    have hpn : (st.pend - usmin (usmin st.pend space) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat =
        st.pend.toNat - (usmin (usmin st.pend space) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hlenN]; omega))
    refine ⟨_, by rw [hlenN]; omega, by rw [hlenN]; omega, fun _ _ => by rw [hlenN]; omega, hpn, rfl, ?_⟩
    show (emitRun st.ring buf _ _).data.toList.map UInt8.toNat = _
    rw [emitRun_data _ _ (by rw [hring.size, hback, hlenN]; omega), List.map_append, hback,
      hring.emit_bytes (by omega) hle hout (by rw [hlenN]; omega) (by rw [hlenN]; omega)]

end Brotli.Decoder
