import Brotli.Decoder.Progress

/-!
# The decoder's work

The work bound counts the decoder's work in a model of its steps: each step of its loops of steps (the calls of `stepD`,
`stepCmd` and the call's own rounds) counts one. Every other loop in the decoder moves one byte read, decoded or handed
out, or one byte of a table it allocates, per round, so the bytes a call reads, decodes, hands out and allocates count the
rest.

A step that goes on takes at least one step of the spec's reading in order, which takes at most a constant number of
steps for each bit it reads and each byte it produces. So a call's steps are at most a constant times the bytes it reads
and decodes, plus a constant.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The model -/

/-- The steps of the command loop. -/
def runCmdSteps (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd) (pos : USize) :
    Nat :=
  if _hn : n = 0 then 1
  else
    let r := stepCmd H k a stop hs st pos
    match r.status with
    | .next => runCmdSteps H k a stop hs (n - USize.ofNat 1) r r.pos + 1
    | _ => 1
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-- The steps of one step of the whole decoder: the command loop's, at a meta-block's commands. -/
def stepDSteps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) : Nat :=
  match D.tag with
  | .cmds => runCmdSteps D.H D.k a stop hs cmdBudget D.cmd D.pos
  | _ => 1

/-- The steps of the decoder's loop. -/
def runDSteps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Nat :=
  if he : D.tag = .ended then 1
  else
    let r := stepD a stop hs D
    if hn : r.status = .next then stepDSteps a stop hs D + runDSteps a stop hs r (h.step he hn)
    else stepDSteps a stop hs D
termination_by (RunArg.mk D h : RunArg a stop hs)
decreasing_by exact ⟨he, hn, rfl⟩

/-- The steps of a call. -/
def callDSteps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (final : Bool) (D : Dec) (h : DInv stop D) (buf : ByteArray)
    (space : Nat) : Nat :=
  runDSteps a stop hs D h +
    if hO : (runD a stop hs D h).status = .needsOutput then
      if (flushD (runD a stop hs D h) buf space).D.cmd.pend = 0 then
        if _hlt : (flushD (runD a stop hs D h) buf space).space < space then
          callDSteps a stop hs final (flushD (runD a stop hs D h) buf space).D (flushD_inv (runD_full hO) buf space)
            (flushD (runD a stop hs D h) buf space).buf (flushD (runD a stop hs D h) buf space).space
        else 0
      else 0
    else 0
termination_by space
decreasing_by exact _hlt

/-! ### Steps of the reading in order -/

theorem lex4_irrefl (x : (Nat × Nat) × (Nat × Nat)) : ¬ Lex4 x x := by
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := x
  simp only [Lex4, LexLt]
  omega

theorem mlt_irrefl (x : Meas) : ¬ MLt x x := by
  obtain ⟨a, b, c⟩ := x
  intro h
  rcases h with h | ⟨_, h⟩
  · omega
  · rcases h with h | ⟨_, h⟩
    · omega
    · exact lex4_irrefl c h

/-- Two places apart take at least one step. -/
theorem Reach.count_pos {P E : Type} {step : P → List Bool → ORes P E} {p q : P} {bs c : List Bool} (h : Reach step p bs q c)
    (hne : ¬ (q = p ∧ c = bs)) : ∃ n, 1 ≤ n ∧ ReachN step n p bs q c := by
  obtain ⟨n, hn⟩ := h.count
  cases hn with
  | refl => exact absurd ⟨rfl, rfl⟩ hne
  | next hs hr => exact ⟨_, by omega, .next hs hr⟩

theorem ReachN.trans {P E : Type} {step : P → List Bool → ORes P E} {n m : Nat} {p q r : P} {a b c : List Bool}
    (h1 : ReachN step n p a q b) (h2 : ReachN step m q b r c) : ReachN step (n + m) p a r c := by
  induction h1 with
  | refl => simpa using h2
  | next hs _ ih =>
    rw [Nat.add_right_comm]
    exact .next hs (ih h2)

/-- The commands' steps counted are the stream's. -/
theorem ReachN.cmds {w : Nat} {last : Bool} {m : MetaBlockHeader} {n : Nat} {p q : Phase} {bs c : List Bool}
    (h : ReachN (cStep w m) n p bs q c) : ReachN sStep n (.cmds w last m p) bs (.cmds w last m q) c := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next (by simp only [sStep, hs]) ih

/-- A step of the command loop that goes on takes at least one step of the reading in order. -/
theorem stepCmd_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st p)
    (hp : pos.toNat ≤ stop.toNat) (hn : (stepCmd H k a stop hs st pos).status = .next) :
    ∃ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' ∧ (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧
      pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧
      ∀ F, ∃ n, 1 ≤ n ∧ ReachN (cStep w m) n p (stateBits st a pos stop F) p'
        (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F) := by
  by_cases hc : ∃ s, p = .command s
  · obtain ⟨s, rfl⟩ := hc
    obtain ⟨ic, hR, h1, h2, h0, hne⟩ := (stepCmd_start (hs := hs) hH hrel hp).1 hn
    refine ⟨.insertCopy s ic, hR, h2, h1, fun F => ⟨1, Nat.le_refl _, .next ?_ (.refl _ _)⟩⟩
    rw [cStep_command _ h0]
    have hsw : ¬ (s.insertCopy.count = 0 ∧ m.insertCopy.n < 2) := fun e => by
      have := hne F
      rw [nextElement_single _ e.1 e.2] at this
      cases this
    rw [nextIn_some hsw (hne F)]
  · have hok := stepCmd_ok (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) (hs := hs) hH hrel hp
    obtain ⟨p', hR, h1, h2, _, hd, _, hj⟩ := hok.next hn
    have hr : (rankC p).1 ≠ 0 := by
      cases p with
      | command s => exact absurd ⟨s, rfl⟩ hc
      | literalSymbol | insertCopy | copyLength | literals | distance | distanceSymbol | copy | word =>
        simp only [rankC]
        omega
    have hlt : LexLt (rankC p') (rankC p) := hd.resolve_left hr
    refine ⟨p', hR, h2, h1, fun F => (hj F).count_pos fun ⟨e1, _⟩ => ?_⟩
    rw [e1] at hlt
    simp only [LexLt] at hlt
    omega

/-- The command loop's steps are at most one more than the steps of the reading in order it takes, up to its result when
it doesn't reject, and up to the state its last step starts from when it does. -/
theorem runCmd_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hH : HdrRel H m) : ∀ (N : Nat) (n : USize) (st : Cmd) (p : Phase) (pos : USize), n.toNat = N → Rel w k.toNat m st p →
      pos.toNat ≤ stop.toNat → ∀ F, ∃ c q st' pos', Rel w k.toNat m st' q ∧ pos.toNat ≤ pos'.toNat ∧ pos'.toNat ≤ stop.toNat ∧
        ReachN (cStep w m) c p (stateBits st a pos stop F) q (stateBits st' a pos' stop F) ∧ runCmdSteps H k a stop hs n st pos ≤ c + 1 ∧
        ((runCmd H k a stop hs n st pos).status ≠ .bad → st' = runCmd H k a stop hs n st pos ∧ pos' = (runCmd H k a stop hs n st pos).pos) ∧
        ((runCmd H k a stop hs n st pos).status = .done → ∃ s, q = .command s ∧ s.remaining = 0) ∧
        ((runCmd H k a stop hs n st pos).status = .next → n ≠ 0 → 1 ≤ c) := by
  intro N
  induction N with
  | zero =>
    intro n st p pos hN hrel hp F
    have hz : n = 0 := usize_zero hN
    have e : runCmd H k a stop hs n st pos = markStep st pos .next := by rw [runCmd, dite_eq_left hz]
    rw [e]
    refine ⟨0, p, markStep st pos .next, pos, hrel.mark _ _, Nat.le_refl _, hp, .refl _ _, ?_, fun _ => ⟨rfl, rfl⟩,
      fun h => StepStatus.noConfusion h, fun _ h => absurd hz h⟩
    rw [runCmdSteps, dite_eq_left hz]
    omega
  | succ N ih =>
    intro n st p pos hN hrel hp F
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hok := stepCmd_ok (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) (hs := hs) hH hrel hp
    have hsteps : runCmdSteps H k a stop hs n st pos = match (stepCmd H k a stop hs st pos).status with
        | .next => runCmdSteps H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos + 1
        | _ => 1 := by
      rw [runCmdSteps, dite_eq_right hn]
    have hrun : runCmd H k a stop hs n st pos = match (stepCmd H k a stop hs st pos).status with
        | .next => runCmd H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos
        | _ => stepCmd H k a stop hs st pos := by
      rw [runCmd, dite_eq_right hn]
      rfl
    rw [hsteps, hrun]
    cases hst : (stepCmd H k a stop hs st pos).status
    case next =>
      obtain ⟨p1, hR1, h1, h2, hc1⟩ := stepCmd_count (hs := hs) hH hrel hp hst
      obtain ⟨n1, hn1, hr1⟩ := hc1 F
      obtain ⟨c2, q, st', pos', hq, g1, g2, hr2, g3, g4, g5, _⟩ := ih (n - USize.ofNat 1) _ p1 _ (by omega) hR1 h1 F
      refine ⟨n1 + c2, q, st', pos', hq, by omega, g2, hr1.trans hr2, ?_, g4, g5, fun _ _ => by omega⟩
      show runCmdSteps H k a stop hs (n - USize.ofNat 1) (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos + 1 ≤ _
      omega
    case needsInput =>
      obtain ⟨b1, _, p', hR', _, _, _, _, hj, _⟩ := hok.needsInput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      refine ⟨c0, p', _, _, hR', by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, hc0, by show 1 ≤ _; omega,
        fun _ => ⟨rfl, rfl⟩, (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩
    case needsOutput =>
      obtain ⟨p', hR', b1, b2, _, _, _, _, hj⟩ := hok.needsOutput hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      exact ⟨c0, p', _, _, hR', b1, b2, hc0, by show 1 ≤ _; omega, fun _ => ⟨rfl, rfl⟩,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩
    case done =>
      obtain ⟨s, hR', b1, b2, _, h0, _, hj⟩ := hok.done hst
      obtain ⟨c0, hc0⟩ := (hj F).count
      exact ⟨c0, .command s, _, _, hR', b1, b2, hc0, by show 1 ≤ _; omega, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨s, rfl, h0⟩,
        (fun h => absurd (hst.symm.trans h) (by decide))⟩
    case bad =>
      exact ⟨0, p, st, pos, hrel, Nat.le_refl _, hp, .refl _ _, Nat.le_refl _, fun e => absurd hst e,
        (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩

/-- A stream step outside the commands that goes on moves to another place. -/
theorem sdown_ne {p p' : SPhase} (h : SDown p p') (hc : ∀ w l m q, p ≠ .cmds w l m q) (he : ∀ st, p ≠ .ended st) : p' ≠ p := by
  intro e
  rw [e] at h
  cases p with
  | hdr w st l ml g q =>
    have h' : HDown q q := h
    unfold HDown LexLt at h'
    omega
  | skip w st l n =>
    simp only [SDown] at h
    omega
  | raw w st l n =>
    simp only [SDown] at h
    omega
  | wbits => exact h
  | mblock => exact h
  | cmds w l m q => exact absurd rfl (hc w l m q)
  | ended st => exact absurd rfl (he st)

/-- The facts a stream step's count gives: an end state and place, the steps of the reading in order up to them, and what
the end state is when the step goes on or pauses. -/
def DCount (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (t : List UInt8) (steps : Nat) (r : Dec) : Prop :=
  ∃ c q D', DRel D' q ∧ D.pos.toNat ≤ D'.pos.toNat ∧ D'.pos.toNat ≤ stop.toNat ∧
    ReachN sStep c p (D.bits a D.pos stop (bits t)) q (D'.bits a D'.pos stop (bits t)) ∧ steps ≤ c + 1 ∧
    (r.status = .next → D' = r ∧ 1 ≤ c) ∧ (r.status = .needsInput → D' = r) ∧ (r.status = .needsOutput → D' = r)

/-- A stream step outside the commands is one step, and takes at least one of the reading in order if it goes on. -/
theorem stepD_count_other {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} (hrel : DRel D p)
    (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) (hc : ∀ w l m q, p ≠ .cmds w l m q) (t : List UInt8) :
    DCount a stop p D t 1 (stepD a stop hs D) := by
  have hok := stepD_ok specSem (a := a) (hs := hs) hrel he hp
  have hen : ∀ st, p ≠ .ended st := hrel.tag_ne he
  cases hst : (stepD a stop hs D).status with
  | next =>
    obtain ⟨p', hR, h1, h2, _, hsd, _, hj⟩ := hok.next hst
    obtain ⟨n, hn1, hr⟩ := (hj t).count_pos fun ⟨e1, _⟩ => sdown_ne hsd hc hen e1
    exact ⟨n, p', _, hR, h1, h2, hr, by omega, fun _ => ⟨rfl, hn1⟩, (fun h => absurd (hst.symm.trans h) (by decide)),
      (fun h => absurd (hst.symm.trans h) (by decide))⟩
  | needsInput =>
    obtain ⟨b1, b2, p', hR, _, _, _, _, _, hj, _⟩ := hok.needsInput hst
    obtain ⟨n, hr⟩ := (hj t).count
    exact ⟨n, p', _, hR, by rw [b1]; exact b2, by rw [b1]; exact Nat.le_refl _, hr, by omega,
      (fun h => absurd (hst.symm.trans h) (by decide)), (fun _ => rfl), (fun h => absurd (hst.symm.trans h) (by decide))⟩
  | needsOutput =>
    obtain ⟨p', hR, h1, h2, _, _, _, _, _, hj⟩ := hok.needsOutput hst
    obtain ⟨n, hr⟩ := (hj t).count
    exact ⟨n, p', _, hR, h1, h2, hr, by omega, (fun h => absurd (hst.symm.trans h) (by decide)),
      (fun h => absurd (hst.symm.trans h) (by decide)), (fun _ => rfl)⟩
  | bad =>
    exact ⟨0, p, D, hrel, Nat.le_refl _, hp, .refl _ _, Nat.le_refl _, (fun h => absurd (hst.symm.trans h) (by decide)),
      (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩
  | memory =>
    exact ⟨0, p, D, hrel, Nat.le_refl _, hp, .refl _ _, Nat.le_refl _, (fun h => absurd (hst.symm.trans h) (by decide)),
      (fun h => absurd (hst.symm.trans h) (by decide)), (fun h => absurd (hst.symm.trans h) (by decide))⟩

private theorem cmdBudget_ne' : cmdBudget ≠ 0 := by
  intro e
  have h : cmdBudget.toNat = 65536 := usize_ofNat' (by decide)
  rw [e] at h
  cases h

/-- A meta-block's commands as a stream step: the command loop's steps, against the reading in order. -/
theorem stepDCmds_count {w : Nat} {last : Bool} {m : MetaBlockHeader} {q0 : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} (hrel : DRel D (.cmds w last m q0)) (hp : D.pos.toNat ≤ stop.toNat) (t : List UInt8) :
    DCount a stop (.cmds w last m q0) D t (runCmdSteps D.H D.k a stop hs cmdBudget D.cmd D.pos) (stepDCmds a stop hs D D.pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  obtain ⟨c, q, st', pos'', hq, g1, g2, hr, g3, g4, g5, g6⟩ :=
    runCmd_count (w := w) (hs := hs) hH _ cmdBudget cmd q0 pos' rfl hR hp (bits t)
  have hr' := ReachN.cmds (last := last') hr
  dsimp only at g3 hr' ⊢
  unfold stepDCmds
  dsimp only
  generalize runCmd H k a stop hs cmdBudget cmd pos' = rc at g4 g5 g6
  cases hst : rc.status with
  | next =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    exact ⟨c, .cmds w last' m q,
      { clearCmd ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ with cmd := st', pos := st'.pos, status := .next },
      ⟨rfl, rfl, hlim, hH, hq⟩, g1, g2, hr', g3, fun _ => ⟨rfl, g6 hst cmdBudget_ne'⟩,
      (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h)⟩
  | needsInput =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    exact ⟨c, .cmds w last' m q,
      { clearCmd ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ with cmd := st', pos := st'.pos, status := .needsInput },
      ⟨rfl, rfl, hlim, hH, hq⟩, g1, g2, hr', g3, (fun h => DStatus.noConfusion h), (fun _ => rfl), (fun h => DStatus.noConfusion h)⟩
  | needsOutput =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    exact ⟨c, .cmds w last' m q,
      { clearCmd ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ with cmd := st', pos := st'.pos, status := .needsOutput },
      ⟨rfl, rfl, hlim, hH, hq⟩, g1, g2, hr', g3, (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h), (fun _ => rfl)⟩
  | bad =>
    exact ⟨c, .cmds w last' m q,
      { clearCmd ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ with cmd := st', pos := pos'', status := .bad },
      ⟨rfl, rfl, hlim, hH, hq⟩, g1, g2, hr', g3, (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h),
      (fun h => DStatus.noConfusion h)⟩
  | done =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    obtain ⟨s, rfl, h0⟩ := g5 hst
    have hcheck := seenOk_iff hH hq
    have hq' := hq
    obtain ⟨hC, htg, hprod⟩ := hq'
    have hwin := hC.toWin
    by_cases hsee : seenOk st'.seen H.nL H.nI H.nD = true
    · show DCount a stop _ _ t _ (if seenOk st'.seen H.nL H.nI H.nD then _ else _)
      rw [ite_eq_left hsee]
      rw [hcheck] at hsee
      have hstep := sStep_cmds_end (w := w) (last := last') (m := m) (stateBits st' a st'.pos stop (bits t)) h0 hsee
      have hr2 : ReachN sStep (c + 1) _ _ _ _ := hr'.trans (.next hstep (.refl _ _))
      cases last' with
      | true =>
        exact ⟨c + 1, .ended ⟨s.output, s.produced, s.distances⟩,
          { clearCmd ⟨.cmds, cmd, hd, H, k, true, left, limit, pos', status⟩ with
            cmd := st', pos := st'.pos, status := .next, tag := if true then .ended else .mblock, H := Hdr.none },
          ⟨rfl, hC.wf, w, ⟨hwin, hprod, hlim⟩⟩, g1, g2, hr2, by omega,
          fun _ => ⟨rfl, by omega⟩, (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h)⟩
      | false =>
        exact ⟨c + 1, .mblock w ⟨s.output, s.produced, s.distances⟩,
          { clearCmd ⟨.cmds, cmd, hd, H, k, false, left, limit, pos', status⟩ with
            cmd := st', pos := st'.pos, status := .next, tag := if false then .ended else .mblock, H := Hdr.none },
          ⟨rfl, hC.wf, ⟨hwin, hprod, hlim⟩⟩, g1, g2, hr2, by omega,
          fun _ => ⟨rfl, by omega⟩, (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h)⟩
    · show DCount a stop _ _ t _ (if seenOk st'.seen H.nL H.nI H.nD then _ else _)
      rw [ite_eq_right hsee]
      exact ⟨c, .cmds w last' m (.command s),
        { clearCmd ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ with cmd := st', pos := st'.pos, status := .bad },
        ⟨rfl, rfl, hlim, hH, hq⟩, g1, g2, hr', g3,
        (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h), (fun h => DStatus.noConfusion h)⟩

end Brotli.Decoder
