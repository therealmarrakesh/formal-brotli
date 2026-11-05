module

public import Brotli.Decoder.StreamSteps

@[expose] public section

/-!
# The stream's loop

`stepD` is one step of the whole decoder. What makes it stop is a measure over the spec's own places: `lenSem` gives each
place the bits left at the end of its meta-block, which the spec's `readMetaBlock_lt` lowers, and within a meta-block the
header's and the commands' ranks go down. `runD` is the loop, with no fuel, by the well-founded order this gives.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The step -/

/-- A state the loop can run from. -/
def DInv (stop : USize) (D : Dec) : Prop := (∃ p, DRel D p) ∧ D.pos.toNat ≤ stop.toNat

/-- A state in a header stands for a place in it, with room for the tables still to come. -/
theorem DInv.hd {stop : USize} {D : Dec} (h : DInv stop D) (ht : D.tag = .hdr) : HIn D.hd := by
  obtain ⟨⟨p, hrel⟩, _⟩ := h
  cases p with
  | hdr w st last mlen g q => exact ⟨g, q, hrel.2.2.2.2.2.2.1, hrel.2.2.2.2.2.2.2.2⟩
  | _ => exact absurd (hrel.1.symm.trans ht) (fun e => DTag.noConfusion e)

/-- A state in a meta-block's commands gives the compiled command loop what it may assume. -/
theorem DInv.cmd {stop : USize} {D : Dec} (h : DInv stop D) (ht : D.tag = .cmds) : CmdInv D.H D.k stop D.cmd D.pos := by
  obtain ⟨⟨p, hrel⟩, hpos⟩ := h
  cases p with
  | cmds w last m q => exact KInv.of_rel hrel.2.2.2.1 hrel.2.2.2.2 hpos
  | _ => exact absurd (hrel.1.symm.trans ht) (fun e => DTag.noConfusion e)

/-- One step of the whole decoder. -/
def stepD (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Dec :=
  match ht : D.tag with
  | .wbits => stepDWbits a stop hs D D.pos
  | .mblock => stepDMeta a stop hs D D.pos
  | .skip => stepDSkip stop D D.pos
  | .raw => stepDRaw a stop hs D D.pos
  | .hdr => stepDHdr a stop hs D D.pos (h.hd ht) h.2
  | .cmds => stepDCmdsP a stop hs D D.pos (h.cmd ht)
  | .ended => D

section
variable {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {h : DInv stop D}

/-- Settles `stepD`'s tag, given its equation. -/
macro "stepD_tag" ht:ident : tactic =>
  `(tactic| (unfold stepD; split <;> rename_i e <;> first | rfl | exact absurd (e.symm.trans $ht) (fun x => DTag.noConfusion x)))

theorem stepD_wbits (ht : D.tag = .wbits) : stepD a stop hs D h = stepDWbits a stop hs D D.pos := by stepD_tag ht
theorem stepD_mblock (ht : D.tag = .mblock) : stepD a stop hs D h = stepDMeta a stop hs D D.pos := by stepD_tag ht
theorem stepD_skip (ht : D.tag = .skip) : stepD a stop hs D h = stepDSkip stop D D.pos := by stepD_tag ht
theorem stepD_raw (ht : D.tag = .raw) : stepD a stop hs D h = stepDRaw a stop hs D D.pos := by stepD_tag ht
theorem stepD_hdr (ht : D.tag = .hdr) : stepD a stop hs D h = stepDHdr a stop hs D D.pos (h.hd ht) h.2 := by stepD_tag ht
theorem stepD_cmds (ht : D.tag = .cmds) : stepD a stop hs D h = stepDCmds a stop hs D D.pos := by stepD_tag ht
theorem stepD_ended (ht : D.tag = .ended) : stepD a stop hs D h = D := by stepD_tag ht

end

/-- A state's place decides its tag. -/
theorem DRel.tag_ne {D : Dec} {p : SPhase} (h : DRel D p) (he : D.tag ≠ .ended) : ∀ st, p ≠ .ended st := by
  intro st e
  subst e
  exact he h.1

/-- A step does what its place's step does. -/
theorem stepD_ok {α : Type} (S : Sem α) {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} (hrel : DRel D p)
    (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) {h : DInv stop D} : DStepOk S a stop p D D.pos (stepD a stop hs D h) := by
  unfold stepD
  split <;> rename_i ht
  all_goals cases p <;> first
    | exact absurd (hrel.1.symm.trans ht) (fun e => DTag.noConfusion e)
    | exact stepDWbits_ok hrel hp
    | exact stepDMeta_ok hrel hp
    | exact stepDSkip_ok hs hrel hp
    | exact stepDRaw_ok hrel hp
    | exact stepDHdr_ok hrel hp
    | exact stepDCmds_ok hrel hp
    | exact absurd ht he

/-! ### What the measure counts -/

/-- A worth that counts the bits left at the end of a place's meta-block, plus one. -/
def lenSem : Sem Nat where
  after _ _ _ bs := some (bs.length + 1)
  block _ _ bs := some (bs.length + 1)
  finish _ bs := some (bs.length + 1)
  first bs := readWBITS bs >>= fun p => some (p.2.length + 1)
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- What a command is worth to the measure: the bits left at the meta-block's end, then the spec's measure on commands. -/
def cK (w : Nat) (last : Bool) (m : MetaBlockHeader) (s : CommandState) (bs : List Bool) : Option (Nat × Nat) :=
  some ((cmdK w (lenSem.after w last) m s bs).getD 0, commandMeasure s bs + 1)

/-- What a place in the commands is worth to the measure. -/
def cVal (w : Nat) (last : Bool) (m : MetaBlockHeader) (p : Phase) (bs : List Bool) : Nat × Nat :=
  (rest w m (cK w last m) p bs).getD (0, 0)

/-- A place in the commands and its bits, in the measure's terms. -/
def cMeas (w : Nat) (last : Bool) (m : MetaBlockHeader) (p : Phase) (bs : List Bool) : (Nat × Nat) × (Nat × Nat) :=
  (cVal w last m p bs, rankC p)

/-- Lower or the same. -/
def Lex4Eq (a b : (Nat × Nat) × (Nat × Nat)) : Prop := Lex4 a b ∨ a = b

theorem Lex4.trans {a b c : (Nat × Nat) × (Nat × Nat)} (h1 : Lex4 a b) (h2 : Lex4 b c) : Lex4 a c := by
  obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := a
  obtain ⟨⟨b1, b2⟩, ⟨b3, b4⟩⟩ := b
  obtain ⟨⟨c1, c2⟩, ⟨c3, c4⟩⟩ := c
  simp only [Lex4, LexLt, Prod.mk.injEq] at h1 h2 ⊢
  omega

theorem Lex4Eq.trans {a b c : (Nat × Nat) × (Nat × Nat)} (h1 : Lex4Eq a b) (h2 : Lex4Eq b c) : Lex4Eq a c := by
  rcases h1 with h1 | rfl
  · rcases h2 with h2 | rfl
    · exact Or.inl (h1.trans h2)
    · exact Or.inl h1
  · exact h2

theorem Lex4.trans_le {a b c : (Nat × Nat) × (Nat × Nat)} (h1 : Lex4 a b) (h2 : Lex4Eq b c) : Lex4 a c := by
  rcases h2 with h2 | rfl
  · exact h1.trans h2
  · exact h1

theorem Lex4Eq.trans_lt {a b c : (Nat × Nat) × (Nat × Nat)} (h1 : Lex4Eq a b) (h2 : Lex4 b c) : Lex4 a c := by
  rcases h1 with h1 | rfl
  · exact h1.trans h2
  · exact h2

private theorem lex_none (x y : Nat) : LexLt (0, 0) (x, y + 1) := by
  simp only [LexLt]
  omega

private theorem lex_some (x : Nat) {y z : Nat} (h : y < z) : LexLt (x, y + 1) (x, z + 1) :=
  Or.inr ⟨rfl, Nat.succ_lt_succ h⟩

private theorem bind_pair {β : Type} (K : CommandState → List Bool → Option β) (s : CommandState) (b : List Bool) :
    (some (s, b) >>= fun (x : CommandState × List Bool) => match x with | (s1, b1) => K s1 b1) = K s b := rfl

/-- One command lowers what a command is worth. The steps keep `cmdK` and `commandMeasure` closed, because the kernel can't
reduce the multiplication in them. -/
theorem readCommand_cK {w : Nat} {last : Bool} {m : MetaBlockHeader} {s : CommandState} {bs : List Bool} (h0 : s.remaining ≠ 0) :
    LexLt ((readCommand w m s bs >>= fun (s1, b) => cK w last m s1 b).getD (0, 0)) ((cK w last m s bs).getD (0, 0)) := by
  have hstep := cmdK_step (w := w) (A := lenSem.after w last) (m := m) s bs h0
  cases hc : readCommand w m s bs with
  | none => exact lex_none _ _
  | some q =>
    obtain ⟨s1, b⟩ := q
    have hm := readCommand_measure hc
    rw [hc] at hstep
    have h1 := hstep.trans (bind_pair (cmdK w (lenSem.after w last) m) s1 b)
    show LexLt ((cmdK w (lenSem.after w last) m s1 b).getD 0, commandMeasure s1 b + 1) ((cmdK w (lenSem.after w last) m s bs).getD 0, commandMeasure s bs + 1)
    rw [h1]
    exact lex_some _ hm

/-- What steps of the commands do to the measure, with `R` the order moving on follows. -/
structure CDown (R : (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat) → Prop) (w k : Nat) (last : Bool) (m : MetaBlockHeader) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (r : Cmd) : Prop where
  next : r.status = .next → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ F, R (cMeas w last m p' (stateBits r a r.pos stop F)) (cMeas w last m p (stateBits st a pos stop F))
  needsInput : r.status = .needsInput → ∃ p', Rel w k m r p' ∧
    ((∀ F, Lex4 (cMeas w last m p' (stateBits r a r.pos stop F)) (cMeas w last m p (stateBits st a pos stop F))) ∨
      (r.pend = st.pend ∧ ∀ F, cMeas w last m p' (stateBits r a r.pos stop F) = cMeas w last m p (stateBits st a pos stop F)))
  needsOutput : r.status = .needsOutput → ∃ p', Rel w k m r p' ∧
    ((∀ F, Lex4 (cMeas w last m p' (stateBits r a r.pos stop F)) (cMeas w last m p (stateBits st a pos stop F))) ∨
      (r.pend = st.pend ∧ ∀ F, cMeas w last m p' (stateBits r a r.pos stop F) = cMeas w last m p (stateBits st a pos stop F)))
  done : r.status = .done → ∃ s, Rel w k m r (.command s) ∧ s.remaining = 0 ∧
    ∀ F, Lex4Eq (cMeas w last m (.command s) (stateBits r a r.pos stop F)) (cMeas w last m p (stateBits st a pos stop F))

/-- Moves on, then pauses: the measure is lower than it was. -/
private theorem pause_after {R : (Nat × Nat) × (Nat × Nat) → (Nat × Nat) × (Nat × Nat) → Prop} {A B C : List Bool → (Nat × Nat) × (Nat × Nat)} {x y : USize}
    (hR : ∀ {u v w}, R u v → Lex4 v w → Lex4 u w) (h2 : ∀ F, Lex4 (B F) (C F))
    (h1 : (∀ F, R (A F) (B F)) ∨ (x = y ∧ ∀ F, A F = B F)) :
    (∀ F, Lex4 (A F) (C F)) := by
  rcases h1 with h | ⟨_, h⟩
  · exact fun F => hR (h F) (h2 F)
  · intro F
    rw [h F]
    exact h2 F

/-- Only a command's start has rank zero. -/
private theorem rank_ne {p : Phase} (hrel : ∀ s, p ≠ .command s) : (rankC p).1 ≠ 0 := by
  cases p with
  | command s => exact absurd rfl (hrel s)
  | literalSymbol | insertCopy | copyLength | literals | distance | distanceSymbol | copy | word =>
    simp only [rankC]
    omega

/-- One step of the commands lowers the measure. -/
theorem stepCmd_down {w : Nat} {k : USize} {last : Bool} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {p : Phase} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) :
    CDown Lex4 w k.toNat last m a stop p st pos (stepCmd H k a stop hs st pos) := by
  by_cases hc : ∃ s, p = .command s
  · obtain ⟨s, rfl⟩ := hc
    obtain ⟨c1, c2, c3, c4⟩ := stepCmd_start (a := a) (stop := stop) (hs := hs) hH hrel hp
    generalize stepCmd H k a stop hs st pos = r at c1 c2 c3 c4 ⊢
    refine ⟨fun e => ?_, fun e => ?_, fun e => absurd e c4, fun e => ?_⟩
    · obtain ⟨ic, r1, r2, r3, r4, r5⟩ := c1 e
      refine ⟨.insertCopy s ic, r1, r2, r3, fun F => Or.inl ?_⟩
      have h := readCommand_cK (w := w) (last := last) (m := m) (s := s) (bs := stateBits st a pos stop F) r4
      rw [readCommand_rest, r5 F] at h
      exact h
    · obtain ⟨r1, r0, r2⟩ := c2 e
      exact ⟨.command s, r1, Or.inr ⟨r0, fun F => by rw [r2 F]⟩⟩
    · obtain ⟨r1, r2, r3⟩ := c3 e
      exact ⟨s, r1, r2, fun F => Or.inr (by rw [r3 F])⟩
  · have hne : ∀ s, p ≠ .command s := fun s e => hc ⟨s, e⟩
    have hstep := stepCmd_inside (K := cK w last m) (a := a) (stop := stop) (hs := hs) hne hH hrel hp
    have hrk := rank_ne hne
    generalize stepCmd H k a stop hs st pos = r at hstep ⊢
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · obtain ⟨p', r1, r2, r3, r4, r5, _⟩ := hstep.next e
      refine ⟨p', r1, r2, r3, fun F => Or.inr ⟨?_, r5.resolve_left hrk⟩⟩
      show (rest w m (cK w last m) p' _).getD (0, 0) = (rest w m (cK w last m) p _).getD (0, 0)
      rw [r4]
    · obtain ⟨_, _, p', r1, r2, _, r3, _⟩ := hstep.needsInput e
      have hv : ∀ F, cVal w last m p' (stateBits r a r.pos stop F) = cVal w last m p (stateBits st a pos stop F) := by
        intro F
        show (rest w m (cK w last m) p' _).getD (0, 0) = (rest w m (cK w last m) p _).getD (0, 0)
        rw [r2]
      refine ⟨p', r1, ?_⟩
      rcases r3 with h | ⟨h1, h2⟩
      · exact Or.inl fun F => Or.inr ⟨hv F, h⟩
      · exact Or.inr ⟨h2, fun F => Prod.ext (hv F) h1⟩
    · obtain ⟨p', r1, _, _, r2, _, r3, _⟩ := hstep.needsOutput e
      have hv : ∀ F, cVal w last m p' (stateBits r a r.pos stop F) = cVal w last m p (stateBits st a pos stop F) := by
        intro F
        show (rest w m (cK w last m) p' _).getD (0, 0) = (rest w m (cK w last m) p _).getD (0, 0)
        rw [r2]
      refine ⟨p', r1, ?_⟩
      rcases r3 with h | ⟨h1, h2⟩
      · exact Or.inl fun F => Or.inr ⟨hv F, h⟩
      · exact Or.inr ⟨h2, fun F => Prod.ext (hv F) h1⟩
    · obtain ⟨s, r1, _, _, r2, r3, _⟩ := hstep.done e
      refine ⟨s, r1, r3, fun F => Or.inl (Or.inr ⟨?_, Or.inl (Nat.pos_of_ne_zero hrk)⟩)⟩
      show (rest w m (cK w last m) (.command s) _).getD (0, 0) = (rest w m (cK w last m) p _).getD (0, 0)
      rw [r2]

/-- Any number of steps of the commands leaves the measure no higher. -/
theorem runCmd_le {w : Nat} {k : USize} {last : Bool} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hH : HdrRel H m) : ∀ (N : Nat) (n : USize) (p : Phase) (st : Cmd) (pos : USize), n.toNat = N → Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      CDown Lex4Eq w k.toNat last m a stop p st pos (runCmd H k a stop hs n st pos) := by
  intro N
  induction N with
  | zero =>
    intro n p st pos hN hrel hp
    rw [runCmd, dite_eq_left (usize_zero hN)]
    exact ⟨fun _ => ⟨p, hrel.mark _ _, Nat.le_refl _, hp, fun _ => Or.inr rfl⟩, fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e,
      fun e => StepStatus.noConfusion e⟩
  | succ N ih =>
    intro n p st pos hN hrel hp
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hstep := stepCmd_down (last := last) (a := a) (stop := stop) (hs := hs) hH hrel hp
    rw [runCmd, dite_eq_right hn]
    dsimp only
    generalize stepCmd H k a stop hs st pos = r at hstep
    cases hst : r.status with
    | next =>
      obtain ⟨p', hR, h1, h2, h3⟩ := hstep.next hst
      have hin := ih (n - USize.ofNat 1) p' r r.pos (by omega) hR h2
      generalize runCmd H k a stop hs (n - USize.ofNat 1) r r.pos = r2 at hin
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
      · obtain ⟨p2, b1, b2, b3, b4⟩ := hin.next e
        exact ⟨p2, b1, Nat.le_trans h1 b2, b3, fun F => (b4 F).trans (Or.inl (h3 F))⟩
      · obtain ⟨p2, b1, b2⟩ := hin.needsInput e
        refine ⟨p2, b1, Or.inl (pause_after (R := Lex4) (x := r2.pend) (y := r.pend) (fun a b => a.trans b) h3 ?_)⟩
        exact b2
      · obtain ⟨p2, b1, b2⟩ := hin.needsOutput e
        refine ⟨p2, b1, Or.inl (pause_after (R := Lex4) (x := r2.pend) (y := r.pend) (fun a b => a.trans b) h3 ?_)⟩
        exact b2
      · obtain ⟨s, b1, b2, b3⟩ := hin.done e
        exact ⟨s, b1, b2, fun F => (b3 F).trans (Or.inl (h3 F))⟩
    | needsInput =>
      exact ⟨fun e => absurd (hst.symm.trans e) (by decide), hstep.needsInput, fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide)⟩
    | needsOutput =>
      exact ⟨fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide), hstep.needsOutput, fun e => absurd (hst.symm.trans e) (by decide)⟩
    | done =>
      exact ⟨fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide), hstep.done⟩
    | bad =>
      exact ⟨fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide), fun e => absurd (hst.symm.trans e) (by decide),
        fun e => absurd (hst.symm.trans e) (by decide)⟩

/-- At least one step of the commands lowers the measure. -/
theorem runCmd_down {w : Nat} {k : USize} {last : Bool} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {n : USize} {p : Phase} {st : Cmd} {pos : USize} (hn : n ≠ 0) (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) :
    CDown Lex4 w k.toNat last m a stop p st pos (runCmd H k a stop hs n st pos) := by
  have hpred := usize_pred hn
  have hstep := stepCmd_down (last := last) (a := a) (stop := stop) (hs := hs) hH hrel hp
  rw [runCmd, dite_eq_right hn]
  dsimp only
  generalize stepCmd H k a stop hs st pos = r at hstep
  cases hst : r.status with
  | next =>
    obtain ⟨p', hR, h1, h2, h3⟩ := hstep.next hst
    have hin := runCmd_le (last := last) (a := a) (stop := stop) (hs := hs) hH _ (n - USize.ofNat 1) p' r r.pos rfl hR h2
    generalize runCmd H k a stop hs (n - USize.ofNat 1) r r.pos = r2 at hin
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · obtain ⟨p2, b1, b2, b3, b4⟩ := hin.next e
      exact ⟨p2, b1, Nat.le_trans h1 b2, b3, fun F => (b4 F).trans_lt (h3 F)⟩
    · obtain ⟨p2, b1, b2⟩ := hin.needsInput e
      refine ⟨p2, b1, Or.inl (pause_after (R := Lex4) (x := r2.pend) (y := r.pend) (fun a b => a.trans b) h3 ?_)⟩
      exact b2
    · obtain ⟨p2, b1, b2⟩ := hin.needsOutput e
      refine ⟨p2, b1, Or.inl (pause_after (R := Lex4) (x := r2.pend) (y := r.pend) (fun a b => a.trans b) h3 ?_)⟩
      exact b2
    · obtain ⟨s, b1, b2, b3⟩ := hin.done e
      exact ⟨s, b1, b2, fun F => (b3 F).trans (Or.inl (h3 F))⟩
  | needsInput => exact hstep
  | needsOutput => exact hstep
  | done => exact hstep
  | bad => exact hstep

/-! ### The measure on the stream -/

/-- The measure: the bits left at the meta-block's end, which kind of place, and how far along. -/
abbrev Meas := Nat × Nat × ((Nat × Nat) × (Nat × Nat))

/-- Lower in the measure. -/
def MLt (a b : Meas) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ Lex4 a.2.2 b.2.2)))

/-- Lower or the same in the measure. -/
def MLe (a b : Meas) : Prop := MLt a b ∨ a = b

/-- A place's measure, for its bits. -/
def mOf : SPhase → List Bool → Meas
  | .wbits, bs => ((lenSem.first bs).getD 0, 2, ((0, 0), (0, 0)))
  | .mblock .., bs => (bs.length + 1, 1, ((0, 0), (0, 0)))
  | .skip w st last n, bs => ((skipK (lenSem.after w last) st n bs).getD 0, 2, ((n, 0), (0, 0)))
  | .raw w st last n, bs => ((rawK (lenSem.after w last) st n bs).getD 0, 2, ((n, 0), (0, 0)))
  | .hdr w st last mlen g p, bs => ((hrest (hdrK w (lenSem.after w last) st mlen) g p bs).getD 0, 3, rankH p)
  | .cmds w last m p, bs => ((cVal w last m p bs).1, 2, (((cVal w last m p bs).2, (rankC p).1), ((rankC p).2, 0)))
  | .ended _, bs => (bs.length + 1, 0, ((0, 0), (0, 0)))

/-- A meta-block's start lowers the bits left. -/
private theorem block_lt (w : Nat) (st : StreamState) (bs : List Bool) : (sLeave lenSem (.mblock w st) bs).getD 0 < bs.length + 1 := by
  show ((metaStart bs >>= fun p => afterStart w (lenSem.after w) st p.1 p.2).getD 0) < _
  rw [← block_start]
  cases hm : readMetaBlock w st bs with
  | none => exact Nat.succ_pos _
  | some p =>
    obtain ⟨⟨st1, l⟩, r⟩ := p
    have := readMetaBlock_lt hm
    show r.length + 1 < bs.length + 1
    omega

/-- A command's start, in the measure. -/
private theorem cVal_command (w : Nat) (last : Bool) (m : MetaBlockHeader) (s : CommandState) (bs : List Bool) :
    cVal w last m (.command s) bs = ((cmdK w (lenSem.after w last) m s bs).getD 0, commandMeasure s bs + 1) := by
  unfold cVal
  rw [rest_command]
  rfl

/-- A step away from a place lowers its measure. -/
private theorem down_next {p p' : SPhase} {bs bs' : List Bool} (hc : ∀ w l m q, p ≠ .cmds w l m q) (hn : ∀ st, p ≠ .ended st)
    (hs : SDown p p') (he : sLeave lenSem p bs = srest lenSem p' bs') : MLt (mOf p' bs') (mOf p bs) := by
  cases p with
  | cmds w l m q => exact absurd rfl (hc w l m q)
  | ended st => exact absurd rfl (hn st)
  | wbits =>
    cases p' with
    | mblock w st =>
      have he' : lenSem.first bs = some (bs'.length + 1) := he
      refine Or.inr ⟨?_, Or.inl (show 1 < 2 by decide)⟩
      show bs'.length + 1 = (lenSem.first bs).getD 0
      rw [he']
      rfl
    | wbits | skip | raw | hdr | cmds | ended => exact hs.elim
  | mblock w st =>
    have hlt := block_lt w st bs
    rw [he] at hlt
    cases p' with
    | ended | skip | raw | hdr => exact Or.inl hlt
    | wbits | mblock | cmds => exact hs.elim
  | hdr w st l mlen g q =>
    have he' : hrest (hdrK w (lenSem.after w l) st mlen) g q bs = srest lenSem p' bs' := he
    cases p' with
    | hdr w2 st2 l2 mlen2 g2 q2 =>
      refine Or.inr ⟨?_, Or.inr ⟨rfl, hs⟩⟩
      show (hrest (hdrK w2 (lenSem.after w2 l2) st2 mlen2) g2 q2 bs').getD 0 = (hrest (hdrK w (lenSem.after w l) st mlen) g q bs).getD 0
      rw [he']
      rfl
    | cmds w2 l2 m2 q2 =>
      obtain ⟨s, rfl⟩ := hs
      refine Or.inr ⟨?_, Or.inl (show 2 < 3 by decide)⟩
      show (cVal w2 l2 m2 (.command s) bs').1 = (hrest (hdrK w (lenSem.after w l) st mlen) g q bs).getD 0
      rw [cVal_command, he']
      rfl
    | wbits | mblock | skip | raw | ended => exact hs.elim
  | skip w st l n =>
    have he' : skipK (lenSem.after w l) st n bs = srest lenSem p' bs' := he
    cases p' with
    | skip w2 st2 l2 n2 =>
      refine Or.inr ⟨?_, Or.inr ⟨rfl, Or.inl (Or.inl hs)⟩⟩
      show (skipK (lenSem.after w2 l2) st2 n2 bs').getD 0 = (skipK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | mblock w2 st2 =>
      refine Or.inr ⟨?_, Or.inl (show 1 < 2 by decide)⟩
      show bs'.length + 1 = (skipK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | ended st2 =>
      refine Or.inr ⟨?_, Or.inl (show 0 < 2 by decide)⟩
      show bs'.length + 1 = (skipK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | wbits | raw | hdr | cmds => exact hs.elim
  | raw w st l n =>
    have he' : rawK (lenSem.after w l) st n bs = srest lenSem p' bs' := he
    cases p' with
    | raw w2 st2 l2 n2 =>
      refine Or.inr ⟨?_, Or.inr ⟨rfl, Or.inl (Or.inl hs)⟩⟩
      show (rawK (lenSem.after w2 l2) st2 n2 bs').getD 0 = (rawK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | mblock w2 st2 =>
      refine Or.inr ⟨?_, Or.inl (show 1 < 2 by decide)⟩
      show bs'.length + 1 = (rawK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | ended st2 =>
      refine Or.inr ⟨?_, Or.inl (show 0 < 2 by decide)⟩
      show bs'.length + 1 = (rawK (lenSem.after w l) st n bs).getD 0
      rw [he']
      rfl
    | wbits | skip | hdr | cmds => exact hs.elim

/-- A pause in a place leaves its measure lower, or the same with no more bytes waiting. -/
private theorem down_pause {p p' : SPhase} {same : Prop} {B B' : List UInt8 → List Bool} (hc : ∀ w l m q, p ≠ .cmds w l m q) (hn : ∀ st, p ≠ .ended st)
    (hs : SDownEq p p' same) (he : ∀ t, sLeave lenSem p (B t) = sLeave lenSem p' (B' t)) (hb : ∀ w st, p = .mblock w st → ∀ t, B' t = B t) :
    (∀ t, MLt (mOf p' (B' t)) (mOf p (B t))) ∨ (same ∧ ∀ t, mOf p' (B' t) = mOf p (B t)) := by
  cases p with
  | cmds w l m q => exact absurd rfl (hc w l m q)
  | ended st => exact absurd rfl (hn st)
  | wbits =>
    cases p' with
    | wbits =>
      refine Or.inr ⟨hs, fun t => ?_⟩
      have he' : lenSem.first (B t) = lenSem.first (B' t) := he t
      show ((lenSem.first (B' t)).getD 0, _) = ((lenSem.first (B t)).getD 0, _)
      rw [he']
    | mblock | skip | raw | hdr | cmds | ended => exact hs.elim
  | mblock w st =>
    cases p' with
    | mblock => exact Or.inr ⟨hs, fun t => by rw [hb w st rfl t]; rfl⟩
    | wbits | skip | raw | hdr | cmds | ended => exact hs.elim
  | hdr w st l mlen g q =>
    cases p' with
    | hdr w2 st2 l2 mlen2 g2 q2 =>
      obtain ⟨hq, hsame⟩ := hs
      subst hq
      refine Or.inr ⟨hsame, fun t => ?_⟩
      have he' : hrest (hdrK w (lenSem.after w l) st mlen) g q2 (B t) = hrest (hdrK w2 (lenSem.after w2 l2) st2 mlen2) g2 q2 (B' t) := he t
      show ((hrest (hdrK w2 (lenSem.after w2 l2) st2 mlen2) g2 q2 (B' t)).getD 0, _) = ((hrest (hdrK w (lenSem.after w l) st mlen) g q2 (B t)).getD 0, _)
      rw [he']
    | wbits | mblock | skip | raw | cmds | ended => exact hs.elim
  | skip w st l n =>
    cases p' with
    | skip w2 st2 l2 n2 =>
      have hv : ∀ t, (skipK (lenSem.after w2 l2) st2 n2 (B' t)).getD 0 = (skipK (lenSem.after w l) st n (B t)).getD 0 := by
        intro t
        have he' : skipK (lenSem.after w l) st n (B t) = skipK (lenSem.after w2 l2) st2 n2 (B' t) := he t
        rw [he']
      rcases hs with hlt | ⟨hne, hsame⟩
      · exact Or.inl fun t => Or.inr ⟨hv t, Or.inr ⟨rfl, Or.inl (Or.inl hlt)⟩⟩
      · subst hne
        refine Or.inr ⟨hsame, fun t => ?_⟩
        show ((skipK (lenSem.after w2 l2) st2 n2 (B' t)).getD 0, _) = ((skipK (lenSem.after w l) st n2 (B t)).getD 0, _)
        rw [hv]
    | wbits | mblock | raw | hdr | cmds | ended => exact hs.elim
  | raw w st l n =>
    cases p' with
    | raw w2 st2 l2 n2 =>
      have hv : ∀ t, (rawK (lenSem.after w2 l2) st2 n2 (B' t)).getD 0 = (rawK (lenSem.after w l) st n (B t)).getD 0 := by
        intro t
        have he' : rawK (lenSem.after w l) st n (B t) = rawK (lenSem.after w2 l2) st2 n2 (B' t) := he t
        rw [he']
      rcases hs with hlt | ⟨hne, hsame⟩
      · exact Or.inl fun t => Or.inr ⟨hv t, Or.inr ⟨rfl, Or.inl (Or.inl hlt)⟩⟩
      · subst hne
        refine Or.inr ⟨hsame, fun t => ?_⟩
        show ((rawK (lenSem.after w2 l2) st2 n2 (B' t)).getD 0, _) = ((rawK (lenSem.after w l) st n2 (B t)).getD 0, _)
        rw [hv]
    | wbits | mblock | skip | hdr | cmds | ended => exact hs.elim

/-- A pause's measure: lower for every future, or the same for every future with no more bytes waiting. -/
def MPause (a : ByteArray) (stop : USize) (p p' : SPhase) (D : Dec) (pos : USize) (r : Dec) : Prop :=
  (∀ t : List UInt8, MLt (mOf p' (r.bits a r.pos stop (bits t))) (mOf p (D.bits a pos stop (bits t)))) ∨
    (r.cmd.pend = D.cmd.pend ∧ ∀ t : List UInt8, mOf p' (r.bits a r.pos stop (bits t)) = mOf p (D.bits a pos stop (bits t)))

/-- What a stream step does to the measure. -/
structure DDown (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (pos : USize) (r : Dec) : Prop where
  next : r.status = .next → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ t : List UInt8, MLt (mOf p' (r.bits a r.pos stop (bits t))) (mOf p (D.bits a pos stop (bits t)))
  needsInput : r.status = .needsInput → r.pos = stop ∧ ∃ p', DRel r p' ∧ MPause a stop p p' D pos r
  needsOutput : r.status = .needsOutput → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ r.cmd.pend.toNat ≠ 0 ∧ MPause a stop p p' D pos r

/-- Turns the commands' order into the measure's. -/
private theorem mlt_of_lex {w : Nat} {l : Bool} {m : MetaBlockHeader} {p p' : Phase} {bs bs' : List Bool}
    (h : Lex4 (cMeas w l m p' bs') (cMeas w l m p bs)) : MLt (mOf (.cmds w l m p') bs') (mOf (.cmds w l m p) bs) := by
  generalize hv1 : cVal w l m p' bs' = v1 at h
  generalize hv2 : cVal w l m p bs = v2 at h
  generalize hr1 : rankC p' = r1 at h
  generalize hr2 : rankC p = r2 at h
  have e1 : mOf (.cmds w l m p') bs' = (v1.1, 2, ((v1.2, r1.1), (r1.2, 0))) := by
    show ((cVal w l m p' bs').1, 2, (((cVal w l m p' bs').2, (rankC p').1), ((rankC p').2, 0))) = _
    rw [hv1, hr1]
  have e2 : mOf (.cmds w l m p) bs = (v2.1, 2, ((v2.2, r2.1), (r2.2, 0))) := by
    show ((cVal w l m p bs).1, 2, (((cVal w l m p bs).2, (rankC p).1), ((rankC p).2, 0))) = _
    rw [hv2, hr2]
  rw [e1, e2]
  have h' : Lex4 (v1, r1) (v2, r2) := by
    simpa only [cMeas, hv1, hv2, hr1, hr2] using h
  obtain ⟨a1, a2⟩ := v1
  obtain ⟨b1, b2⟩ := v2
  obtain ⟨c1, c2⟩ := r1
  obtain ⟨d1, d2⟩ := r2
  simp only [Lex4, LexLt, MLt, Prod.mk.injEq, true_and] at h' ⊢
  omega

private theorem meq_of_eq {w : Nat} {l : Bool} {m : MetaBlockHeader} {p p' : Phase} {bs bs' : List Bool}
    (h : cMeas w l m p' bs' = cMeas w l m p bs) : mOf (.cmds w l m p') bs' = mOf (.cmds w l m p) bs := by
  have h1 : cVal w l m p' bs' = cVal w l m p bs := congrArg Prod.fst h
  have h2 : rankC p' = rankC p := congrArg Prod.snd h
  show ((cVal w l m p' bs').1, 2, (((cVal w l m p' bs').2, (rankC p').1), ((rankC p').2, 0))) =
    ((cVal w l m p bs).1, 2, (((cVal w l m p bs).2, (rankC p).1), ((rankC p).2, 0)))
  rw [h1, h2]

private theorem cmdBudget_ne : cmdBudget ≠ 0 := by
  intro e
  have h : cmdBudget.toNat = 65536 := usize_ofNat' (by decide)
  rw [e] at h
  cases h

/-- The commands' step lowers the measure. -/
theorem stepDCmds_down {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec}
    {pos : USize} (hrel : DRel D (.cmds w last m p)) (hp : pos.toNat ≤ stop.toNat) :
    DDown a stop (.cmds w last m p) D pos (stepDCmds a stop hs D pos) := by
  have hok := stepDCmds_ok (S := specSem) (a := a) (hs := hs) hrel hp
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  have hstep := runCmd_down (last := last') (a := a) (stop := stop) (hs := hs) cmdBudget_ne hH hR hp
  unfold stepDCmds takeCmd at hok ⊢
  dsimp only at hok ⊢
  generalize runCmd H k a stop hs cmdBudget cmd pos = r at hstep hok
  cases hst : r.status with
  | next =>
    rw [hst] at hok
    dsimp only at hok ⊢
    obtain ⟨p', hR', h1, h2, h3⟩ := hstep.next hst
    exact ⟨fun _ => ⟨.cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, h1, h2, fun t => mlt_of_lex (h3 _)⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsInput =>
    rw [hst] at hok
    dsimp only at hok ⊢
    obtain ⟨p', hR', h3⟩ := hstep.needsInput hst
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨(hok.needsInput rfl).1, .cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, ?_⟩, fun e => DStatus.noConfusion e⟩
    rcases h3 with h | ⟨h1, h2⟩
    · exact Or.inl fun t => mlt_of_lex (h _)
    · exact Or.inr ⟨h1, fun t => meq_of_eq (h2 _)⟩
  | needsOutput =>
    rw [hst] at hok
    dsimp only at hok ⊢
    obtain ⟨p', hR', h3⟩ := hstep.needsOutput hst
    obtain ⟨_, _, h1, h2, _, h4, _, _, _⟩ := hok.needsOutput rfl
    refine ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => ⟨.cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, h1, h2, h4, ?_⟩⟩
    rcases h3 with h | ⟨h5, h6⟩
    · exact Or.inl fun t => mlt_of_lex (h _)
    · exact Or.inr ⟨h5, fun t => meq_of_eq (h6 _)⟩
  | bad =>
    dsimp only
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | done =>
    rw [hst] at hok
    obtain ⟨s, hR', h4, h3⟩ := hstep.done hst
    have hsee := seenOk_iff hH hR'
    dsimp only at hok ⊢
    by_cases hc : seenOk r H.nL H.nI H.nD = true
    · rw [ite_eq_left hc] at hok ⊢
      rw [hsee] at hc
      have hval : ∀ bs, (cVal w last' m (.command s) bs).1 = bs.length + 1 := by
        intro bs
        rw [cVal_command, cmdK_stop _ _ h4]
        unfold finishC
        rw [ite_eq_left hc]
        rfl
      have hfst : ∀ {a b : (Nat × Nat) × (Nat × Nat)}, Lex4Eq a b → a.1.1 ≤ b.1.1 := by
        intro a b h
        rcases h with h | rfl
        · obtain ⟨⟨a1, a2⟩, _⟩ := a
          obtain ⟨⟨b1, b2⟩, _⟩ := b
          simp only [Lex4, LexLt, Prod.mk.injEq] at h
          dsimp only
          omega
        · exact Nat.le_refl _
      obtain ⟨_, _, h1, h2, _, _⟩ := hok.next rfl
      obtain ⟨hC, _, hprod⟩ := hR'
      have hwin := hC.toWin
      have hend : ∀ {c : Nat} {z : (Nat × Nat) × (Nat × Nat)} {x v : Nat} {y : (Nat × Nat) × (Nat × Nat)}, x ≤ v → c < 2 → MLt (x, c, z) (v, 2, y) := by
        intro c z x v y hx hc
        rcases Nat.lt_or_eq_of_le hx with h | h
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inl hc⟩
      have hlow : ∀ F, (stateBits r a r.pos stop F).length + 1 ≤ (cVal w last' m p (stateBits cmd a pos stop F)).1 := by
        intro F
        rw [← hval]
        exact hfst (h3 F)
      cases last' with
      | true =>
        exact ⟨fun _ => ⟨.ended ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, w, ⟨hwin, hprod, hlim⟩⟩, h1, h2, fun t => hend (hlow _) (by decide)⟩,
          fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      | false =>
        exact ⟨fun _ => ⟨.mblock w ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, ⟨hwin, hprod, hlim⟩⟩, h1, h2, fun t => hend (hlow _) (by decide)⟩,
          fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · rw [ite_eq_right hc]
      exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩

/-- A step lowers the measure. -/
theorem stepD_down {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} (hrel : DRel D p) (he : D.tag ≠ .ended)
    (hp : D.pos.toNat ≤ stop.toNat) {hinv : DInv stop D} : DDown a stop p D D.pos (stepD a stop hs D hinv) := by
  by_cases hc : ∃ w l m q, p = .cmds w l m q
  · obtain ⟨w, l, m, q, rfl⟩ := hc
    have ht : D.tag = .cmds := hrel.1
    unfold stepD
    split <;> rename_i ht'
    all_goals first
      | exact absurd (ht.symm.trans ht') (fun e => DTag.noConfusion e)
      | exact stepDCmds_down hrel hp
  · have hc' : ∀ w l m q, p ≠ .cmds w l m q := fun w l m q e => hc ⟨w, l, m, q, e⟩
    have hn := hrel.tag_ne he
    have h := stepD_ok lenSem (a := a) (hs := hs) (h := hinv) hrel he hp
    generalize stepD a stop hs D hinv = r at h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · obtain ⟨p', r1, r2, r3, r4, r5, _⟩ := h.next e
      exact ⟨p', r1, r2, r3, fun t => down_next hc' hn r5 (r4 t)⟩
    · obtain ⟨r1, _, p', r2, r3, _, r4, r5, _⟩ := h.needsInput e
      exact ⟨r1, p', r2, down_pause hc' hn r4 r3 r5⟩
    · obtain ⟨p', r1, r2, r3, r4, r5, r6, r7, _⟩ := h.needsOutput e
      exact ⟨p', r1, r2, r3, r5, down_pause hc' hn r6 r4 r7⟩

/-! ### The order is well founded -/

theorem plex_wf {α β : Type} {ra : α → α → Prop} {rb : β → β → Prop} (ha : WellFounded ra) (hb : WellFounded rb) :
    WellFounded (fun x y : α × β => ra x.1 y.1 ∨ (x.1 = y.1 ∧ rb x.2 y.2)) := by
  refine Subrelation.wf (r := Prod.Lex ra rb) ?_ (Prod.lex ⟨ra, ha⟩ ⟨rb, hb⟩).wf
  intro x y h
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · have h1' : x1 = y1 := h1
    subst h1'
    exact Prod.Lex.right _ h2

theorem lexLt_wf : WellFounded LexLt := plex_wf Nat.lt_wfRel.wf Nat.lt_wfRel.wf

theorem lex4_wf : WellFounded Lex4 := plex_wf lexLt_wf lexLt_wf

theorem mlt_wf : WellFounded MLt := plex_wf Nat.lt_wfRel.wf (plex_wf Nat.lt_wfRel.wf lex4_wf)

/-! ### The loop -/

/-- What the loop recurs on. -/
structure RunArg (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) where
  D : Dec
  inv : DInv stop D

/-- The state after a step that moved on. -/
def runRel (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (x y : RunArg a stop hs) : Prop :=
  y.D.tag ≠ .ended ∧ (stepD a stop hs y.D y.inv).status = .next ∧ x.D = stepD a stop hs y.D y.inv

/-- The loop's steps can't go on forever. -/
theorem runRel_wf (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) : WellFounded (runRel a stop hs) := by
  have key : ∀ m : Meas, ∀ (y : RunArg a stop hs) (p : SPhase), DRel y.D p → mOf p (y.D.bits a y.D.pos stop (bits [])) = m → Acc (runRel a stop hs) y := by
    intro m
    induction m using mlt_wf.induction with
    | _ m ih =>
      intro y p hrel he
      refine Acc.intro y fun x hx => ?_
      obtain ⟨ht, hn, hxe⟩ := hx
      obtain ⟨p', hR, _, _, hlt⟩ := (stepD_down (a := a) (hs := hs) hrel ht y.inv.2).next hn
      refine ih _ ?_ x p' (by rw [hxe]; exact hR) rfl
      rw [← he, hxe]
      exact hlt []
  exact ⟨fun y => by
    obtain ⟨p, hrel⟩ := y.inv.1
    exact key _ y p hrel rfl⟩

instance (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) : WellFoundedRelation (RunArg a stop hs) :=
  ⟨runRel a stop hs, runRel_wf a stop hs⟩

/-- A step that moved on leaves a state the loop can run from. -/
theorem DInv.step {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} (h : DInv stop D) (he : D.tag ≠ .ended)
    (hn : (stepD a stop hs D h).status = .next) : DInv stop (stepD a stop hs D h) := by
  obtain ⟨⟨p, hrel⟩, hp⟩ := h
  obtain ⟨p', hR, _, h2, _⟩ := (stepD_ok specSem (a := a) (hs := hs) hrel he hp).next hn
  exact ⟨⟨p', hR⟩, h2⟩

/-- Steps until the stream's end, or until one pauses or stops. -/
def runD (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Dec :=
  if he : D.tag = .ended then { D with status := .next }
  else
    let r := stepD a stop hs D h
    if hn : r.status = .next then runD a stop hs r (h.step he hn)
    else r
termination_by (RunArg.mk D h : RunArg a stop hs)
decreasing_by exact ⟨he, hn, rfl⟩

end Brotli.Decoder
