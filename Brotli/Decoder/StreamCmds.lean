import Brotli.Decoder.StreamState
import Brotli.Decoder.Positions

/-!
# From a header to its commands, and on

Starting a meta-block's commands once its header is read, running them, and the check at their end.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The block type flags at the start of a meta-block's commands: type 0 of each category has occurred. -/
def seenInit : ByteArray := ((List.range 768).map fun i => if i % 256 = 0 then (1 : UInt8) else 0).toByteArray

theorem seenInit_size : seenInit.size = 768 := by
  simp [seenInit, List.size_toByteArray]

theorem seenInit_at {i : Nat} (h : i < 768) : seenInit.data[i]?.getD 0 = if i % 256 = 0 then (1 : UInt8) else 0 := by
  simp only [seenInit, List.data_toByteArray, List.getElem?_toArray]
  simp [h]

/-- The command loop's state at the start of a meta-block, with `seen` the flags `seenInit`. -/
def cmdStart (c : Cmd) (d : Done) (word count mlen : UInt64) (seen : ByteArray) : Cmd :=
  { c with
    word := word, count := count, remaining := mlen, iCur := 0, iPrev := 1, iCount := d.countI, lCur := 0, lPrev := 1, lCount := d.countL
    dCur := 0, dPrev := 1, dCount := d.countD, seen := seen, tag := .command }

private theorem blockRel_start {seenInit : ByteArray} (seenInit_at : ∀ {i : Nat}, i < 768 → seenInit.data[i]?.getD 0 = if i % 256 = 0 then (1 : UInt8) else 0)
    {c : BlockCategory} {off : Nat} {count : UInt64} (hoff : off = 0 ∨ off = 256 ∨ off = 512)
    (hc : count.toNat = c.firstCount) (hw : c.Wf) : BlockRel seenInit off 0 1 count (.initial c) c where
  cur := rfl
  prev := rfl
  count := hc.symm
  wf := by
    refine ⟨fun h => h, by show 0 < c.n; have := hw.1; omega, fun t ht => ?_⟩
    simp only [BlockState.initial, List.mem_singleton] at ht
    subst ht
    have := hw.1
    omega
  flags := by
    intro t ht
    rw [seenInit_at (by rcases hoff with h | h | h <;> omega)]
    have hmem : t ∈ (BlockState.initial c).seen ↔ t = 0 := by simp [BlockState.initial]
    rw [hmem]
    have hmod : (off + t) % 256 = 0 ↔ t = 0 := by
      rcases hoff with h | h | h <;> subst h <;> omega
    by_cases h0 : t = 0
    · rw [ite_eq_left (hmod.mpr h0)]
      exact ⟨fun _ => h0, fun _ => by decide⟩
    · rw [ite_eq_right (fun e => h0 (hmod.mp e))]
      exact ⟨fun e => absurd rfl e, fun e => absurd e h0⟩

/-- A state at the start of a meta-block's commands stands for that place. -/
theorem cmdStart_rel {c : Cmd} {d : Done} {g : Gh} {w k : Nat} {st : StreamState} {word count mlen : UInt64} {seen : ByteArray}
    (hs1 : seen.size = 768) (hs2 : ∀ {i : Nat}, i < 768 → seen.data[i]?.getD 0 = if i % 256 = 0 then (1 : UInt8) else 0)
    (hw : (BitBuffer.mk word count).Wf) (hu : Upto d g 10) (hwin : WinRel w k c st.output st.distances) (hp : st.produced = st.output.length) :
    Rel w k g.m (cmdStart c d word count mlen seen) (.command (startState st mlen.toNat g.m)) := by
  have hL := hu.cat .L (by decide)
  have hI := hu.cat .I (by decide)
  have hD := hu.cat .D (by decide)
  refine ⟨?_, rfl, hp⟩
  exact {
    wf := hw
    win := hwin.win
    k24 := hwin.k24
    ring := hwin.ring
    bytes := hwin.bytes
    ctx := hwin.ctx
    pendLe := hwin.pendLe
    pendOut := hwin.pendOut
    written := hwin.written
    rem := rfl
    d0 := hwin.d0
    d1 := hwin.d1
    d2 := hwin.d2
    d3 := hwin.d3
    dsLt := hwin.dsLt
    iRel := blockRel_start hs2 (off := 256) (by decide) hI.count hI.wf
    lRel := blockRel_start hs2 (off := 0) (by decide) hL.count hL.wf
    dRel := blockRel_start hs2 (off := 512) (by decide) hD.count hD.wf
    seenSize := hs1
    wordLe := hwin.wordLe }

/-! ### The check at the end of the commands -/

/-- Checks `n` flags from `t`. -/
def allMarked (flags : ByteArray) (t n : UInt64) : Bool :=
  if _hn : n = 0 then true
  else if getU flags t.toUSize = 0 then false else allMarked flags (t + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem allMarked_iff (flags : ByteArray) : ∀ (N : Nat) (t n : UInt64), n.toNat = N → t.toNat + N < 2 ^ 32 →
    (allMarked flags t n = true ↔ ∀ k, t.toNat ≤ k → k < t.toNat + N → flags.data[k]?.getD 0 ≠ 0) := by
  intro N
  induction N with
  | zero =>
    intro t n hn _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [allMarked, dite_eq_left hz]
    exact ⟨fun _ k h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro t n hn h32
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (t + 1).toNat = t.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : t.toUSize.toNat = t.toNat := word_toUSize (by omega)
    have hget : getU flags t.toUSize = flags.data[t.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [getU_toNat, hus]
    rw [allMarked, dite_eq_right hz, hget]
    by_cases hc : flags.data[t.toNat]?.getD 0 = 0
    · rw [ite_eq_left hc]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd hc (h t.toNat (Nat.le_refl _) (by omega))⟩
    · rw [ite_eq_right hc, ih (t + 1) (n - 1) hn1 (by rw [hi1]; omega), hi1]
      constructor
      · intro h k h1 h2
        by_cases he : k = t.toNat
        · rw [he]
          exact hc
        · exact h k (by omega) (by omega)
      · intro h k h1 h2
        exact h k (by omega) (by omega)

/-- A meta-block's end check: every block type occurred. -/
@[inline] def seenOk (seen : ByteArray) (nL nI nD : UInt64) : Bool :=
  allMarked seen 0 nL && allMarked seen 256 nI && allMarked seen 512 nD

private theorem uses_iff {seen : ByteArray} {off : Nat} {cur prev count : UInt64} {st : BlockState} {c : BlockCategory} (h : BlockRel seen off cur prev count st c)
    {o n : UInt64} (ho : o.toNat = off) (hoff : off ≤ 512) (hn : n.toNat = c.n) (hc : c.n ≤ 256) :
    allMarked seen o n = true ↔ usesEveryType c st = true := by
  rw [allMarked_iff seen _ o n rfl (by omega), ho, hn]
  unfold usesEveryType
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem]
  constructor
  · intro hall t ht
    exact (h.flags t (by omega)).mp (hall (off + t) (by omega) (by omega))
  · intro hall j h1 h2
    have e : j = off + (j - off) := by omega
    rw [e]
    exact (h.flags (j - off) (by omega)).mpr (hall _ (by omega))

/-- The check says what the spec checks. -/
theorem seenOk_iff {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {st : Cmd} {s : CommandState} (hH : HdrRel H m)
    (hrel : Rel w k m st (.command s)) :
    seenOk st.seen H.nL H.nI H.nD = (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy && usesEveryType m.distance s.distance) := by
  have hC := hrel.1
  have hL := uses_iff hC.lRel (o := 0) rfl (by omega) hH.nL hH.ok.literal.2.1
  have hI := uses_iff hC.iRel (o := 256) rfl (by omega) hH.nI hH.ok.insertCopy.2.1
  have hD := uses_iff hC.dRel (o := 512) rfl (by omega) hH.nD hH.ok.distance.2.1
  unfold seenOk
  generalize allMarked st.seen 0 H.nL = a1 at hL
  generalize allMarked st.seen 256 H.nI = a2 at hI
  generalize allMarked st.seen 512 H.nD = a3 at hD
  generalize usesEveryType m.literal s.literal = b1 at hL
  generalize usesEveryType m.insertCopy s.insertCopy = b2 at hI
  generalize usesEveryType m.distance s.distance = b3 at hD
  have e1 : a1 = b1 := Bool.eq_iff_iff.mpr hL
  have e2 : a2 = b2 := Bool.eq_iff_iff.mpr hI
  have e3 : a3 = b3 := Bool.eq_iff_iff.mpr hD
  rw [e1, e2, e3]

/-! ### Steps -/

/-- A command loop's state with nothing in it, to hold a state's place while the real one is written. -/
def Cmd.none : Cmd := ⟨0, 0, ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ByteArray.empty, .command, 0, 0, 0, 0, 0, 0,
  0, ByteArray.empty, 0, 0, .next⟩

/-- A header machine's state with nothing in it. -/
def Hd.none : Hd := ⟨0, 0, 0, .next, .cat, Done.none, .L, .type, true, .L, 0, 0, 0, 0, 0, ByteArray.empty, ByteArray.empty, 0, 0, 0, 0, 0,
  ByteArray.empty, 0, 0, 0, 0, Tab.none, Tab.none, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Empties a stream state's command loop state, so that its window is held once. -/
@[noinline] def clearCmd (D : Dec) : Dec := { D with cmd := Cmd.none }

/-- Empties a stream state's header machine state, so that what it writes is held once. -/
@[noinline] def clearHd (D : Dec) : Dec := { D with hd := Hd.none }

/-- A stream state's command loop state, and the stream state emptied of it. A step that writes the window takes the state
this way: the step needs the call's result, so the stream state lets go of the window first, while the compiler may move a
plain `let D0 := clearCmd D` past the step and leave the window held twice while it writes. -/
@[noinline] def takeCmd (D : Dec) : Cmd × Dec := (D.cmd, clearCmd D)

/-- A stream state's header machine state, and the stream state emptied of it, as `takeCmd` takes the command loop state. -/
@[noinline] def takeHd (D : Dec) : Hd × Dec := (D.hd, clearHd D)

/-- Steps the commands take before the outer loop looks at them. -/
def cmdBudget : USize := USize.ofNat 65536

/-- The place in a meta-block's commands. -/
def stepDCmds (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  let H := D.H
  let k := D.k
  let last := D.last
  match takeCmd D with
  | (c, D0) =>
  let r := runCmd H k a stop hs cmdBudget c pos
  let rp := r.pos
  match r.status with
  | .next => { D0 with cmd := r, pos := rp, status := .next }
  | .needsInput => { D0 with cmd := r, pos := rp, status := .needsInput }
  | .needsOutput => { D0 with cmd := r, pos := rp, status := .needsOutput }
  | .bad => { D0 with cmd := r, pos := rp, status := .bad }
  | .done =>
    if seenOk r.seen H.nL H.nI H.nD then
      { D0 with cmd := r, pos := rp, status := .next, tag := if last then .ended else .mblock, H := Hdr.none }
    else { D0 with cmd := r, pos := rp, status := .bad }

/-- The bits of a state outside a header. -/
theorem Dec.bits_cmd {D : Dec} (h : D.tag ≠ .hdr) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    D.bits a pos stop F = availBits D.cmd.word D.cmd.count a pos stop F := by
  unfold Dec.bits Dec.word Dec.count
  cases ht : D.tag <;> first | exact absurd ht h | rfl

/-- The bits a state outside a header holds. -/
theorem Dec.held_cmd {D : Dec} (h : D.tag ≠ .hdr) : D.held = (BitBuffer.mk D.cmd.word D.cmd.count).held := by
  unfold Dec.held Dec.word Dec.count
  cases ht : D.tag <;> first | exact absurd ht h | rfl

theorem stepDCmds_ok {α : Type} {S : Sem α} {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec}
    {pos : USize} (hrel : DRel D (.cmds w last m p)) (hp : pos.toNat ≤ stop.toNat) :
    DStepOk S a stop (.cmds w last m p) D pos (stepDCmds a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  have hstep := runCmd_ok (hs := hs) (K := cmdK w (S.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
  have hbad := runCmd_bad (hs := hs) (K := cmdK w (S.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmd H k a stop hs cmdBudget cmd pos = r at hstep hbad
  cases hst : r.status with
  | next =>
    dsimp only
    obtain ⟨p', hR', h1, h2, h3, h4, h5⟩ := hstep.next hst
    exact ⟨fun _ => ⟨.cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, h1, h2, (fun t => h3 _), trivial, h4, fun t => sreach_cmds (h5 _)⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsInput =>
    dsimp only
    obtain ⟨h1, h2, p', hR', h3, h4, h5, h6, h7⟩ := hstep.needsInput hst
    exact ⟨fun e => DStatus.noConfusion e, fun _ => ⟨h1, h2, .cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, (fun t => h3 _), h4, trivial,
      (fun _ _ e => SPhase.noConfusion e), h5, (fun t => sreach_cmds (h6 _)), short_cmds h7⟩, fun e => DStatus.noConfusion e,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsOutput =>
    dsimp only
    obtain ⟨p', hR', h1, h2, h3, h4, h5, h6⟩ := hstep.needsOutput hst
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => ⟨.cmds w last' m p', ⟨ht, hl, hlim, hH, hR'⟩, h1, h2, (fun t => h3 _),
      h4,
      trivial, (fun _ _ e => SPhase.noConfusion e), h5, fun t => sreach_cmds (h6 _)⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | bad =>
    dsimp only
    obtain ⟨p1, st1, pos1, g1, g2, g3, g4, g5, g6⟩ := hbad hst
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨fun t => hstep.bad hst _, .cmds w last' m p1, (BitBuffer.mk st1.word st1.count).held, pos1, g1, g2, g3,
        by rw [BitBuffer.held_length]; exact g4, fun t => reach_cmds (g5 _), fun t => g6 _⟩⟩
  | done =>
    obtain ⟨s, hR', h1, h2, h3, h4, h5, h6⟩ := hstep.done hst
    have hsee := seenOk_iff hH hR'
    dsimp only
    by_cases hc : seenOk r.seen H.nL H.nI H.nD = true
    · rw [ite_eq_left hc]
      rw [hsee] at hc
      obtain ⟨hC, _, hprod⟩ := hR'
      have hwin := hC.toWin
      have hfin : ∀ F, rest w m (cmdK w (S.after w last') m) p (stateBits cmd a pos stop F) =
          S.after w last' ⟨s.output, s.produced, s.distances⟩ (stateBits r a r.pos stop F) := by
        intro F
        rw [h3 F]
        show cmdK w (S.after w last') m s _ = _
        rw [cmdK_stop _ _ h4]
        unfold finishC
        rw [ite_eq_left hc]
      have hj : ∀ F, SReach (.cmds w last' m p) (stateBits cmd a pos stop F) (afterBlock w last' ⟨s.output, s.produced, s.distances⟩)
          (stateBits r a r.pos stop F) := fun F =>
        (sreach_cmds (h6 F)).snoc (fun _ _ e => SPhase.noConfusion e) (sStep_cmds_end _ h4 hc)
      cases last' with
      | true =>
        exact ⟨fun _ => ⟨.ended ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, w, ⟨hwin, hprod, hlim⟩⟩, h1, h2, (fun t => (hfin _).trans (S.after_true ..)), trivial, h5,
          fun t => hj _⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      | false =>
        exact ⟨fun _ => ⟨.mblock w ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, ⟨hwin, hprod, hlim⟩⟩, h1, h2, (fun t => (hfin _).trans (S.after_false ..)), trivial, h5,
          fun t => hj _⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · rw [ite_eq_right hc]
      rw [hsee] at hc
      have hrej : ∀ bs, rest w m (cmdK w (S.after w last') m) (.command s) bs = none := by
        intro bs
        show cmdK w (S.after w last') m s bs = _
        rw [cmdK_stop _ _ h4]
        unfold finishC
        rw [ite_eq_right hc]
      have hcl := hR'.wf.count_le
      refine ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
        fun _ => ⟨fun t => ?_, .cmds w last' m (.command s), (BitBuffer.mk r.word r.count).held, r.pos, h1, Nat.le_refl _, h2, ?_,
          fun t => reach_cmds (h6 _), fun t => hrej _⟩⟩
      · show rest w m (cmdK w (S.after w last') m) p (stateBits cmd a pos stop (bits t)) = _
        rw [h3]
        exact hrej _
      · rw [BitBuffer.held_length]
        show 8 * r.pos.toNat + r.count.toNat ≤ 8 * r.pos.toNat + 64
        exact Nat.add_le_add_left hcl _

/-- What handing out a state's bytes needs: none waiting, or a window holding them. -/
def WinOk (D : Dec) : Prop :=
  D.cmd.pend = 0 ∨ ∃ out : List Nat, RingOk D.cmd.ring D.k.toNat D.cmd.wpos.toNat out ∧ D.cmd.pend.toNat ≤ 2 ^ D.k.toNat ∧
    D.cmd.pend.toNat ≤ out.length ∧ D.k.toNat ≤ 24

/-- A state whose command loop state stands for a place can hand out its bytes. -/
theorem Rel.winOk {w : Nat} {m : MetaBlockHeader} {D : Dec} {p : Phase} (h : Rel w D.k.toNat m D.cmd p) : WinOk D :=
  Or.inr ⟨p.out, h.window⟩

/-- The same window and bytes waiting, with the same window size, can still be handed out. -/
theorem WinOk.same {D r : Dec} (h : WinOk D) (hc : r.cmd.WinSame D.cmd) (hk : r.k = D.k) : WinOk r := by
  obtain ⟨e1, e2, e3⟩ := hc
  unfold WinOk at h ⊢
  rw [e1, e2, e3, hk]
  exact h

/-- The commands, when they reject, can hand out their bytes. -/
theorem stepDCmds_badWin {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m p)) (hp : pos.toNat ≤ stop.toNat) :
    (stepDCmds a stop hs D pos).status = .bad → WinOk (stepDCmds a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hstep := runCmd_ok (hs := hs) (K := cmdK w (specSem.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
  have hbad := runCmd_badWin (hs := hs) (K := cmdK w (specSem.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmd H k a stop hs cmdBudget cmd pos = r at hstep hbad
  cases hst : r.status with
  | bad =>
    intro _
    obtain ⟨p1, st1, h1, h2⟩ := hbad hst
    exact WinOk.same (D := ⟨.cmds, st1, hd, H, k, last', left, limit, pos', status⟩) (Rel.winOk h1) h2 rfl
  | done =>
    obtain ⟨s, hR', -⟩ := hstep.done hst
    dsimp only
    split
    · intro e
      cases e
    · intro _
      exact Rel.winOk (D := ⟨.cmds, r, hd, H, k, last', left, limit, pos', status⟩) hR'
  | next => intro e; cases e
  | needsInput => intro e; cases e
  | needsOutput => intro e; cases e

end Brotli.Decoder
