module

public import Brotli.Decoder.StreamState
public import Brotli.Decoder.Positions
public import Brotli.Decoder.LoopK
public import Brotli.Decoder.LoopY
public import Brotli.Decoder.FastRun

@[expose] public section

/-!
# From a header to its commands, and on

Starting a meta-block's commands once its header is read, running them, and the check at their end.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The command loop's state at the start of a meta-block: in each category, only type 0 has occurred. -/
def cmdStart (c : Cmd) (d : Done) (word count mlen : UInt64) : Cmd :=
  { c with
    word := word, count := count, remaining := mlen, iCount := d.countI, lCount := d.countL, dCount := d.countD
    flags := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0⟩, tag := .command
    ext := { c.ext with iCur := 0, iPrev := 1, lCur := 0, lPrev := 1, dCur := 0, dPrev := 1, clen := 2, copyBase := 2 } }

private theorem flagOf_start : ∀ t, t < 256 → flagOf 1 0 0 0 t = decide (t = 0) := by
  decide +kernel

private theorem blockRel_start {c : BlockCategory} {count : UInt64} (hc : count.toNat = c.firstCount) (hw : c.Wf) :
    BlockRel 1 0 0 0 0 1 count (.initial c) c where
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
    have hmem : t ∈ (BlockState.initial c).seen ↔ t = 0 := by simp [BlockState.initial]
    rw [flagOf_start t ht, hmem, decide_eq_true_iff]

/-- A state at the start of a meta-block's commands stands for that place. -/
theorem cmdStart_rel {c : Cmd} {d : Done} {g : Gh} {w k : Nat} {st : StreamState} {word count mlen : UInt64}
    (hw : (BitBuffer.mk word count).Wf) (hu : Upto d g 10) (hwin : WinRel w k c st.output st.distances) (hp : st.produced = st.output.length) :
    Rel w k g.m (cmdStart c d word count mlen) (.command (startState st mlen.toNat g.m)) := by
  have hL := hu.cat .L (by decide)
  have hI := hu.cat .I (by decide)
  have hD := hu.cat .D (by decide)
  refine ⟨?_, rfl, hp⟩
  exact {
    wf := hw
    win := hwin.win
    k24 := hwin.k24
    k10 := hwin.k10
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
    iRel := blockRel_start hI.count hI.wf
    lRel := blockRel_start hL.count hL.wf
    dRel := blockRel_start hD.count hD.wf
    wordLe := hwin.wordLe
    clen1 := by show 1 ≤ (2 : UInt64).toNat; decide
    cbase1 := by show 1 ≤ (2 : UInt64).toNat; decide }

/-! ### The check at the end of the commands -/

/-- The first `k` bits, for `k ≤ 64`. -/
@[inline] def firstBits (k : UInt64) : UInt64 := if k = 0 then 0 else 0xFFFFFFFFFFFFFFFF >>> (64 - k)

private theorem firstBits_bit {k : UInt64} (hk : k.toNat ≤ 64) (i : Nat) :
    (firstBits k).toNat.testBit i = decide (i < k.toNat) := by
  unfold firstBits
  by_cases h0 : k = 0
  · subst h0
    simp
  · rw [ite_eq_right h0]
    have hk0 : k.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
    rw [UInt64.toNat_shiftRight, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (64 : UInt64).toNat = 64 from rfl]; omega))]
    rw [show (64 : UInt64).toNat = 64 from rfl, show (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 from rfl,
      Nat.mod_eq_of_lt (show 64 - k.toNat < 64 by omega), Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
    by_cases h : i < k.toNat
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]

/-- How many of the types below `n` word `j` holds. -/
@[inline] def wordNeed (n j : UInt64) : UInt64 :=
  if n ≤ 64 * j then 0 else if 64 * j + 64 ≤ n then 64 else n - 64 * j

private theorem wordNeed_toNat {n j : UInt64} (hj : j.toNat < 4) :
    (wordNeed n j).toNat = min 64 (n.toNat - 64 * j.toNat) := by
  have e1 : (64 * j).toNat = 64 * j.toNat := by
    rw [UInt64.toNat_mul, show (64 : UInt64).toNat = 64 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (64 * j + 64).toNat = 64 * j.toNat + 64 := by
    rw [UInt64.toNat_add, e1, show (64 : UInt64).toNat = 64 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  unfold wordNeed
  by_cases h1 : n ≤ 64 * j
  · have : n.toNat ≤ 64 * j.toNat := by rw [← e1]; exact UInt64.le_iff_toNat_le.mp h1
    rw [ite_eq_left h1]
    show 0 = _
    omega
  · have : ¬ n.toNat ≤ 64 * j.toNat := fun h => h1 (UInt64.le_iff_toNat_le.mpr (by rw [e1]; exact h))
    rw [ite_eq_right h1]
    by_cases h2 : 64 * j + 64 ≤ n
    · have : 64 * j.toNat + 64 ≤ n.toNat := by rw [← e2]; exact UInt64.le_iff_toNat_le.mp h2
      rw [ite_eq_left h2]
      show 64 = _
      omega
    · have : ¬ 64 * j.toNat + 64 ≤ n.toNat := fun h => h2 (UInt64.le_iff_toNat_le.mpr (by rw [e2]; exact h))
      rw [ite_eq_right h2, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [e1]; omega)), e1]
      omega

/-- Whether word `j` has every type below `n` that it holds. -/
@[inline] def wordHas (w n j : UInt64) : Bool := w &&& firstBits (wordNeed n j) == firstBits (wordNeed n j)

private theorem and_eq_iff {w m : UInt64} :
    (w &&& m == m) = true ↔ ∀ i, i < 64 → m.toNat.testBit i = true → w.toNat.testBit i = true := by
  rw [beq_iff_eq]
  constructor
  · intro h i _ hm
    have := congrArg (fun x : UInt64 => x.toNat.testBit i) h
    simp only [UInt64.toNat_and, Nat.testBit_and, hm, Bool.and_true] at this
    exact this
  · intro h
    apply UInt64.toNat_inj.mp
    apply Nat.eq_of_testBit_eq
    intro i
    rw [UInt64.toNat_and, Nat.testBit_and]
    by_cases hi : i < 64
    · cases hm : m.toNat.testBit i
      · simp
      · rw [h i hi hm]
        rfl
    · have := m.toNat_lt
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp

private theorem wordHas_iff {w n j : UInt64} (hj : j.toNat < 4) :
    wordHas w n j = true ↔ ∀ i, i < 64 → 64 * j.toNat + i < n.toNat → w.toNat.testBit i = true := by
  have hk := wordNeed_toNat (n := n) hj
  unfold wordHas
  rw [and_eq_iff]
  constructor
  · intro h i hi hlt
    exact h i hi (by rw [firstBits_bit (by omega) i, hk]; exact decide_eq_true (by omega))
  · intro h i hi hm
    rw [firstBits_bit (by omega) i, hk] at hm
    exact h i hi (by have := of_decide_eq_true hm; omega)

/-- Whether a category's flags have every type below `n`. -/
@[inline] def allFlags (w0 w1 w2 w3 n : UInt64) : Bool := wordHas w0 n 0 && wordHas w1 n 1 && wordHas w2 n 2 && wordHas w3 n 3

theorem allFlags_iff {w0 w1 w2 w3 n : UInt64} :
    allFlags w0 w1 w2 w3 n = true ↔ ∀ t, t < n.toNat → flagOf w0 w1 w2 w3 t = true := by
  unfold allFlags
  simp only [Bool.and_eq_true]
  rw [wordHas_iff (by decide), wordHas_iff (by decide), wordHas_iff (by decide), wordHas_iff (by decide)]
  simp only [show (0 : UInt64).toNat = 0 from rfl, show (1 : UInt64).toNat = 1 from rfl, show (2 : UInt64).toNat = 2 from rfl,
    show (3 : UInt64).toNat = 3 from rfl]
  constructor
  · intro ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ t ht
    have hi : t % 64 < 64 := Nat.mod_lt _ (by decide)
    unfold flagOf
    have : t / 64 = 0 ∨ t / 64 = 1 ∨ t / 64 = 2 ∨ t / 64 ≥ 3 := by omega
    rcases this with h | h | h | h
    · simp only [h, ↓reduceIte]
      exact h0 _ hi (by omega)
    · simp only [h, ↓reduceIte, Nat.reduceEqDiff]
      exact h1 _ hi (by omega)
    · simp only [h, ↓reduceIte, Nat.reduceEqDiff]
      exact h2 _ hi (by omega)
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      exact h3 _ hi (by omega)
  · intro h
    have g : ∀ k i, 64 * k + i < n.toNat → flagOf w0 w1 w2 w3 (64 * k + i) = true := fun k i hl => h _ hl
    refine ⟨⟨⟨fun i hi hl => ?_, fun i hi hl => ?_⟩, fun i hi hl => ?_⟩, fun i hi hl => ?_⟩
    · have := g 0 i hl
      unfold flagOf at this
      rwa [show (64 * 0 + i) / 64 = 0 by omega, show (64 * 0 + i) % 64 = i by omega] at this
    · have := g 1 i hl
      unfold flagOf at this
      rwa [show (64 * 1 + i) / 64 = 1 by omega, show (64 * 1 + i) % 64 = i by omega] at this
    · have := g 2 i hl
      unfold flagOf at this
      rwa [show (64 * 2 + i) / 64 = 2 by omega, show (64 * 2 + i) % 64 = i by omega] at this
    · have := g 3 i hl
      unfold flagOf at this
      rwa [show (64 * 3 + i) / 64 = 3 by omega, show (64 * 3 + i) % 64 = i by omega] at this

/-- A meta-block's end check: every block type occurred. -/
@[inline] def seenOk (st : Cmd) (nL nI nD : UInt64) : Bool :=
  allFlags st.flags.fL0 st.flags.fL1 st.flags.fL2 st.flags.fL3 nL && allFlags st.flags.fI0 st.flags.fI1 st.flags.fI2 st.flags.fI3 nI &&
    allFlags st.flags.fD0 st.flags.fD1 st.flags.fD2 st.flags.fD3 nD

private theorem uses_iff {w0 w1 w2 w3 cur prev count : UInt64} {st : BlockState} {c : BlockCategory}
    (h : BlockRel w0 w1 w2 w3 cur prev count st c) {n : UInt64} (hn : n.toNat = c.n) (hc : c.n ≤ 256) :
    allFlags w0 w1 w2 w3 n = true ↔ usesEveryType c st = true := by
  rw [allFlags_iff, hn]
  unfold usesEveryType
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem]
  exact ⟨fun hall t ht => (h.flags t (by omega)).mp (hall t ht), fun hall t ht => (h.flags t (by omega)).mpr (hall t ht)⟩

/-- The check says what the spec checks. -/
theorem seenOk_iff {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {st : Cmd} {s : CommandState} (hH : HdrRel H m)
    (hrel : Rel w k m st (.command s)) :
    seenOk st H.nL H.nI H.nD = (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy && usesEveryType m.distance s.distance) := by
  have hC := hrel.1
  have hL := uses_iff hC.lRel hH.nL hH.ok.literal.2.1
  have hI := uses_iff hC.iRel hH.nI hH.ok.insertCopy.2.1
  have hD := uses_iff hC.dRel hH.nD hH.ok.distance.2.1
  unfold seenOk
  generalize allFlags st.flags.fL0 st.flags.fL1 st.flags.fL2 st.flags.fL3 H.nL = a1 at hL
  generalize allFlags st.flags.fI0 st.flags.fI1 st.flags.fI2 st.flags.fI3 H.nI = a2 at hI
  generalize allFlags st.flags.fD0 st.flags.fD1 st.flags.fD2 st.flags.fD3 H.nD = a3 at hD
  generalize usesEveryType m.literal s.literal = b1 at hL
  generalize usesEveryType m.insertCopy s.insertCopy = b2 at hI
  generalize usesEveryType m.distance s.distance = b3 at hD
  have e1 : a1 = b1 := Bool.eq_iff_iff.mpr hL
  have e2 : a2 = b2 := Bool.eq_iff_iff.mpr hI
  have e3 : a3 = b3 := Bool.eq_iff_iff.mpr hD
  rw [e1, e2, e3]

/-! ### Steps -/

/-- A command loop's state with nothing in it, to hold a state's place while the real one is written. -/
def Cmd.none : Cmd := ⟨0, 0, ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩,
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ByteArray.empty, 0⟩, .command, 0, 0, .next⟩

/-- A header machine's state with nothing in it. -/
def Hd.none : Hd := ⟨0, 0, 0, .next, .cat, Done.none, .L, .type, true, .L, 0, 0, 0, 0, 0, ByteArray.empty, headNone, nextNone, 0, 0, 0, 0, 0,
  ByteArray.empty, 0, 0, 0, 0, Tab.none, Tab.none, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty, headNone_size,
  nextNone_size⟩

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

/-- The state a take function hands out is the state's own. -/
theorem takeCmd_inv {D : Dec} {c : Cmd} {D0 : Dec} {stop pos : USize} (hc : takeCmd D = (c, D0))
    (h : CmdInv D.H D.k stop D.cmd pos) : CmdInv D.H D.k stop c pos :=
  (show D.cmd = c from congrArg Prod.fst hc) ▸ h

/-- The place in a meta-block's commands: the command loop with the fast loop (`runCmdF`), given what it may assume of
the state, and the check at the commands' end. -/
def stepDCmds (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize)
    (h : CmdInv D.H D.k stop D.cmd pos) : Dec :=
  let H := D.H
  let k := D.k
  let last := D.last
  match hc : takeCmd D with
  | (c, D0) =>
  let r := runCmdF H k a stop hs cmdBudget c pos (takeCmd_inv hc h)
  let rp := r.pos
  match r.status with
  | .next => { D0 with cmd := r, pos := rp, status := .next }
  | .needsInput => { D0 with cmd := r, pos := rp, status := .needsInput }
  | .needsOutput => { D0 with cmd := r, pos := rp, status := .needsOutput }
  | .bad => { D0 with cmd := r, pos := rp, status := .bad }
  | .done =>
    if seenOk r H.nL H.nI H.nD then
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
    {pos : USize} (hrel : DRel D (.cmds w last m p)) (_hp : pos.toNat ≤ stop.toNat) {h : CmdInv D.H D.k stop D.cmd pos} :
    DStepOk S a stop (.cmds w last m p) D pos (stepDCmds a stop hs D pos h) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR, hL⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  have hstep := runCmdF_ok (hs := hs) (K := cmdK w (S.after w last') m) (fun s bs h0 => cmdK_step s bs h0) hH cmdBudget hR h
  have hbad := runCmdF_bad (hs := hs) (K := cmdK w (S.after w last') m) (fun s bs h0 => cmdK_step s bs h0) hH cmdBudget hR h
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmdF H k a stop hs cmdBudget cmd pos h = r at hstep hbad
  cases hst : r.status with
  | next =>
    dsimp only
    obtain ⟨p', hR', h1, h2, h3, h4, h5⟩ := hstep.next hst
    exact ⟨fun _ => ⟨.cmds w last' m p', ⟨ht, hl, hlim, hH, hR', reach_live (h5 []) hL⟩, h1, h2, (fun t => h3 _), trivial, h4,
      fun t => sreach_cmds (h5 _)⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsInput =>
    dsimp only
    obtain ⟨h1, h2, p', hR', h3, h4, h5, h6, h7⟩ := hstep.needsInput hst
    exact ⟨fun e => DStatus.noConfusion e, fun _ => ⟨h1, h2, .cmds w last' m p', ⟨ht, hl, hlim, hH, hR', reach_live (h6 []) hL⟩,
      (fun t => h3 _), h4, trivial,
      (fun _ _ e => SPhase.noConfusion e), h5, (fun t => sreach_cmds (h6 _)), short_cmds h7⟩, fun e => DStatus.noConfusion e,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsOutput =>
    dsimp only
    obtain ⟨p', hR', h1, h2, h3, h4, h5, h6⟩ := hstep.needsOutput hst
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => ⟨.cmds w last' m p',
      ⟨ht, hl, hlim, hH, hR', reach_live (h6 []) hL⟩, h1, h2, (fun t => h3 _),
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
    have hne : s.produced ≠ 0 := by
      have : 1 ≤ s.produced + s.remaining := reach_live (h6 []) hL
      omega
    dsimp only
    by_cases hc : seenOk r H.nL H.nI H.nD = true
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
        exact ⟨fun _ => ⟨.ended ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, w, Or.inl ⟨⟨hwin, hprod, hlim⟩, hne⟩⟩, h1, h2,
          (fun t => (hfin _).trans (S.after_true ..)), trivial, h5,
          fun t => hj _⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      | false =>
        exact ⟨fun _ => ⟨.mblock w ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, Or.inl ⟨⟨hwin, hprod, hlim⟩, hne⟩⟩, h1, h2,
          (fun t => (hfin _).trans (S.after_false ..)), trivial, h5,
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
  D.cmd.pend = 0 ∨ ∃ out : List Nat, RingOk D.cmd.ring D.k.toNat D.cmd.wpos.toNat out ∧ D.cmd.pend.toNat + 16 ≤ 2 ^ D.k.toNat ∧
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
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m p)) (_hp : pos.toNat ≤ stop.toNat)
    {h : CmdInv D.H D.k stop D.cmd pos} :
    (stepDCmds a stop hs D pos h).status = .bad → WinOk (stepDCmds a stop hs D pos h) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR, -⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hstep := runCmdF_ok (hs := hs) (K := cmdK w (specSem.after w last') m) (fun s bs h0 => cmdK_step s bs h0) hH cmdBudget hR h
  have hbad := runCmdF_badWin (hs := hs) (K := cmdK w (specSem.after w last') m) (fun s bs h0 => cmdK_step s bs h0) hH cmdBudget hR h
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmdF H k a stop hs cmdBudget cmd pos h = r at hstep hbad
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
