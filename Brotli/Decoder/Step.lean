import Brotli.Decoder.State
import Brotli.Decoder.Copy

/-!
# One step of the command loop

Each place in the command loop has a step, and `StepOk` is what a step must do in the spec's terms. These steps are
the bridge's real test: every result is tied to `rest`, for every future.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- How far a place is along a command: steps within a command lower this, and the start of a command is the lowest. -/
def rankC : Phase → Nat × Nat
  | .command _ => (0, 0)
  | .copy _ _ n => (1, n)
  | .word _ pending => (1, pending.length)
  | .distanceSymbol .. => (2, 0)
  | .distance .. => (3, 0)
  | .literals _ _ _ _ _ n lit _ => (4, 2 * n + if lit.count = 0 then 1 else 0)
  | .literalSymbol .. => (4, 0)
  | .copyLength .. => (5, 0)
  | .insertCopy .. => (6, 0)

/-- A move from a place to the next: down a command, or out of a command's start. -/
def Down (p p' : Phase) : Prop := (rankC p).1 = 0 ∨ LexLt (rankC p') (rankC p)

/-- A pause from a place: the same place or further down. -/
def DownEq (p p' : Phase) : Prop := (rankC p).1 = 0 ∨ LexLt (rankC p') (rankC p) ∨ rankC p' = rankC p

/-- Settles `Down` for a move whose places are spelled out. -/
macro "step_down" : tactic => `(tactic| first | exact Or.inl rfl | (simp only [Down, rankC, LexLt]; omega))

/-- What a step must do. Moving on keeps the state tied to `rest`, whatever bits follow. Needing input means the chunk
is used up, and the spec rejects if no more bits come. Needing output means the window is full of bytes not yet handed
over. Finishing means MLEN is reached at the start of a command. Rejecting means the spec rejects, whatever bits follow. -/
structure StepOk {α : Type} (w k : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (r : Cmd) : Prop where
  next : r.status = .next → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧ Down p p'
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', Rel w k m r p' ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    rest w m K p' (BitBuffer.mk r.word r.count).held = none ∧ DownEq p p'
  needsOutput : r.status = .needsOutput → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    r.pend.toNat = 2 ^ k ∧ DownEq p p'
  done : r.status = .done → ∃ s, Rel w k m r (.command s) ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K (.command s) (stateBits r a r.pos stop F)) ∧
    s.remaining = 0
  bad : r.status = .bad → ∀ F, rest w m K p (stateBits st a pos stop F) = none

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize}
  {p : Phase} {st : Cmd} {pos : USize} {r : Cmd}

/-- A step that moved on. -/
theorem StepOk.ofNext (hs : r.status = .next) {p' : Phase} (hrel : Rel w k m r p') (h1 : pos.toNat ≤ r.pos.toNat)
    (h2 : r.pos.toNat ≤ stop.toNat)
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F))
    (hd : Down p p' := by step_down) :
    StepOk w k m K a stop p st pos r :=
  ⟨fun _ => ⟨p', hrel, h1, h2, h, hd⟩, fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

/-- A step that rejected. -/
theorem StepOk.ofBad (hs : r.status = .bad) (h : ∀ F, rest w m K p (stateBits st a pos stop F) = none) :
    StepOk w k m K a stop p st pos r :=
  ⟨fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e), fun _ => h⟩

/-- A step that ran out of input. -/
theorem StepOk.ofInput (hs : r.status = .needsInput) (hstop : r.pos = stop) (hle : pos.toNat ≤ stop.toNat) {p' : Phase}
    (hrel : Rel w k m r p')
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F))
    (hn : rest w m K p' (BitBuffer.mk r.word r.count).held = none) (hd : DownEq p p') : StepOk w k m K a stop p st pos r :=
  ⟨fun e => StepStatus.noConfusion (hs.symm.trans e), fun _ => ⟨hstop, hle, p', hrel, h, hn, hd⟩,
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

/-- A place is as far down as itself. -/
theorem DownEq.self (p : Phase) : DownEq p p := Or.inr (Or.inr rfl)

/-- The place a copy is at. -/
theorem copyPhase_rank {w : Nat} {s : CommandState} {clen dcode d : Nat} {q : Phase} (h : copyPhase w s clen dcode d = some q) :
    (rankC q).1 = 1 := by
  unfold copyPhase at h
  dsimp only at h
  split at h
  · obtain ⟨word, _, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · cases h
    · cases h
      rfl
  · split at h
    · cases h
    · cases h
      rfl

/-- A read that fell short and changed nothing. -/
theorem StepOk.ofShort (hrel : Rel w k m st p) (hstop : pos = stop)
    (hn : rest w m K p (BitBuffer.mk st.word st.count).held = none) :
    StepOk w k m K a stop p st pos (markStep st pos .needsInput) :=
  StepOk.ofInput rfl hstop (by rw [hstop]; exact Nat.le_refl _) (hrel.mark _ _) (fun _ => rfl) hn (DownEq.self p)

/-- A step that found the window full, and changed nothing. -/
theorem StepOk.ofFull (hrel : Rel w k m st p) (hp : pos.toNat ≤ stop.toNat) (hfull : st.pend.toNat = 2 ^ k) :
    StepOk w k m K a stop p st pos (markStep st pos .needsOutput) :=
  ⟨fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e,
    fun _ => ⟨p, hrel.mark _ _, Nat.le_refl _, hp, fun _ => rfl, hfull, DownEq.self p⟩,
    fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e⟩

/-- A step taken after a refill is a step from before it. -/
theorem StepOk.refilled {st1 : Cmd} {pos1 : USize} (h : StepOk w k m K a stop p st1 pos1 r)
    (hb : ∀ F, stateBits st a pos stop F = stateBits st1 a pos1 stop F) (h1 : pos.toNat ≤ pos1.toNat)
    (h2 : pos1.toNat ≤ stop.toNat) : StepOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', hrel, h3, h4, h5, h6⟩ := h.next e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6⟩
  needsInput e := by
    obtain ⟨h3, _, p', hrel, h5, h6, h7⟩ := h.needsInput e
    exact ⟨h3, Nat.le_trans h1 h2, p', hrel, (fun F => by rw [hb]; exact h5 F), h6, h7⟩
  needsOutput e := by
    obtain ⟨p', hrel, h3, h4, h5, h6, h7⟩ := h.needsOutput e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6, h7⟩
  done e := by
    obtain ⟨s, hrel, h3, h4, h5, h6⟩ := h.done e
    exact ⟨s, hrel, Nat.le_trans h1 h3, h4, fun F => by rw [hb]; exact h5 F, h6⟩
  bad e := fun F => by rw [hb]; exact h.bad e F

end

/-- `copyBytes` in two runs. -/
theorem copyBytes_add (d : Nat) : ∀ (a b : Nat) (out : List Nat),
    copyBytes d (a + b) out = copyBytes d b (copyBytes d a out)
  | 0, b, out => by simp [copyBytes]
  | a + 1, b, out => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [copyBytes]
    exact copyBytes_add d a b _

theorem usize_ofNat' {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

theorem u64_ofNat {n : Nat} (h : n < 2 ^ 32) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by omega)

theorem u64_zero {x : UInt64} (h : x = 0) : x.toNat = 0 := by
  rw [h]
  rfl

theorem u64_ne {x : UInt64} (h : ¬ x = 0) : x.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by rw [e]; rfl))

/-- The room left in the window. -/
theorem room_toNat {k pend : USize} (hk : k.toNat ≤ 24) (hle : pend.toNat ≤ 2 ^ k.toNat) :
    (ringSize k - pend).toUInt64.toNat = 2 ^ k.toNat - pend.toNat := by
  rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [ringSize_toNat hk]; exact hle)),
    ringSize_toNat hk]

/-- A window that is full, in fixed-width terms. -/
theorem full_iff {k pend : USize} (hk : k.toNat ≤ 24) (hle : pend.toNat ≤ 2 ^ k.toNat) (h : ringSize k ≤ pend) :
    pend.toNat = 2 ^ k.toNat := by
  have := USize.le_iff_toNat_le.mp h
  rw [ringSize_toNat hk] at this
  omega

/-- A window that isn't full. -/
theorem room_pos {k pend : USize} (hk : k.toNat ≤ 24) (h : ¬ ringSize k ≤ pend) : pend.toNat < 2 ^ k.toNat := by
  have : ¬ (ringSize k).toNat ≤ pend.toNat := fun e => h (USize.le_iff_toNat_le.mpr e)
  rw [ringSize_toNat hk] at this
  omega

/-! ### A backward copy -/

/-- A copy step's new state, around the loop's result. Not inlined, so the state stays live across the loop and is
reused here. -/
@[noinline] def finishCopy (st0 : Cmd) (r : CopyRun) (run size pos : USize) : Cmd :=
  { st0 with
    ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
    left := st0.left - run.toUInt64
    pend := st0.pend + run
    written := usmin (size - USize.ofNat 16) (st0.written + run)
    pos := pos, status := .next }

/-- Copies as much as the window has room for. -/
def stepCopy (k : USize) (st : Cmd) (pos : USize) : Cmd :=
  if st.left = 0 then { st with tag := .command, pos := pos, status := .next }
  else if ringSize k ≤ st.pend then markStep st pos .needsOutput
  else
    let run := (umin st.left (ringSize k - st.pend).toUInt64).toUSize
    let d := st.dist.toUSize
    if h : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ d ∧ d ≤ ringSize k then
      let ring := st.ring
      let st0 := clearRing st
      let r := copyRun d (ringMask k) (ringSize k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1))
        (ringSize_toNat (winCheck_k h.1))
        (by
          have := USize.le_iff_toNat_le.mp h.2.1
          rwa [usize_ofNat' (by decide)] at this)
        (by
          have := USize.le_iff_toNat_le.mp h.2.2
          rwa [ringSize_toNat (winCheck_k h.1)] at this)
        run ring st0.wpos st0.p1 st0.p2 (winCheck_size h.1) (winCheck_pos h.1)
      finishCopy st0 r run (ringSize k) pos
    else markStep st pos .bad

/-- What follows the copy loop, whatever it returned. -/
private theorem copy_after {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd} {pos run : USize} {r : CopyRun}
    (hC : Core w k.toNat m st s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (htag : st.tag = .copy) (hprod : s.produced = s.output.length + n) (hdn : st.dist.toNat = d) (hleft : st.left.toNat = n)
    (hd1 : 1 ≤ d) (hdw : d ≤ w) (hdo : d ≤ s.output.length) (hp : pos.toNat ≤ stop.toNat) (hrunN : run.toNat ≤ n) (hrun0 : run.toNat ≠ 0)
    (hrunR : st.pend.toNat + run.toNat ≤ 2 ^ k.toNat)
    (h1 : RingOk r.ring k.toNat r.wpos.toNat (copyBytes d run.toNat s.output))
    (h2 : contextBytes (copyBytes d run.toNat s.output) = (r.p1.toNat, r.p2.toNat))
    (h3 : ∀ b ∈ copyBytes d run.toNat s.output, b < 256)
    (h4 : (copyBytes d run.toNat s.output).length = s.output.length + run.toNat) :
    StepOk w k.toNat m K a stop (.copy s d n) st pos (finishCopy (clearRing st) r run (ringSize k) pos) := by
  have hk := hC.k24
  have hwin := hC.win
  have hwri := hC.written
  have hpO := hC.pendOut
  have hle := hC.pendLe
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hrunU : run.toUInt64.toNat = run.toNat := USize.toNat_toUInt64 _
  refine StepOk.ofNext (p' := .copy { s with output := copyBytes d run.toNat s.output } d (n - run.toNat))
    (hd := Or.inr (Or.inr ⟨rfl, show n - run.toNat < n by omega⟩)) rfl
    ⟨?_, htag, ?_, hdn, ?_, hd1, hdw, ?_⟩ (Nat.le_refl _) hp fun F => ?_
  · refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
    · show (st.pend + run).toNat ≤ _
      rw [pend_after hk hrunR]
      omega
    · show (st.pend + run).toNat ≤ _
      rw [pend_after hk hrunR, h4]
      omega
    · show (usmin (ringSize k - USize.ofNat 16) (st.written + run)).toNat = _
      rw [written_after hk hwin (by omega) (by omega) rfl, h4, hwri]
      omega
  · show s.produced = (copyBytes d run.toNat s.output).length + (n - run.toNat)
    rw [h4]
    omega
  · show (st.left - run.toUInt64).toNat = n - run.toNat
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hrunU]; omega)), hrunU, hleft]
  · show d ≤ (copyBytes d run.toNat s.output).length
    rw [h4]
    omega
  · show K { s with output := copyBytes d n s.output } _ =
      K { s with output := copyBytes d (n - run.toNat) (copyBytes d run.toNat s.output) } _
    have hsplit : copyBytes d n s.output = copyBytes d (n - run.toNat) (copyBytes d run.toNat s.output) := by
      rw [← copyBytes_add]
      congr 1
      omega
    rw [hsplit]
    rfl

/-- The copy step does its job. -/
theorem stepCopy_ok {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd}
    {pos : USize} (hrel : Rel w k.toNat m st (.copy s d n)) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m K a stop (.copy s d n) st pos (stepCopy k st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hdist, hleft, hd1, hdw, hdo⟩ := hrel
  have hk := hC.k24
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k.toNat := Nat.two_pow_pos _
  have hwin := hC.win
  have hple := hC.pendLe
  have hdLt32 : st.dist.toNat < 2 ^ 32 := by omega
  have hdU : st.dist.toUSize.toNat = st.dist.toNat := word_toUSize hdLt32
  unfold stepCopy
  split
  · rename_i hz
    have hn0 : n = 0 := by
      have := u64_zero hz
      omega
    subst hn0
    refine StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, by omega⟩ (Nat.le_refl _) hp fun F => rfl
  · rename_i hnz
    have hnzN := u64_ne hnz
    split
    · rename_i hfull
      exact StepOk.ofFull hrel0 hp (full_iff hk hple hfull)
    · rename_i hroom
      have hplt := room_pos hk hroom
      have hguard : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ st.dist.toUSize ∧ st.dist.toUSize ≤ ringSize k := by
        refine ⟨winCheck_of hk hC.ring.size hC.ring.pos_lt, USize.le_iff_toNat_le.mpr ?_, USize.le_iff_toNat_le.mpr ?_⟩
        · rw [usize_ofNat' (by decide), hdU]
          omega
        · rw [hdU, ringSize_toNat hk]
          omega
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hrunU : (umin st.left (ringSize k - st.pend).toUInt64).toUSize.toNat =
          min st.left.toNat (2 ^ k.toNat - st.pend.toNat) := by
        rw [word_toUSize (by rw [umin_toNat, room_toNat hk hple]; omega), umin_toNat, room_toNat hk hple]
      generalize (umin st.left (ringSize k - st.pend).toUInt64).toUSize = run at hrunU ⊢
      have hspec := copyRun_spec (d := st.dist.toUSize) (mask := ringMask k) (size := ringSize k) hk (ringMask_toNat hk)
        (ringSize_toNat hk) (by omega) (by omega) run.toNat run st.ring st.wpos st.p1 st.p2 hC.ring.size hC.ring.pos_lt
        s.output rfl (by omega) hC.ring hC.ctx hC.bytes
      dsimp only at hspec
      generalize copyRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hspec ⊢
      rw [hdU, hdist] at hspec
      obtain ⟨h1, h2, h3, h4⟩ := hspec
      exact copy_after hC htag hprod hdist hleft hd1 hdw hdo hp (by omega) (by omega) (by omega) h1 h2 h3 h4

/-! ### A dictionary word -/

/-- A word step's new state, around the loop's result. -/
@[noinline] def finishWord (st0 : Cmd) (r : CopyRun) (run size pos : USize) : Cmd :=
  { st0 with
    ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
    wordPos := st0.wordPos + run
    pend := st0.pend + run
    written := usmin (size - USize.ofNat 16) (st0.written + run)
    pos := pos, status := .next }

/-- Writes as much of the word as the window has room for. -/
def stepWord (k : USize) (st : Cmd) (pos : USize) : Cmd :=
  let n := st.wordBuf.usize - st.wordPos
  if n = 0 then { st with tag := .command, pos := pos, status := .next }
  else if ringSize k ≤ st.pend then markStep st pos .needsOutput
  else
    let run := usmin n (ringSize k - st.pend)
    if h : winCheck k st.wpos st.ring = true ∧ st.wordPos.toNat + run.toNat ≤ st.wordBuf.size ∧
        st.wordPos.toNat + run.toNat ≤ 2 ^ 32 - 1 then
      let ring := st.ring
      let st0 := clearRing st
      let r := wordRun st0.wordBuf (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) run st0.wordPos ring
        st0.wpos st0.p1 st0.p2 h.2.1 h.2.2 (winCheck_size h.1) (winCheck_pos h.1)
      finishWord st0 r run (ringSize k) pos
    else markStep st pos .bad

/-- What follows the word loop, whatever it returned. -/
private theorem word_after {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {pending : List Nat} {st : Cmd} {pos run : USize} {r : CopyRun}
    (hC : Core w k.toNat m st s.output s.remaining s.distances s.insertCopy s.literal s.distance)
    (htag : st.tag = .word) (hprod : s.produced = s.output.length + pending.length)
    (hpend : (st.wordBuf.data.toList.drop st.wordPos.toNat).map UInt8.toNat = pending) (hsmall : st.wordBuf.size ≤ 38)
    (hwp : st.wordPos.toNat ≤ st.wordBuf.size) (hp : pos.toNat ≤ stop.toNat) (hrunN : st.wordPos.toNat + run.toNat ≤ st.wordBuf.size)
    (hrun0 : run.toNat ≠ 0) (hrunR : st.pend.toNat + run.toNat ≤ 2 ^ k.toNat) (hplen : pending.length = st.wordBuf.size - st.wordPos.toNat)
    (h1 : RingOk r.ring k.toNat r.wpos.toNat ((pending.take run.toNat).reverse ++ s.output))
    (h2 : contextBytes ((pending.take run.toNat).reverse ++ s.output) = (r.p1.toNat, r.p2.toNat))
    (h3 : ∀ b ∈ (pending.take run.toNat).reverse ++ s.output, b < 256) :
    StepOk w k.toNat m K a stop (.word s pending) st pos (finishWord (clearRing st) r run (ringSize k) pos) := by
  have hk := hC.k24
  have hwin := hC.win
  have hwri := hC.written
  have hpO := hC.pendOut
  have hle := hC.pendLe
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hnewPos : (st.wordPos + run).toNat = st.wordPos.toNat + run.toNat := by
    rw [USize.toNat_add, ← USize.size_eq_two_pow]
    have := USize.le_size
    exact Nat.mod_eq_of_lt (by omega)
  have hlen : ((pending.take run.toNat).reverse ++ s.output).length = s.output.length + run.toNat := by
    simp only [List.length_append, List.length_reverse, List.length_take]
    omega
  refine StepOk.ofNext (p' := .word { s with output := (pending.take run.toNat).reverse ++ s.output } (pending.drop run.toNat))
    (hd := Or.inr (Or.inr ⟨rfl, show (pending.drop run.toNat).length < pending.length by rw [List.length_drop]; omega⟩)) rfl
    ⟨?_, htag, ?_, ?_, hsmall, ?_⟩ (Nat.le_refl _) hp fun F => ?_
  · refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
    · show (st.pend + run).toNat ≤ _
      rw [pend_after hk hrunR]
      omega
    · show (st.pend + run).toNat ≤ ((pending.take run.toNat).reverse ++ s.output).length
      rw [pend_after hk hrunR, hlen]
      omega
    · show (usmin (ringSize k - USize.ofNat 16) (st.written + run)).toNat = min w ((pending.take run.toNat).reverse ++ s.output).length
      rw [written_after hk hwin (by omega) (by omega) rfl, hlen, hwri]
      omega
  · show s.produced = ((pending.take run.toNat).reverse ++ s.output).length + (pending.drop run.toNat).length
    rw [hlen, List.length_drop]
    omega
  · show ((st.wordBuf.data.toList.drop (st.wordPos + run).toNat)).map UInt8.toNat = _
    rw [hnewPos, ← hpend, ← List.drop_drop, List.map_drop]
  · show (st.wordPos + run).toNat ≤ st.wordBuf.size
    rw [hnewPos]
    exact hrunN
  · show K { s with output := pending.reverse ++ s.output } _ =
      K { s with output := (pending.drop run.toNat).reverse ++ ((pending.take run.toNat).reverse ++ s.output) } _
    have hsplit : pending.reverse ++ s.output =
        (pending.drop run.toNat).reverse ++ ((pending.take run.toNat).reverse ++ s.output) := by
      rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]
    rw [hsplit]
    rfl

/-- The word step does its job. -/
theorem stepWord_ok {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {pending : List Nat} {st : Cmd} {pos : USize}
    (hrel : Rel w k.toNat m st (.word s pending)) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m K a stop (.word s pending) st pos (stepWord k st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hpend, hsmall, hwp⟩ := hrel
  have hk := hC.k24
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k.toNat := Nat.two_pow_pos _
  have hple := hC.pendLe
  have hbs : st.wordBuf.data.toList.length = st.wordBuf.size := by
    show st.wordBuf.data.toList.length = st.wordBuf.data.size
    simp
  have hplen : pending.length = st.wordBuf.size - st.wordPos.toNat := by
    rw [← hpend]
    simp [hbs]
  have hsizeU : st.wordBuf.usize.toNat = st.wordBuf.size := usize_ofNat' (by omega)
  have hnU : (st.wordBuf.usize - st.wordPos).toNat = st.wordBuf.size - st.wordPos.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hsizeU]; exact hwp)), hsizeU]
  unfold stepWord
  dsimp only
  split
  · rename_i hz
    have hnil : pending = [] := by
      apply List.eq_nil_of_length_eq_zero
      have : (st.wordBuf.usize - st.wordPos).toNat = 0 := by rw [hz]; rfl
      omega
    subst hnil
    refine StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, by simpa using hprod⟩ (Nat.le_refl _) hp fun F => ?_
    show rest w m K (.word s []) _ = rest w m K (.command s) _
    rw [rest_word_end]
    rfl
  · rename_i hnz
    have hnzN := usize_ne hnz
    split
    · rename_i hfull
      exact StepOk.ofFull hrel0 hp (full_iff hk hple hfull)
    · rename_i hroom
      have hplt := room_pos hk hroom
      have hroomU : (ringSize k - st.pend).toNat = 2 ^ k.toNat - st.pend.toNat := room_toNat hk hple
      have hrunU : (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)).toNat =
          min (st.wordBuf.size - st.wordPos.toNat) (2 ^ k.toNat - st.pend.toNat) := by
        rw [usmin_toNat, hnU, hroomU]
      have hguard : winCheck k st.wpos st.ring = true ∧
          st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)).toNat ≤ st.wordBuf.size ∧
          st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)).toNat ≤ 2 ^ 32 - 1 :=
        ⟨winCheck_of hk hC.ring.size hC.ring.pos_lt, by omega, by omega⟩
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hspec := wordRun_spec (buf := st.wordBuf) (mask := ringMask k) hk (ringMask_toNat hk) _
        (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)) st.wordPos
        st.ring st.wpos st.p1 st.p2 hguard.2.1 hguard.2.2 hC.ring.size hC.ring.pos_lt s.output rfl hC.ring hC.ctx hC.bytes
      dsimp only at hspec
      generalize wordRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hspec ⊢
      obtain ⟨h1, h2, h3⟩ := hspec
      have hmoved : ((st.wordBuf.data.toList.drop st.wordPos.toNat).take
          (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)).toNat).map UInt8.toNat =
          pending.take (usmin (st.wordBuf.usize - st.wordPos) (ringSize k - st.pend)).toNat := by
        rw [← hpend, List.map_take]
      rw [hmoved] at h1 h2 h3
      exact word_after hC htag hprod hpend hsmall hwp hp hguard.2.1 (by omega) (by omega) hplen h1 h2 h3

end Brotli.Decoder
