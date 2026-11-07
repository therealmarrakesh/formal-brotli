module

public import Brotli.Decoder.State
public import Brotli.Decoder.Copy
public import Brotli.Decoder.Order
public import Brotli.Decoder.Fixed

@[expose] public section

/-!
# One step of the command loop

Each place in the command loop has a step, and `StepOk` is what a step must do in the spec's terms. These steps are
the bridge's real test: every result is tied to `rest`, for every future.
-/

namespace Brotli.Decoder

open Brotli.Spec

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

/-- A pause from a place: further down, or as far down with no more bytes waiting. -/
def DownEq (p p' : Phase) (st r : Cmd) : Prop := LexLt (rankC p') (rankC p) ∨ (rankC p' = rankC p ∧ r.pend = st.pend)

/-- Settles `Down` for a move whose places are spelled out. -/
macro "step_down" : tactic => `(tactic| first | exact Or.inl rfl | (simp only [Down, rankC, LexLt]; omega))

/-- A move's bytes: they go on the front of the output, and they're waiting to go out. -/
def OutStep (p p' : Phase) (st r : Cmd) : Prop := ∃ l, p'.out = l ++ p.out ∧ r.pend.toNat = st.pend.toNat + l.length

/-- A buffer holds as many bits as its count. -/
@[simp] theorem BitBuffer.held_length (b : BitBuffer) : b.held.length = b.count.toNat := lowBits_length _ _

/-- What a step must do. Moving on keeps the state tied to `rest`, whatever bits follow. Needing input means the chunk
is used up, and the spec rejects if no more bits come. Needing output means bytes not yet handed over wait. Finishing means MLEN is reached at the start of a command. Rejecting means the spec rejects, whatever bits follow.
Whatever the step does short of rejecting, the place it ends at is where the spec's reading in order takes the place it
started at, whatever bits follow, and needing input means the reading in order has too few bits there. -/
structure StepOk {α : Type} (w k : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (r : Cmd) : Prop where
  next : r.status = .next → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧ Down p p' ∧ OutStep p p' st r ∧
    ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F)
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', Rel w k m r p' ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    rest w m K p' (BitBuffer.mk r.word r.count).held = none ∧ DownEq p p' st r ∧ OutStep p p' st r ∧
    (∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F)) ∧
    CShort w m p' (BitBuffer.mk r.word r.count).held
  needsOutput : r.status = .needsOutput → ∃ p', Rel w k m r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)) ∧
    r.pend.toNat ≠ 0 ∧ DownEq p p' st r ∧ OutStep p p' st r ∧
    ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F)
  done : r.status = .done → ∃ s, Rel w k m r (.command s) ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K (.command s) (stateBits r a r.pos stop F)) ∧
    s.remaining = 0 ∧ OutStep p (.command s) st r ∧ ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) (.command s) (stateBits r a r.pos stop F)
  bad : r.status = .bad → ∀ F, rest w m K p (stateBits st a pos stop F) = none

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize}
  {p : Phase} {st : Cmd} {pos : USize} {r : Cmd}

/-- A step that moved on. -/
theorem StepOk.ofNext (hs : r.status = .next) {p' : Phase} (hrel : Rel w k m r p') (h1 : pos.toNat ≤ r.pos.toNat)
    (h2 : r.pos.toNat ≤ stop.toNat)
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F))
    (hj : ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F))
    (hd : Down p p' := by step_down) (hout : OutStep p p' st r := by exact ⟨[], rfl, rfl⟩) :
    StepOk w k m K a stop p st pos r :=
  ⟨fun _ => ⟨p', hrel, h1, h2, h, hd, hout, hj⟩, fun e => StepStatus.noConfusion (hs.symm.trans e),
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
    (hn : rest w m K p' (BitBuffer.mk r.word r.count).held = none) (hd : DownEq p p' st r) (hout : OutStep p p' st r)
    (hj : ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F))
    (hsh : CShort w m p' (BitBuffer.mk r.word r.count).held) : StepOk w k m K a stop p st pos r :=
  ⟨fun e => StepStatus.noConfusion (hs.symm.trans e), fun _ => ⟨hstop, hle, p', hrel, h, hn, hd, hout, hj, hsh⟩,
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

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
    (hn : rest w m K p (BitBuffer.mk st.word st.count).held = none)
    (hsh : cStep w m p (BitBuffer.mk st.word st.count).held = .short) :
    StepOk w k m K a stop p st pos (markStep st pos .needsInput) :=
  StepOk.ofInput rfl hstop (by rw [hstop]; exact Nat.le_refl _) (hrel.mark _ _) (fun _ => rfl) hn (Or.inr ⟨rfl, rfl⟩) ⟨[], rfl, rfl⟩
    (fun _ => Reach.refl _ _) (CShort.here hsh)

/-- A step that found no room for more bytes to wait, and changed nothing. -/
theorem StepOk.ofFull (hrel : Rel w k m st p) (hp : pos.toNat ≤ stop.toNat) (hfull : st.pend.toNat ≠ 0) :
    StepOk w k m K a stop p st pos (markStep st pos .needsOutput) :=
  ⟨fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e,
    fun _ => ⟨p, hrel.mark _ _, Nat.le_refl _, hp, (fun _ => rfl), hfull, Or.inr ⟨rfl, rfl⟩, ⟨[], rfl, rfl⟩, fun _ => Reach.refl _ _⟩,
    fun e => StepStatus.noConfusion e, fun e => StepStatus.noConfusion e⟩

/-- A move's bytes depend only on what was waiting before it. -/
theorem OutStep.ofPend {p1 p2 : Phase} {st1 : Cmd} (h : OutStep p1 p2 st1 r) (he : st1.pend = st.pend) : OutStep p1 p2 st r := by
  obtain ⟨l, h1, h2⟩ := h
  exact ⟨l, h1, by rw [h2, he]⟩

/-- A pause depends only on what was waiting before it. -/
theorem DownEq.ofPend {p1 p2 : Phase} {st1 : Cmd} (h : DownEq p1 p2 st1 r) (he : st1.pend = st.pend) : DownEq p1 p2 st r := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2.trans he⟩

/-- A step taken after a refill is a step from before it. -/
theorem StepOk.refilled {st1 : Cmd} {pos1 : USize} (h : StepOk w k m K a stop p st1 pos1 r)
    (hb : ∀ F, stateBits st a pos stop F = stateBits st1 a pos1 stop F) (h1 : pos.toNat ≤ pos1.toNat)
    (h2 : pos1.toNat ≤ stop.toNat) (he : st1.pend = st.pend) : StepOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', hrel, h3, h4, h5, h6, h7, h8⟩ := h.next e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6, h7.ofPend he, fun F => by rw [hb]; exact h8 F⟩
  needsInput e := by
    obtain ⟨h3, _, p', hrel, h5, h6, h7, h8, h9, h10⟩ := h.needsInput e
    exact ⟨h3, Nat.le_trans h1 h2, p', hrel, (fun F => by rw [hb]; exact h5 F), h6, h7.ofPend he, h8.ofPend he,
      (fun F => by rw [hb]; exact h9 F), h10⟩
  needsOutput e := by
    obtain ⟨p', hrel, h3, h4, h5, h6, h7, h8, h9⟩ := h.needsOutput e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6, h7.ofPend he, h8.ofPend he,
      fun F => by rw [hb]; exact h9 F⟩
  done e := by
    obtain ⟨s, hrel, h3, h4, h5, h6, h7, h8⟩ := h.done e
    exact ⟨s, hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6, h7.ofPend he, fun F => by rw [hb]; exact h8 F⟩
  bad e := fun F => by rw [hb]; exact h.bad e F

end

/-- A backward copy goes on the front of the output. -/
theorem copyBytes_front (d : Nat) : ∀ (n : Nat) (out : List Nat), ∃ l, copyBytes d n out = l ++ out ∧ l.length = n
  | 0, out => ⟨[], by simp [copyBytes], rfl⟩
  | n + 1, out => by
    obtain ⟨l, h1, h2⟩ := copyBytes_front d n (out.getD (d - 1) 0 :: out)
    refine ⟨l ++ [out.getD (d - 1) 0], ?_, by simp [h2]⟩
    simp only [copyBytes]
    rw [h1]
    simp

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

/-- The room left for bytes to wait. -/
theorem room_sub {k cap pend : USize} (hle : pend.toNat ≤ (room k cap).toNat) :
    (room k cap - pend).toUInt64.toNat = (room k cap).toNat - pend.toNat := by
  rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle)]

/-- The room left for bytes to wait, as a position. -/
theorem room_sub' {k cap pend : USize} (hle : pend.toNat ≤ (room k cap).toNat) :
    (room k cap - pend).toNat = (room k cap).toNat - pend.toNat :=
  USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle)

/-- No room left: some bytes wait. -/
theorem full_ne {k cap pend : USize} (hk : k.toNat ≤ 24) (hk10 : 10 ≤ k.toNat) (h : room k cap ≤ pend) :
    pend.toNat ≠ 0 := by
  have := USize.le_iff_toNat_le.mp h
  have := room_one (cap := cap) hk (Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk10))
  omega

/-- Room left. -/
theorem room_lt {k cap pend : USize} (h : ¬ room k cap ≤ pend) : pend.toNat < (room k cap).toNat := by
  have : ¬ (room k cap).toNat ≤ pend.toNat := fun e => h (USize.le_iff_toNat_le.mpr e)
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
  else if room k st.cap ≤ st.pend then markStep st pos .needsOutput
  else
    let run := (umin st.left (room k st.cap - st.pend).toUInt64).toUSize
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
    (hrunR : st.pend.toNat + run.toNat + 16 ≤ 2 ^ k.toNat)
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
  obtain ⟨l, hl1, hl2⟩ := copyBytes_front d run.toNat s.output
  have hrun' : st.pend.toNat + run.toNat ≤ 2 ^ k.toNat := by omega
  have hpe : (finishCopy (clearRing st) r run (ringSize k) pos).pend.toNat = st.pend.toNat + l.length := by
    rw [hl2]
    exact pend_after hk hrun'
  refine StepOk.ofNext (p' := .copy { s with output := copyBytes d run.toNat s.output } d (n - run.toNat))
    (hd := Or.inr (Or.inr ⟨rfl, show n - run.toNat < n by omega⟩)) (hout := ⟨l, hl1, hpe⟩) rfl
    ⟨?_, htag, ?_, hdn, ?_, hd1, hdw, ?_⟩ (Nat.le_refl _) hp (fun F => ?_)
    (fun F => (cReach_copy w m d _ run.toNat n s (by omega)))
  · refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
    · show (st.pend + run).toNat + 16 ≤ _
      rw [pend_after hk hrun']
      omega
    · show (st.pend + run).toNat ≤ _
      rw [pend_after hk hrun', h4]
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
    exact StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, by omega⟩ (Nat.le_refl _) hp (fun F => rfl)
      (fun F => (Reach.one rfl))
  · rename_i hnz
    have hnzN := u64_ne hnz
    split
    · rename_i hfull
      exact StepOk.ofFull hrel0 hp (full_ne hk hC.k10 hfull)
    · rename_i hroom
      have hplt := room_lt hroom
      have hRl := room_le16 (cap := st.cap) hk (by omega)
      have hguard : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ st.dist.toUSize ∧ st.dist.toUSize ≤ ringSize k := by
        refine ⟨winCheck_of hk hC.ring.size hC.ring.pos_lt, USize.le_iff_toNat_le.mpr ?_, USize.le_iff_toNat_le.mpr ?_⟩
        · rw [usize_ofNat' (by decide), hdU]
          omega
        · rw [hdU, ringSize_toNat hk]
          omega
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hrunU : (umin st.left (room k st.cap - st.pend).toUInt64).toUSize.toNat =
          min st.left.toNat ((room k st.cap).toNat - st.pend.toNat) := by
        rw [word_toUSize (by rw [umin_toNat, room_sub (by omega)]; omega), umin_toNat, room_sub (by omega)]
      generalize (umin st.left (room k st.cap - st.pend).toUInt64).toUSize = run at hrunU ⊢
      have hspec := copyRun_spec (d := st.dist.toUSize) (mask := ringMask k) (size := ringSize k) hk (ringMask_toNat hk)
        (ringSize_toNat hk) (by omega) (by omega) (by omega) run.toNat run st.ring st.wpos st.p1 st.p2 hC.ring.size
        hC.ring.pos_lt
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
    ext := { st0.ext with wordPos := st0.wordPos + run }
    pend := st0.pend + run
    written := usmin (size - USize.ofNat 16) (st0.written + run)
    pos := pos, status := .next }

/-- Writes as much of the word as the window has room for. -/
def stepWord (k : USize) (st : Cmd) (pos : USize) : Cmd :=
  let n := st.wordBuf.usize - st.wordPos
  if n = 0 then { st with tag := .command, pos := pos, status := .next }
  else if room k st.cap ≤ st.pend then markStep st pos .needsOutput
  else
    let run := usmin n (room k st.cap - st.pend)
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
    (hrun0 : run.toNat ≠ 0) (hrunR : st.pend.toNat + run.toNat + 16 ≤ 2 ^ k.toNat)
    (hplen : pending.length = st.wordBuf.size - st.wordPos.toNat)
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
  have hrun' : st.pend.toNat + run.toNat ≤ 2 ^ k.toNat := by omega
  have hpe : (finishWord (clearRing st) r run (ringSize k) pos).pend.toNat = st.pend.toNat + (pending.take run.toNat).reverse.length := by
    rw [List.length_reverse, List.length_take, Nat.min_eq_left (by omega)]
    exact pend_after hk hrun'
  refine StepOk.ofNext (p' := .word { s with output := (pending.take run.toNat).reverse ++ s.output } (pending.drop run.toNat))
    (hd := Or.inr (Or.inr ⟨rfl, show (pending.drop run.toNat).length < pending.length by rw [List.length_drop]; omega⟩))
    (hout := ⟨_, rfl, hpe⟩) rfl
    ⟨?_, htag, ?_, ?_, hsmall, ?_⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => (cReach_word w m _ run.toNat s pending))
  · refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
    · show (st.pend + run).toNat + 16 ≤ _
      rw [pend_after hk hrun']
      omega
    · show (st.pend + run).toNat ≤ ((pending.take run.toNat).reverse ++ s.output).length
      rw [pend_after hk hrun', hlen]
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
    refine StepOk.ofNext (p' := .command s) rfl ⟨{ hC with }, rfl, by simpa using hprod⟩ (Nat.le_refl _) hp (fun F => ?_)
      (fun F => (Reach.one rfl))
    show rest w m K (.word s []) _ = rest w m K (.command s) _
    rw [rest_word_end]
    rfl
  · rename_i hnz
    have hnzN := usize_ne hnz
    split
    · rename_i hfull
      exact StepOk.ofFull hrel0 hp (full_ne hk hC.k10 hfull)
    · rename_i hroom
      have hplt := room_lt hroom
      have hRl := room_le16 (cap := st.cap) hk (by have := hC.win; omega)
      have hroomU : (room k st.cap - st.pend).toNat = (room k st.cap).toNat - st.pend.toNat := room_sub' (by omega)
      have hrunU : (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat =
          min (st.wordBuf.size - st.wordPos.toNat) ((room k st.cap).toNat - st.pend.toNat) := by
        rw [usmin_toNat, hnU, hroomU]
      have hguard : winCheck k st.wpos st.ring = true ∧
          st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ st.wordBuf.size ∧
          st.wordPos.toNat + (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat ≤ 2 ^ 32 - 1 :=
        ⟨winCheck_of hk hC.ring.size hC.ring.pos_lt, by omega, by omega⟩
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hspec := wordRun_spec (buf := st.wordBuf) (mask := ringMask k) hk (ringMask_toNat hk) _
        (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)) st.wordPos
        st.ring st.wpos st.p1 st.p2 hguard.2.1 hguard.2.2 hC.ring.size hC.ring.pos_lt s.output rfl hC.ring hC.ctx hC.bytes
      dsimp only at hspec
      generalize wordRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hspec ⊢
      obtain ⟨h1, h2, h3⟩ := hspec
      have hmoved : ((st.wordBuf.data.toList.drop st.wordPos.toNat).take
          (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat).map UInt8.toNat =
          pending.take (usmin (st.wordBuf.usize - st.wordPos) (room k st.cap - st.pend)).toNat := by
        rw [← hpend, List.map_take]
      rw [hmoved] at h1 h2 h3
      exact word_after hC htag hprod hpend hsmall hwp hp hguard.2.1 (by omega) (by omega) hplen h1 h2 h3

/-! ### The compiled copy and word steps

`stepCopyK` and `stepWordK` are `stepCopy` and `stepWord` with their loops ending in the step's new state itself, so
that the loop's result is never allocated as a record. The proofs are about `stepCopy` and `stepWord`; the `csimp`
theorems prove each equal to its compiled form, and the compiler runs that. -/

/-- `finishCopy` from the loop's result as plain values, written out. -/
@[noinline] def finishCopyS (st0 : Cmd) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (run rsz pos : USize) : Cmd :=
  { st0 with
    ring := ring, wpos := wpos, p1 := p1, p2 := p2
    left := st0.left - run.toUInt64
    pend := st0.pend + run
    written := usmin (rsz - USize.ofNat 16) (st0.written + run)
    pos := pos, status := .next }

/-- `copyRun`, ending in `finishCopyS`. -/
def copyRunK (st0 : Cmd) (run rsz pos0 : USize) (d mask size : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize)
    (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : Cmd :=
  if hn : n = 0 then finishCopyS st0 ring wpos p1 p2 run rsz pos0
  else
    have hb : (ringBack wpos d mask size).toNat < ring.size := by
      rw [ringBack_toNat hk hmask hsz hwp hd1 hd2, hsize]
      exact ringIdx_lt hwp (by omega)
    let byte := ring.uget (ringBack wpos d mask size) hb
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    copyRunK st0 run rsz pos0 d mask size k hk hmask hsz hd1 hd2 (n - USize.ofNat 1) (ringWrite ring wpos byte hr)
      (ringNext wpos mask) byte p1 ((size_ringWrite ring wpos byte hr).trans hsize) hnext
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

theorem copyRunK_eq (st0 : Cmd) (run rsz pos0 : USize) (d mask size : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      copyRunK st0 run rsz pos0 d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp =
        finishCopy st0 (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp) run rsz pos0 := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn : n = 0 := usize_zero hN
    rw [copyRunK, copyRun, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRunK, copyRun, dite_eq_right hn, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

/-- `stepCopy`, with the loop ending in the new state. -/
def stepCopyK (k : USize) (st : Cmd) (pos : USize) : Cmd :=
  if st.left = 0 then { st with tag := .command, pos := pos, status := .next }
  else if room k st.cap ≤ st.pend then markStep st pos .needsOutput
  else
    let run := (umin st.left (room k st.cap - st.pend).toUInt64).toUSize
    let d := st.dist.toUSize
    if h : winCheck k st.wpos st.ring = true ∧ USize.ofNat 1 ≤ d ∧ d ≤ ringSize k then
      let ring := st.ring
      let st0 := clearRing st
      copyRunK st0 run (ringSize k) pos d (ringMask k) (ringSize k) k.toNat (winCheck_k h.1)
        (ringMask_toNat (winCheck_k h.1)) (ringSize_toNat (winCheck_k h.1))
        (by
          have := USize.le_iff_toNat_le.mp h.2.1
          rwa [usize_ofNat' (by decide)] at this)
        (by
          have := USize.le_iff_toNat_le.mp h.2.2
          rwa [ringSize_toNat (winCheck_k h.1)] at this)
        run ring st0.wpos st0.p1 st0.p2 (winCheck_size h.1) (winCheck_pos h.1)
    else markStep st pos .bad

@[csimp] theorem stepCopy_csimp : @stepCopy = @stepCopyK := by
  funext k st pos
  unfold stepCopy stepCopyK
  -- each `split` takes the same branch on both sides, whose conditions are the same
  split
  · rfl
  · split
    · rfl
    · dsimp only
      split
      · exact (copyRunK_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).symm
      · rfl

/-- `finishWord` from the loop's result as plain values, written out. -/
@[noinline] def finishWordS (st0 : Cmd) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (run size pos : USize) : Cmd :=
  { st0 with
    ring := ring, wpos := wpos, p1 := p1, p2 := p2
    ext := { st0.ext with wordPos := st0.wordPos + run }
    pend := st0.pend + run
    written := usmin (size - USize.ofNat 16) (st0.written + run)
    pos := pos, status := .next }

/-- `wordRun`, ending in `finishWordS`. -/
def wordRunK (st0 : Cmd) (run size pos0 : USize) (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k) : Cmd :=
  if hn : n = 0 then finishWordS st0 ring wpos p1 p2 run size pos0
  else
    have hnz := usize_ne hn
    have hpred := usize_pred hn
    let byte := buf.uget idx (by omega)
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    wordRunK st0 run size pos0 buf mask k hk hmask (n - USize.ofNat 1) (idx + USize.ofNat 1) (ringWrite ring wpos byte hr)
      (ringNext wpos mask) byte p1 (by rw [hi]; omega) (by rw [hi]; omega) ((size_ringWrite ring wpos byte hr).trans hsize)
      hnext
termination_by n.toNat
decreasing_by
  omega

theorem wordRunK_eq (st0 : Cmd) (run size pos0 : USize) (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
      (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      wordRunK st0 run size pos0 buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp =
        finishWord st0 (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp) run size pos0 := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n = 0 := usize_zero hN
    rw [wordRunK, wordRun, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [wordRunK, wordRun, dite_eq_right hn, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

/-- `stepWord`, with the loop ending in the new state. -/
def stepWordK (k : USize) (st : Cmd) (pos : USize) : Cmd :=
  let n := st.wordBuf.usize - st.wordPos
  if n = 0 then { st with tag := .command, pos := pos, status := .next }
  else if room k st.cap ≤ st.pend then markStep st pos .needsOutput
  else
    let run := usmin n (room k st.cap - st.pend)
    if h : winCheck k st.wpos st.ring = true ∧ st.wordPos.toNat + run.toNat ≤ st.wordBuf.size ∧
        st.wordPos.toNat + run.toNat ≤ 2 ^ 32 - 1 then
      let ring := st.ring
      let st0 := clearRing st
      wordRunK st0 run (ringSize k) pos st0.wordBuf (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) run
        st0.wordPos ring st0.wpos st0.p1 st0.p2 h.2.1 h.2.2 (winCheck_size h.1) (winCheck_pos h.1)
    else markStep st pos .bad

@[csimp] theorem stepWord_csimp : @stepWord = @stepWordK := by
  funext k st pos
  unfold stepWord stepWordK
  dsimp only
  split
  · rfl
  · split
    · rfl
    · split
      · exact (wordRunK_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).symm
      · rfl

end Brotli.Decoder
