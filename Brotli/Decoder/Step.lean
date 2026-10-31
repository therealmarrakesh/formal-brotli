import Brotli.Decoder.State
import Brotli.Decoder.Copy

/-!
# One step of the command loop

Each place in the command loop has a step, and `StepOk` is what a step must do in the spec's terms. These steps are
the bridge's real test: every result is tied to `rest`, for every future.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- What a step must do. Moving on keeps the state tied to `rest`, whatever bits follow. Needing input means the chunk
is used up, and the spec rejects if no more bits come. Needing output means the window is full of bytes not yet handed
over. Finishing means MLEN is reached at the start of a command. Rejecting means the spec rejects, whatever bits follow. -/
structure StepOk {α : Type} (w k : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (r : Stepped) : Prop where
  next : r.status = .next → ∃ p', Rel w k m r.st p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r.st a r.pos stop F)
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', Rel w k m r.st p' ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r.st a r.pos stop F)) ∧
    rest w m K p' (BitBuffer.mk r.st.word r.st.count).held = none
  needsOutput : r.status = .needsOutput → ∃ p', Rel w k m r.st p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r.st a r.pos stop F)) ∧
    r.st.pend.toNat = 2 ^ k
  done : r.status = .done → ∃ s, Rel w k m r.st (.command s) ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K (.command s) (stateBits r.st a r.pos stop F)) ∧
    s.remaining = 0
  bad : r.status = .bad → ∀ F, rest w m K p (stateBits st a pos stop F) = none

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize}
  {p : Phase} {st : Cmd} {pos : USize} {r : Stepped}

/-- A step that moved on. -/
theorem StepOk.ofNext (hs : r.status = .next) {p' : Phase} (hrel : Rel w k m r.st p') (h1 : pos.toNat ≤ r.pos.toNat)
    (h2 : r.pos.toNat ≤ stop.toNat)
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r.st a r.pos stop F)) :
    StepOk w k m K a stop p st pos r :=
  ⟨fun _ => ⟨p', hrel, h1, h2, h⟩, fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

/-- A step that rejected. -/
theorem StepOk.ofBad (hs : r.status = .bad) (h : ∀ F, rest w m K p (stateBits st a pos stop F) = none) :
    StepOk w k m K a stop p st pos r :=
  ⟨fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e), fun _ => h⟩

/-- A step that ran out of input. -/
theorem StepOk.ofInput (hs : r.status = .needsInput) (hstop : r.pos = stop) (hle : pos.toNat ≤ stop.toNat) {p' : Phase}
    (hrel : Rel w k m r.st p')
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r.st a r.pos stop F))
    (hn : rest w m K p' (BitBuffer.mk r.st.word r.st.count).held = none) : StepOk w k m K a stop p st pos r :=
  ⟨fun e => StepStatus.noConfusion (hs.symm.trans e), fun _ => ⟨hstop, hle, p', hrel, h, hn⟩,
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

/-- A read that fell short and changed nothing. -/
theorem StepOk.ofShort (hrel : Rel w k m st p) (hstop : pos = stop)
    (hn : rest w m K p (BitBuffer.mk st.word st.count).held = none) :
    StepOk w k m K a stop p st pos ⟨st, pos, .needsInput⟩ :=
  StepOk.ofInput rfl hstop (by rw [hstop]; exact Nat.le_refl _) hrel (fun _ => rfl) hn

/-- A step taken after a refill is a step from before it. -/
theorem StepOk.refilled {st1 : Cmd} {pos1 : USize} (h : StepOk w k m K a stop p st1 pos1 r)
    (hb : ∀ F, stateBits st a pos stop F = stateBits st1 a pos1 stop F) (h1 : pos.toNat ≤ pos1.toNat)
    (h2 : pos1.toNat ≤ stop.toNat) : StepOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', hrel, h3, h4, h5⟩ := h.next e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, fun F => by rw [hb]; exact h5 F⟩
  needsInput e := by
    obtain ⟨h3, _, p', hrel, h5, h6⟩ := h.needsInput e
    exact ⟨h3, Nat.le_trans h1 h2, p', hrel, fun F => by rw [hb]; exact h5 F, h6⟩
  needsOutput e := by
    obtain ⟨p', hrel, h3, h4, h5, h6⟩ := h.needsOutput e
    exact ⟨p', hrel, Nat.le_trans h1 h3, h4, fun F => by rw [hb]; exact h5 F, h6⟩
  done e := by
    obtain ⟨s, hrel, h3, h4, h5, h6⟩ := h.done e
    exact ⟨s, hrel, Nat.le_trans h1 h3, h4, fun F => by rw [hb]; exact h5 F, h6⟩
  bad e := fun F => by rw [hb]; exact h.bad e F

/-- Two steps in a row, the first moving on, are one step. -/
theorem StepOk.trans {r1 : Stepped} {p1 : Phase} (hle : pos.toNat ≤ r1.pos.toNat)
    (h : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p1 (stateBits r1.st a r1.pos stop F))
    (h2 : StepOk w k m K a stop p1 r1.st r1.pos r) : StepOk w k m K a stop p st pos r where
  next e := by
    obtain ⟨p', hrel, h3, h4, h5⟩ := h2.next e
    exact ⟨p', hrel, Nat.le_trans hle h3, h4, fun F => by rw [h]; exact h5 F⟩
  needsInput e := by
    obtain ⟨h3, h6, p', hrel, h5, h7⟩ := h2.needsInput e
    exact ⟨h3, Nat.le_trans hle h6, p', hrel, fun F => by rw [h]; exact h5 F, h7⟩
  needsOutput e := by
    obtain ⟨p', hrel, h3, h4, h5, h6⟩ := h2.needsOutput e
    exact ⟨p', hrel, Nat.le_trans hle h3, h4, fun F => by rw [h]; exact h5 F, h6⟩
  done e := by
    obtain ⟨s, hrel, h3, h4, h5, h6⟩ := h2.done e
    exact ⟨s, hrel, Nat.le_trans hle h3, h4, fun F => by rw [h]; exact h5 F, h6⟩
  bad e := fun F => by rw [h]; exact h2.bad e F

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

/-! ### A backward copy -/

/-- Copies as much as the window has room for. -/
def stepCopy (w k : Nat) (st : Cmd) (pos : USize) : Stepped :=
  if st.left.toNat = 0 then ⟨{ st with tag := .command }, pos, .next⟩
  else if 2 ^ k - st.pend.toNat = 0 then ⟨st, pos, .needsOutput⟩
  else
    let run := min st.left.toNat (2 ^ k - st.pend.toNat)
    if h : k ≤ 24 ∧ (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧ (USize.ofNat (2 ^ k)).toNat = 2 ^ k ∧
        1 ≤ (USize.ofNat st.dist.toNat).toNat ∧ (USize.ofNat st.dist.toNat).toNat ≤ 2 ^ k ∧ st.ring.size = 2 ^ k ∧
        st.wpos.toNat < 2 ^ k then
      let ring := st.ring
      let st0 := clearRing st
      let r := copyRun (USize.ofNat st0.dist.toNat) (USize.ofNat (2 ^ k - 1)) (USize.ofNat (2 ^ k)) k h.1 h.2.1 h.2.2.1
        h.2.2.2.1 h.2.2.2.2.1 run ring st0.wpos st0.p1 st0.p2 h.2.2.2.2.2.1 h.2.2.2.2.2.2
      ⟨{ st0 with
          ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
          left := st0.left - UInt64.ofNat run
          pend := USize.ofNat (st0.pend.toNat + run)
          written := USize.ofNat (min w (st0.written.toNat + run)) }, pos, .next⟩
    else ⟨st, pos, .bad⟩

/-- The copy step does its job. -/
theorem stepCopy_ok {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray}
    {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd}
    {pos : USize} (hrel : Rel w k m st (.copy s d n)) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k m K a stop (.copy s d n) st pos (stepCopy w k st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hdist, hleft, hd1, hdw, hdo⟩ := hrel
  have hk := hC.k24
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k := Nat.two_pow_pos _
  have hwin := hC.win
  have hdLt32 : st.dist.toNat < 2 ^ 32 := by omega
  have hdU : (USize.ofNat st.dist.toNat).toNat = st.dist.toNat := usize_ofNat' hdLt32
  unfold stepCopy
  split
  · rename_i hz
    have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨fun _ => ⟨.command s, ⟨?_, rfl, ?_⟩, Nat.le_refl _, hp, fun F => rfl⟩, fun h => StepStatus.noConfusion h,
      fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
    · exact { hC with }
    · omega
  · rename_i hnz
    split
    · rename_i hfull
      have hle := hC.pendLe
      exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h,
        fun _ => ⟨_, hrel0, Nat.le_refl _, hp, fun _ => rfl, by show st.pend.toNat = _; omega⟩,
        fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
    · rename_i hroom
      have hguard : k ≤ 24 ∧ (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧ (USize.ofNat (2 ^ k)).toNat = 2 ^ k ∧
          1 ≤ (USize.ofNat st.dist.toNat).toNat ∧ (USize.ofNat st.dist.toNat).toNat ≤ 2 ^ k ∧ st.ring.size = 2 ^ k ∧
          st.wpos.toNat < 2 ^ k :=
        ⟨hk, usize_ofNat' (by omega), usize_ofNat' (by omega), by omega, by omega, hC.ring.size, hC.ring.pos_lt⟩
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hspec := copyRun_spec (d := USize.ofNat st.dist.toNat) (mask := USize.ofNat (2 ^ k - 1))
        (size := USize.ofNat (2 ^ k)) hguard.1 hguard.2.1 hguard.2.2.1 hguard.2.2.2.1 hguard.2.2.2.2.1
        (min st.left.toNat (2 ^ k - st.pend.toNat)) st.ring st.wpos st.p1 st.p2 hguard.2.2.2.2.2.1 hguard.2.2.2.2.2.2
        s.output (by omega) hC.ring hC.ctx hC.bytes
      dsimp only at hspec
      generalize copyRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hspec ⊢
      rw [hdU] at hspec
      obtain ⟨h1, h2, h3, h4⟩ := hspec
      generalize hrunD : min st.left.toNat (2 ^ k - st.pend.toNat) = run at h1 h2 h3 h4 ⊢
      have hrunL : run ≤ n := by omega
      have hrunR : run + st.pend.toNat ≤ 2 ^ k := by omega
      have hdn : st.dist.toNat = d := hdist
      rw [hdn] at h1 h2 h3 h4
      refine ⟨fun _ => ⟨.copy { s with output := copyBytes d run s.output } d (n - run), ⟨?_, htag, ?_, hdn, ?_, hd1, hdw, ?_⟩,
        Nat.le_refl _, hp, fun F => ?_⟩, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h,
        fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
      · have hwri := hC.written
        have hpO := hC.pendOut
        refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
        · show (USize.ofNat (st.pend.toNat + run)).toNat ≤ _
          rw [usize_ofNat' (by omega)]
          omega
        · show (USize.ofNat (st.pend.toNat + run)).toNat ≤ _
          rw [usize_ofNat' (by omega), h4]
          omega
        · show (USize.ofNat (min w (st.written.toNat + run))).toNat = _
          rw [usize_ofNat' (by omega), h4, hwri]
          omega
      · show s.produced = (copyBytes d run s.output).length + (n - run)
        rw [h4]
        omega
      · show (st.left - UInt64.ofNat run).toNat = n - run
        have hrunU : (UInt64.ofNat run).toNat = run := u64_ofNat (by omega)
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hrunU]; omega)), hrunU, hleft]
      · show d ≤ (copyBytes d run s.output).length
        rw [h4]
        omega
      · show K { s with output := copyBytes d n s.output } _ =
          K { s with output := copyBytes d (n - run) (copyBytes d run s.output) } _
        have hsplit : copyBytes d n s.output = copyBytes d (n - run) (copyBytes d run s.output) := by
          rw [← copyBytes_add]
          congr 1
          omega
        rw [hsplit]
        rfl

/-! ### A dictionary word -/

/-- Writes as much of the word as the window has room for. -/
def stepWord (w k : Nat) (st : Cmd) (pos : USize) : Stepped :=
  let n := st.wordBuf.size - st.wordPos.toNat
  if n = 0 then ⟨{ st with tag := .command }, pos, .next⟩
  else if 2 ^ k - st.pend.toNat = 0 then ⟨st, pos, .needsOutput⟩
  else
    let run := min n (2 ^ k - st.pend.toNat)
    if h : k ≤ 24 ∧ (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧ st.wordPos.toNat + run ≤ st.wordBuf.size ∧
        st.wordPos.toNat + run ≤ 2 ^ 32 - 1 ∧ st.ring.size = 2 ^ k ∧ st.wpos.toNat < 2 ^ k then
      let ring := st.ring
      let st0 := clearRing st
      let r := wordRun st0.wordBuf (USize.ofNat (2 ^ k - 1)) k h.1 h.2.1 run st0.wordPos ring st0.wpos st0.p1 st0.p2
        h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
      ⟨{ st0 with
          ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
          wordPos := st0.wordPos + USize.ofNat run
          pend := USize.ofNat (st0.pend.toNat + run)
          written := USize.ofNat (min w (st0.written.toNat + run)) }, pos, .next⟩
    else ⟨st, pos, .bad⟩

/-- The word step does its job. -/
theorem stepWord_ok {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray}
    {stop : USize} {s : CommandState} {pending : List Nat} {st : Cmd} {pos : USize} (hrel : Rel w k m st (.word s pending))
    (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k m K a stop (.word s pending) st pos (stepWord w k st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hpend, hsmall, hwp⟩ := hrel
  have hk := hC.k24
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k := Nat.two_pow_pos _
  have hwin := hC.win
  have hbs : st.wordBuf.data.toList.length = st.wordBuf.size := by
    show st.wordBuf.data.toList.length = st.wordBuf.data.size
    simp
  have hplen : pending.length = st.wordBuf.size - st.wordPos.toNat := by
    rw [← hpend]
    simp [hbs]
  unfold stepWord
  dsimp only
  split
  · rename_i hz
    have hnil : pending = [] := by
      apply List.eq_nil_of_length_eq_zero
      omega
    subst hnil
    refine ⟨fun _ => ⟨.command s, ⟨{ hC with }, rfl, by simpa using hprod⟩, Nat.le_refl _, hp, fun F => ?_⟩,
      fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
    show rest w m K (.word s []) _ = rest w m K (.command s) _
    rw [rest_word_end]
    rfl
  · rename_i hnz
    split
    · rename_i hfull
      have hle := hC.pendLe
      exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h,
        fun _ => ⟨_, hrel0, Nat.le_refl _, hp, fun _ => rfl, by show st.pend.toNat = _; omega⟩,
        fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
    · rename_i hroom
      have hguard : k ≤ 24 ∧ (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧
          st.wordPos.toNat + min (st.wordBuf.size - st.wordPos.toNat) (2 ^ k - st.pend.toNat) ≤ st.wordBuf.size ∧
          st.wordPos.toNat + min (st.wordBuf.size - st.wordPos.toNat) (2 ^ k - st.pend.toNat) ≤ 2 ^ 32 - 1 ∧
          st.ring.size = 2 ^ k ∧ st.wpos.toNat < 2 ^ k :=
        ⟨hk, usize_ofNat' (by omega), by omega, by omega, hC.ring.size, hC.ring.pos_lt⟩
      rw [dite_eq_left hguard]
      dsimp only [clearRing]
      have hspec := wordRun_spec (buf := st.wordBuf) (mask := USize.ofNat (2 ^ k - 1)) hguard.1 hguard.2.1
        (min (st.wordBuf.size - st.wordPos.toNat) (2 ^ k - st.pend.toNat)) st.wordPos
        st.ring st.wpos st.p1 st.p2 hguard.2.2.1 hguard.2.2.2.1 hguard.2.2.2.2.1 hguard.2.2.2.2.2 s.output
        hC.ring hC.ctx hC.bytes
      dsimp only at hspec
      generalize wordRun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = r at hspec ⊢
      obtain ⟨h1, h2, h3⟩ := hspec
      generalize hrunD : min (st.wordBuf.size - st.wordPos.toNat) (2 ^ k - st.pend.toNat) = run at h1 h2 h3 ⊢
      have hmoved : ((st.wordBuf.data.toList.drop st.wordPos.toNat).take run).map UInt8.toNat = pending.take run := by
        rw [← hpend, List.map_take]
      rw [hmoved] at h1 h2 h3
      have hnewPos : (st.wordPos + USize.ofNat run).toNat = st.wordPos.toNat + run := by
        have hrunU : (USize.ofNat run).toNat = run := usize_ofNat' (by omega)
        rw [USize.toNat_add, hrunU, ← USize.size_eq_two_pow]
        have := USize.le_size
        exact Nat.mod_eq_of_lt (by omega)
      have hlen : ((pending.take run).reverse ++ s.output).length = s.output.length + run := by
        simp only [List.length_append, List.length_reverse, List.length_take]
        omega
      refine ⟨fun _ => ⟨.word { s with output := (pending.take run).reverse ++ s.output } (pending.drop run),
        ⟨?_, htag, ?_, ?_, hsmall, ?_⟩, Nat.le_refl _, hp, fun F => ?_⟩, fun h => StepStatus.noConfusion h,
        fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
      · have hwri := hC.written
        have hpO := hC.pendOut
        have hle := hC.pendLe
        refine { hC with ring := h1, bytes := h3, ctx := h2, pendLe := ?_, pendOut := ?_, written := ?_ }
        · show (USize.ofNat (st.pend.toNat + run)).toNat ≤ _
          rw [usize_ofNat' (by omega)]
          omega
        · show (USize.ofNat (st.pend.toNat + run)).toNat ≤ _
          rw [usize_ofNat' (by omega)]
          show _ ≤ ((pending.take run).reverse ++ s.output).length
          rw [hlen]
          omega
        · show (USize.ofNat (min w (st.written.toNat + run))).toNat = _
          rw [usize_ofNat' (by omega)]
          show _ = min w ((pending.take run).reverse ++ s.output).length
          rw [hlen, hwri]
          omega
      · show s.produced = ((pending.take run).reverse ++ s.output).length + (pending.drop run).length
        rw [hlen, List.length_drop]
        omega
      · show ((st.wordBuf.data.toList.drop (st.wordPos + USize.ofNat run).toNat)).map UInt8.toNat = _
        rw [hnewPos, ← hpend, ← List.drop_drop, List.map_drop]
      · show (st.wordPos + USize.ofNat run).toNat ≤ st.wordBuf.size
        rw [hnewPos]
        omega
      · show K { s with output := pending.reverse ++ s.output } _ =
          K { s with output := (pending.drop run).reverse ++ ((pending.take run).reverse ++ s.output) } _
        have hsplit : pending.reverse ++ s.output = (pending.drop run).reverse ++ ((pending.take run).reverse ++ s.output) := by
          rw [← List.append_assoc, ← List.reverse_append, List.take_append_drop]
        rw [hsplit]
        rfl

end Brotli.Decoder
