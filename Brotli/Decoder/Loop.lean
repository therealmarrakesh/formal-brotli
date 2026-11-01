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
  refine (stepAt_ok hK hH (hrel.withBits h1) h3 h5).refilled (fun F => ?_) h2 h3
  show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
    (refill st.word st.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F)
  rw [← List.append_assoc, ← List.append_assoc, h4]

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

/-- Any number of steps together does what one step must. -/
theorem runCmd_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m) :
    ∀ (N : Nat) (n : USize) (p : Phase) (st : Cmd) (pos : USize), n.toNat = N → Rel w k.toNat m st p → pos.toNat ≤ stop.toNat →
      StepOk w k.toNat m K a stop p st pos (runCmd H k a stop hs n st pos) := by
  intro N
  induction N with
  | zero =>
    intro n p st pos hN hrel hp
    rw [runCmd, dite_eq_left (usize_zero hN)]
    exact StepOk.ofNext rfl (hrel.mark _ _) (Nat.le_refl _) hp fun _ => rfl
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
      obtain ⟨p', hR, h1, h2, h3⟩ := hstep.next hst
      exact StepOk.trans h1 h3 (ih _ p' r r.pos (by omega) hR h2)
    | needsInput => exact hstep
    | needsOutput => exact hstep
    | done => exact hstep
    | bad => exact hstep

/-- `stepCmd_ok` for the spec's own commands. -/
theorem stepCmd_commands {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st p)
    (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k.toNat m (commandsFrom w m) a stop p st pos (stepCmd H k a stop hs st pos) :=
  stepCmd_ok (fun _ bs h0 => commandsFrom_step bs h0) hH hrel hp

/-! ### Handing bytes out -/

/-- The bytes a place has produced so far, most recent first. -/
def Phase.out : Phase → List Nat
  | .command s => s.output
  | .insertCopy s _ => s.output
  | .copyLength s .. => s.output
  | .literals _ _ _ _ _ _ _ out => out
  | .literalSymbol _ _ _ _ _ _ _ out => out
  | .distance s .. => s.output
  | .distanceSymbol s .. => s.output
  | .copy s .. => s.output
  | .word s _ => s.output

/-- What flushing returns. -/
structure Flushed where
  st : Cmd
  buf : ByteArray

/-- Adds up to `space` bytes waiting in the window to the caller's buffer, stopping where the ring wraps. -/
def flushCmd (k : Nat) (st : Cmd) (buf : ByteArray) (space : Nat) : Flushed :=
  let u := st.pend.toNat
  if u = 0 ∨ space = 0 then ⟨st, buf⟩
  else
    let start := ringStart (2 ^ k) st.wpos.toNat u
    let len := min (min u space) (2 ^ k - start)
    ⟨{ st with pend := USize.ofNat (u - len) }, emitRun st.ring buf start len⟩

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

/-- Flushing keeps the state's place, adds the next bytes waiting to the buffer, oldest first, and takes them off those
waiting. It adds at least one byte when one is waiting and there is space. -/
theorem flushCmd_spec {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} {buf : ByteArray} {space : Nat}
    (h : Rel w k m st p) :
    let r := flushCmd k st buf space
    ∃ len, len ≤ space ∧ len ≤ st.pend.toNat ∧ (st.pend.toNat ≠ 0 → space ≠ 0 → 1 ≤ len) ∧
      r.st.pend.toNat = st.pend.toNat - len ∧ Rel w k m r.st p ∧
      r.st.word = st.word ∧ r.st.count = st.count ∧
      r.buf.data.toList.map UInt8.toNat =
        buf.data.toList.map UInt8.toNat ++ ((p.out.take st.pend.toNat).reverse).take len := by
  obtain ⟨hring, hle, hout, hk⟩ := h.window
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k := Nat.two_pow_pos _
  dsimp only
  unfold flushCmd
  dsimp only
  split
  · rename_i hz
    refine ⟨0, Nat.zero_le _, Nat.zero_le _, by omega, rfl, h, rfl, rfl, by simp⟩
  · rename_i hz
    have hplt := hring.pos_lt
    have hstart : ringStart (2 ^ k) st.wpos.toNat st.pend.toNat < 2 ^ k := by
      unfold ringStart
      exact ringIdx_lt hplt (by omega)
    generalize hlenD : min (min st.pend.toNat space) (2 ^ k - ringStart (2 ^ k) st.wpos.toNat st.pend.toNat) = len
    have hpn : (USize.ofNat (st.pend.toNat - len)).toNat = st.pend.toNat - len := usize_ofNat' (by omega)
    refine ⟨len, by omega, by omega, by omega, hpn, h.withPend (by rw [hpn]; omega), rfl, rfl, ?_⟩
    show (emitRun st.ring buf _ len).data.toList.map UInt8.toNat = _
    rw [emitRun_data _ _ (by rw [hring.size]; omega), List.map_append,
      hring.emit_bytes (by omega) hle hout (by omega) (by omega)]

end Brotli.Decoder
