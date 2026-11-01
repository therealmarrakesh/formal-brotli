import Brotli.Decoder.Interface

/-!
# Checks on the goals

Decoders the goals must rule out, each failing the goal aimed at it, and one decoder that meets goals 1, 2 and 4,
which shows they don't contradict each other.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Rejects everything. -/
def rejectAll : Machine Unit where
  start _ := ((), .needsInput)
  step _ _ _ _ out _ _ := { state := (), used := 0, output := out, status := .rejected }

/-- Goal 1 rules out rejecting everything: the stream `[6]` is valid. -/
theorem rejectAll_not_correct : ¬ Correct rejectAll := by
  intro h
  let c : Call := ⟨[], [], [], 0, 0, false⟩
  have ha : (Run.initial rejectAll 0).Allowed [6] c :=
    ⟨rfl, by simp [Run.initial, c], by simp [c], by simp [Run.initial], by simpa [c] using USize.size_pos⟩
  have hd := h.rejected (Reaches.call .start ha) rfl
  have hv : decode [6] = some [] := by decide +kernel
  simp [hv] at hd

/-- Never stops asking for input. -/
def alwaysAsks : Machine Unit where
  start _ := ((), .needsInput)
  step _ _ start stop out _ _ := { state := (), used := stop - start, output := out, status := .needsInput }

/-- Goal 4 rules out asking for input after the end was signalled. -/
theorem alwaysAsks_not_truthful : ¬ Truthful alwaysAsks := by
  intro h
  let c : Call := ⟨[], [], [], 0, 0, true⟩
  have ha : (Run.initial alwaysAsks 0).Allowed [] c :=
    ⟨rfl, by simp [Run.initial, c], by simp [Run.initial, c], by simp [c], by simpa [c] using USize.size_pos⟩
  have hd := h.needsInput .start ha rfl
  simp [c] at hd

/-- Keeps everything and hands nothing out, its state counting the bytes it holds. -/
def holdAll : Machine Nat where
  start _ := (0, .needsInput)
  step n _ start stop out _ _ := { state := n + (stop - start), used := stop - start, output := out, status := .needsInput }

/-- A byte at a time, `holdAll` holds as many bytes as it has been given. -/
private theorem holdAll_runs (L : Nat) : ∀ n, n ≤ L → ∃ R, Reaches holdAll 0 (List.replicate L 0) R ∧ R.state = n ∧ R.read = n ∧ R.status = .needsInput ∧ R.ended = false := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨_, .start, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    intro hn
    obtain ⟨R, h1, h2, h3, h4, h5⟩ := ih (by omega)
    let c : Call := ⟨[], [], [], 1, 0, false⟩
    have ha : R.Allowed (List.replicate L 0) c := by
      refine ⟨by rw [h4]; rfl, by simp [c, h3]; omega, by simp [c], by simp [h5], ?_⟩
      have := USize.le_size
      simp only [c, List.length_nil]
      omega
    refine ⟨_, .call h1 ha, ?_, ?_, rfl, ?_⟩
    · simp [Run.after, Run.reply, holdAll, c, h2]
    · simp [Run.after, Run.reply, holdAll, c, h3]
    · simp [Run.after, c, h5]

/-- Goal 3 rules out holding everything back, for every fixed demand. -/
theorem holdAll_not_streams (K : Nat) : ¬ Streams holdAll id (fun _ => K) := by
  intro h
  obtain ⟨R, h1, h2, _⟩ := holdAll_runs (K + 1) (K + 1) (Nat.le_refl _)
  have hd := h.within_demand h1
  simp only [id, h2] at hd
  omega

/-- Reports the memory limit at once. -/
def alwaysLimit : Machine Unit where
  start _ := ((), .memoryLimit)
  step _ _ _ _ out _ _ := { state := (), used := 0, output := out, status := .memoryLimit }

/-- Goal 3 rules out reporting the memory limit when the limit covers the demand. -/
theorem alwaysLimit_not_streams (size : Unit → Nat) (demand : List UInt8 → Nat) :
    ¬ Streams alwaysLimit size demand := by
  intro h
  have hd := h.honest_limit (limit := demand []) (x := []) .start rfl
  simp [Run.initial] at hd

/-! ### Goals 1, 2 and 4 can be met together -/

/-- What `bufferAll` keeps: the input so far, the output not yet handed out, and whether the end was signalled. -/
structure Buffer where
  got : List UInt8
  out : List UInt8
  ended : Bool

/-- The chunk of an input array. -/
def Buffer.chunk (c : ByteArray) (start stop : Nat) : List UInt8 :=
  (c.data.toList.drop start).take (stop - start)

/-- Hands out what fits, keeping the rest. -/
def Buffer.emit (got out : List UInt8) (buf : ByteArray) (space used : Nat) : Reply Buffer :=
  { state := ⟨got, out.drop space, true⟩
    used := used
    output := (buf.data.toList ++ out.take space).toByteArray
    status := if out.length ≤ space then .done else .needsOutput }

/-- Keeps all its input and calls `decode` at the end. It meets goals 1, 2 and 4. -/
def bufferAll : Machine Buffer where
  start _ := (⟨[], [], false⟩, .needsInput)
  step s c start stop buf space final :=
    if s.ended then Buffer.emit (s.got ++ Buffer.chunk c start stop) s.out buf space (stop - start)
    else if final then
      match decode (s.got ++ Buffer.chunk c start stop) with
      | none => { state := ⟨s.got ++ Buffer.chunk c start stop, [], true⟩, used := stop - start, output := buf,
                  status := .rejected }
      | some out => Buffer.emit (s.got ++ Buffer.chunk c start stop) out buf space (stop - start)
    else { state := ⟨s.got ++ Buffer.chunk c start stop, [], false⟩, used := stop - start, output := buf,
           status := .needsInput }

/-- What a run of `bufferAll` holds. -/
structure BufferInv (x : List UInt8) (R : Run Buffer) : Prop where
  got : R.state.got = x.take R.read
  ended : R.state.ended = R.ended
  before : R.ended = false → R.status = .needsInput ∧ R.emitted = [] ∧ R.state.out = []
  rejected : R.status = .rejected → R.ended = true ∧ decode x = none ∧ R.state.out = []
  after : R.ended = true → R.status ≠ .rejected → decode x = some (R.emitted ++ R.state.out) ∧
    (R.status = .done ∧ R.state.out = [] ∨ R.status = .needsOutput ∧ R.state.out ≠ [])
  whole : R.ended = true → R.read = x.length

/-- The chunk a call sees is the next bytes of the stream. -/
private theorem chunk_input {x : List UInt8} {R : Run Buffer} {c : Call} (h : R.read + c.size ≤ x.length) :
    Buffer.chunk (R.input x c) c.pre.length (c.pre.length + c.size) = (x.drop R.read).take c.size := by
  have hl : ((x.drop R.read).take c.size).length = c.size := by
    simp only [List.length_take, List.length_drop]
    omega
  simp only [Buffer.chunk, Run.input, List.data_toByteArray, List.toList_toArray, Nat.add_sub_cancel_left,
    List.append_assoc, List.drop_left']
  simp [hl]

private theorem used_call (c : Call) : c.pre.length + c.size - c.pre.length = c.size := by
  omega

/-- The three kinds of reply: handing out, rejecting and asking for input. -/
private theorem bufferAll_step (s : Buffer) (c : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat)
    (final : Bool) :
    (s.ended = true ∧ bufferAll.step s c start stop buf space final =
      Buffer.emit (s.got ++ Buffer.chunk c start stop) s.out buf space (stop - start)) ∨
    (s.ended = false ∧ final = true ∧ decode (s.got ++ Buffer.chunk c start stop) = none ∧
      bufferAll.step s c start stop buf space final =
        { state := ⟨s.got ++ Buffer.chunk c start stop, [], true⟩, used := stop - start, output := buf,
          status := .rejected }) ∨
    (s.ended = false ∧ final = true ∧ ∃ out, decode (s.got ++ Buffer.chunk c start stop) = some out ∧
      bufferAll.step s c start stop buf space final =
        Buffer.emit (s.got ++ Buffer.chunk c start stop) out buf space (stop - start)) ∨
    (s.ended = false ∧ final = false ∧ bufferAll.step s c start stop buf space final =
      { state := ⟨s.got ++ Buffer.chunk c start stop, [], false⟩, used := stop - start, output := buf,
        status := .needsInput }) := by
  cases he : s.ended with
  | true => exact Or.inl ⟨rfl, by simp [bufferAll, he]⟩
  | false =>
    cases final with
    | false => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by simp [bufferAll, he]⟩))
    | true =>
      cases hd : decode (s.got ++ Buffer.chunk c start stop) with
      | none => exact Or.inr (Or.inl ⟨rfl, rfl, rfl, by simp [bufferAll, he, hd]⟩)
      | some out => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, out, rfl, by simp [bufferAll, he, hd]⟩))

/-- The bytes a hand-out adds to a call's buffer. -/
private theorem emit_fresh (buf out : List UInt8) (space : Nat) :
    (buf.toByteArray.data.toList ++ out.take space).toByteArray.data.toList.drop buf.length = out.take space := by
  simp [List.data_toByteArray]

private theorem emit_inv {x e out : List UInt8} {space n o : Nat} (hd : decode x = some (e ++ out))
    (hn : n = x.length) :
    BufferInv x
      { state := ⟨x, out.drop space, true⟩
        status := if out.length ≤ space then .done else .needsOutput
        read := n
        offered := o
        emitted := e ++ out.take space
        ended := true } := by
  refine ⟨by simp [hn], rfl, by simp, ?_, ?_, fun _ => hn⟩
  · intro hs
    split at hs <;> simp at hs
  · intro _ _
    refine ⟨by simp only [List.append_assoc, List.take_append_drop, hd], ?_⟩
    by_cases h : out.length ≤ space
    · exact Or.inl ⟨by simp [h], by simp [h]⟩
    · exact Or.inr ⟨by simp [h], by simp only [ne_eq, List.drop_eq_nil_iff]; exact h⟩

private theorem bufferAll_inv {limit : Nat} {x : List UInt8} {R : Run Buffer}
    (h : Reaches bufferAll limit x R) : BufferInv x R := by
  induction h with
  | start => exact ⟨by simp [Run.initial, bufferAll], by simp [Run.initial, bufferAll],
      by simp [Run.initial, bufferAll], by simp [Run.initial, bufferAll], by simp [Run.initial],
      by simp [Run.initial]⟩
  | @call R c _ ha ih =>
    have hC := chunk_input ha.inside
    have hG : R.state.got ++ (x.drop R.read).take c.size = x.take (R.read + c.size) := by
      rw [ih.got]
      exact (List.take_add).symm
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨he, hs⟩ | ⟨he, hf, hd, hs⟩ | ⟨he, hf, out, hd, hs⟩ | ⟨he, hf, hs⟩
    · -- the end was signalled earlier
      have hR : R.ended = true := by rw [← ih.ended, he]
      have hn := ih.whole hR
      have hk : c.size = 0 := by have := ha.inside; omega
      have hne : R.status ≠ .rejected := by
        intro hr
        have := ha.running
        simp [hr, Status.stopped] at this
      have hdec := (ih.after hR hne).1
      have hx : x.take (R.read + c.size) = x := by rw [hn, hk, Nat.add_zero, List.take_length]
      rw [hC, hG, hx, used_call] at hs
      have hrp : R.reply bufferAll x c = Buffer.emit x R.state.out c.buf.toByteArray c.space c.size := hs
      have hr : R.after bufferAll x c =
          { state := ⟨x, R.state.out.drop c.space, true⟩
            status := if R.state.out.length ≤ c.space then .done else .needsOutput
            read := x.length
            offered := max R.offered (R.read + c.size)
            emitted := R.emitted ++ R.state.out.take c.space
            ended := true } := by
        unfold Run.after
        rw [hrp]
        simp only [Buffer.emit, emit_fresh, hR, Bool.true_or, hn, hk, Nat.add_zero]
      rw [hr]
      exact emit_inv hdec rfl
    · -- the end is signalled now, on an invalid stream
      have hwhole := ha.whole hf
      have hx : x.take (R.read + c.size) = x := by rw [hwhole, List.take_length]
      rw [hC, hG, hx] at hd hs
      rw [used_call] at hs
      have hR : R.ended = false := by rw [← ih.ended, he]
      have hrp : R.reply bufferAll x c =
          { state := ⟨x, [], true⟩, used := c.size, output := c.buf.toByteArray, status := .rejected } := hs
      have hr : R.after bufferAll x c =
          { state := ⟨x, [], true⟩
            status := .rejected
            read := x.length
            offered := max R.offered (R.read + c.size)
            emitted := R.emitted
            ended := true } := by
        unfold Run.after
        rw [hrp]
        simp [hR, hf, hwhole, List.data_toByteArray]
      rw [hr]
      exact ⟨by simp, rfl, by simp, fun _ => ⟨rfl, hd, rfl⟩, by simp, fun _ => rfl⟩
    · -- the end is signalled now, on a valid stream
      have hwhole := ha.whole hf
      have hx : x.take (R.read + c.size) = x := by rw [hwhole, List.take_length]
      rw [hC, hG, hx] at hd hs
      rw [used_call] at hs
      have hR : R.ended = false := by rw [← ih.ended, he]
      have hem := (ih.before hR).2.1
      have hrp : R.reply bufferAll x c = Buffer.emit x out c.buf.toByteArray c.space c.size := hs
      have hr : R.after bufferAll x c =
          { state := ⟨x, out.drop c.space, true⟩
            status := if out.length ≤ c.space then .done else .needsOutput
            read := x.length
            offered := max R.offered (R.read + c.size)
            emitted := [] ++ out.take c.space
            ended := true } := by
        unfold Run.after
        rw [hrp]
        simp only [Buffer.emit, emit_fresh, hR, hf, Bool.false_or, hwhole, hem]
      rw [hr]
      exact emit_inv (e := []) (by simpa using hd) rfl
    · -- more input
      rw [hC, hG, used_call] at hs
      have hR : R.ended = false := by rw [← ih.ended, he]
      have hem := (ih.before hR).2.1
      have hrp : R.reply bufferAll x c =
          { state := ⟨x.take (R.read + c.size), [], false⟩, used := c.size, output := c.buf.toByteArray,
            status := .needsInput } := hs
      have hr : R.after bufferAll x c =
          { state := ⟨x.take (R.read + c.size), [], false⟩
            status := .needsInput
            read := R.read + c.size
            offered := max R.offered (R.read + c.size)
            emitted := []
            ended := false } := by
        unfold Run.after
        rw [hrp]
        simp [hR, hf, hem, List.data_toByteArray]
      rw [hr]
      exact ⟨rfl, rfl, by simp, by simp, by simp, by simp⟩

/-- `bufferAll` meets goal 1. -/
theorem bufferAll_correct : Correct bufferAll where
  done {_ x R} h hs := by
    have hi := bufferAll_inv h
    cases he : R.ended with
    | false =>
      have := (hi.before he).1
      simp [hs] at this
    | true =>
      obtain ⟨hd, hst⟩ := hi.after he (by simp [hs])
      rcases hst with h' | h'
      · exact ⟨rfl, hi.whole he, by simpa [h'.2] using hd⟩
      · simp [hs] at h'
  rejected {_ x R} h hs := ((bufferAll_inv h).rejected hs).2.1

/-- `bufferAll` meets goal 2. -/
theorem bufferAll_noWrongBytes : NoWrongBytes bufferAll := by
  intro _ x R y h hd
  have hi := bufferAll_inv h
  cases he : R.ended with
  | false => simp [(hi.before he).2.1]
  | true =>
    by_cases hr : R.status = .rejected
    · have := (hi.rejected hr).2.1
      simp [hd] at this
    · have := (hi.after he hr).1
      rw [hd] at this
      simp only [Option.some.injEq] at this
      exact ⟨_, this.symm⟩

/-- `bufferAll` meets the truthful part of goal 4. -/
theorem bufferAll_truthful : Truthful bufferAll where
  used_le {_ x R c} _ _ := by
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨_, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩ <;>
      simp [Run.reply, hs, Buffer.emit]
  keeps {_ x R c} _ _ := by
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨_, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩ <;>
      simp [Run.reply, hs, Buffer.emit, List.data_toByteArray]
  output_le {_ x R c} _ _ := by
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨_, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩ <;>
      simp [Run.reply, hs, Buffer.emit, List.size_toByteArray, List.data_toByteArray] <;> omega
  needsInput {_ x R c} _ _ hst := by
    simp only [Run.reply] at hst ⊢
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨_, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, hf, hs⟩
    · rw [hs] at hst
      simp only [Buffer.emit] at hst
      split at hst <;> simp at hst
    · rw [hs] at hst
      simp at hst
    · rw [hs] at hst
      simp only [Buffer.emit] at hst
      split at hst <;> simp at hst
    · rw [hs]
      exact ⟨used_call c, hf⟩
  needsOutput {_ x R c} _ _ hst := by
    simp only [Run.reply] at hst ⊢
    rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      with ⟨_, hs⟩ | ⟨_, _, _, hs⟩ | ⟨_, _, _, _, hs⟩ | ⟨_, _, hs⟩
    · rw [hs] at hst ⊢
      simp only [Buffer.emit] at hst ⊢
      split at hst
      · simp at hst
      · simp only [List.size_toByteArray, List.length_append, List.length_take, List.data_toByteArray,
          List.toList_toArray]
        omega
    · rw [hs] at hst
      simp at hst
    · rw [hs] at hst ⊢
      simp only [Buffer.emit] at hst ⊢
      split at hst
      · simp at hst
      · simp only [List.size_toByteArray, List.length_append, List.length_take, List.data_toByteArray,
          List.toList_toArray]
        omega
    · rw [hs] at hst
      simp at hst

/-- What's left of a run of `bufferAll`, which each answering call lowers. -/
private def bufferMeasure (x : List UInt8) (R : Run Buffer) : Nat :=
  (x.length - R.read) + (if R.ended then 0 else 1 + ((decode x).getD []).length) + R.state.out.length

private theorem bufferMeasure_lt {limit : Nat} {x : List UInt8} {R : Run Buffer} {c : Call}
    (h : Reaches bufferAll limit x R) (ha : R.Allowed x c) (hans : R.Answers c) :
    bufferMeasure x (R.after bufferAll x c) < bufferMeasure x R := by
  have hi := bufferAll_inv h
  have hC := chunk_input ha.inside
  have hG : R.state.got ++ (x.drop R.read).take c.size = x.take (R.read + c.size) := by
    rw [hi.got]
    exact (List.take_add).symm
  have hin := ha.inside
  rcases bufferAll_step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
    with ⟨he, hs⟩ | ⟨he, hf, hd, hs⟩ | ⟨he, hf, out, hd, hs⟩ | ⟨he, hf, hs⟩
  · have hR : R.ended = true := by rw [← hi.ended, he]
    have hn := hi.whole hR
    have hne : R.status ≠ .rejected := by
      intro hr
      have := ha.running
      simp [hr, Status.stopped] at this
    rcases (hi.after hR hne).2 with ⟨hst, _⟩ | ⟨hst, hout⟩
    · have := ha.running
      simp [hst, Status.stopped] at this
    · have hsp := hans.2 hst
      have hlen : 0 < R.state.out.length := List.length_pos_iff.mpr hout
      have hk : c.size = 0 := by omega
      rw [hC, hG, used_call] at hs
      have hrp : R.reply bufferAll x c =
          Buffer.emit (x.take (R.read + c.size)) R.state.out c.buf.toByteArray c.space c.size := hs
      unfold bufferMeasure Run.after
      rw [hrp]
      simp [Buffer.emit, hR, hn, hk]
      omega
  · have hwhole := ha.whole hf
    have hR : R.ended = false := by rw [← hi.ended, he]
    have hO := (hi.before hR).2.2
    rw [hC, hG, used_call] at hs
    have hrp : R.reply bufferAll x c =
        { state := ⟨x.take (R.read + c.size), [], true⟩, used := c.size, output := c.buf.toByteArray,
          status := .rejected } := hs
    unfold bufferMeasure Run.after
    rw [hrp]
    simp [hR, hf, hO, hwhole]
    omega
  · have hwhole := ha.whole hf
    have hR : R.ended = false := by rw [← hi.ended, he]
    have hO := (hi.before hR).2.2
    have hx : x.take (R.read + c.size) = x := by rw [hwhole, List.take_length]
    rw [hC, hG, hx] at hd hs
    rw [used_call] at hs
    have hrp : R.reply bufferAll x c = Buffer.emit x out c.buf.toByteArray c.space c.size := hs
    unfold bufferMeasure Run.after
    rw [hrp]
    simp [Buffer.emit, hR, hf, hO, hwhole, hd]
    omega
  · have hR : R.ended = false := by rw [← hi.ended, he]
    have hO := (hi.before hR).2.2
    have hst := (hi.before hR).1
    have hk : 0 < c.size := by
      rcases hans.1 hst with h' | h'
      · exact h'
      · simp [hf] at h'
    rw [hC, hG, used_call] at hs
    have hrp : R.reply bufferAll x c =
        { state := ⟨x.take (R.read + c.size), [], false⟩, used := c.size, output := c.buf.toByteArray,
          status := .needsInput } := hs
    unfold bufferMeasure Run.after
    rw [hrp]
    simp [hR, hf, hO]
    omega

/-- `bufferAll` meets the terminating part of goal 4. -/
theorem bufferAll_terminates : Terminates bufferAll := by
  intro limit x R hR
  have key : ∀ n (R : Run Buffer), Reaches bufferAll limit x R → bufferMeasure x R < n →
      Acc (Follows bufferAll limit x) R := by
    intro n
    induction n with
    | zero => intro _ _ h; omega
    | succ n ih =>
      intro R hR hn
      refine Acc.intro R ?_
      intro R' hf
      obtain ⟨_, c, ha, hans, rfl⟩ := hf
      exact ih _ (.call hR ha) (by have := bufferMeasure_lt hR ha hans; omega)
  exact key _ R hR (Nat.lt_succ_self _)

end Brotli.Decoder
