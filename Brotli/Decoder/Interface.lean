module

public import Brotli.Spec.Stream
public import Brotli.Decoder.FastEq

@[expose] public section

/-!
# The decoder's interface and goals

What a streaming decoder looks like to its caller, and the correctness goals, stated over any machine with
that interface. There is no decoder here.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- What a call reports. -/
inductive Status where
  | needsInput
  | needsOutput
  | done
  | rejected
  | memoryLimit
  deriving DecidableEq

fast_deceq Status [needsInput, needsOutput, done, rejected, memoryLimit]

/-- A stopped decoder takes no more calls. -/
def Status.stopped : Status → Bool
  | .done | .rejected | .memoryLimit => true
  | .needsInput | .needsOutput => false

/-- What a call returns: the new state, the input bytes it used, the caller's buffer with the output appended, and
a status. The bytes used are the whole chunk when it needs input, the whole stream when it is done, and, when it rejects
or reports the limit, the bytes up to where it decided that: `RejectUsed` and `LimitUsed` say what those bytes alone
settle. -/
structure Reply (σ : Type) where
  state : σ
  used : Nat
  output : ByteArray
  status : Status

/-- A streaming decoder. `start` takes the memory limit. `step` takes the state, an input array with the start and
stop of the chunk inside it, the caller's output buffer, the output space and the end flag, so a caller can resume
a chunk and reuse a buffer without copying either. -/
structure Machine (σ : Type) where
  start : Nat → σ × Status
  step : σ → ByteArray → Nat → Nat → ByteArray → Nat → Bool → Reply σ

/-- A run so far, on a stream the caller delivers: the state, the last status, the bytes used, how far the stream
has been offered, the bytes handed out, and whether the end has been signalled. -/
structure Run (σ : Type) where
  state : σ
  status : Status
  read : Nat
  offered : Nat
  emitted : List UInt8
  ended : Bool

/-- One call: the bytes around the chunk in the input array, what the output buffer already holds, the chunk's
size, the output space and the end flag. -/
structure Call where
  pre : List UInt8
  post : List UInt8
  buf : List UInt8
  size : Nat
  space : Nat
  final : Bool

variable {σ : Type}

/-- The run before any call. -/
def Run.initial (D : Machine σ) (limit : Nat) : Run σ :=
  { state := (D.start limit).1, status := (D.start limit).2, read := 0, offered := 0, emitted := [],
    ended := false }

/-- A call's input array: the next bytes of the stream `x` as the chunk, with other bytes around it. -/
def Run.input (x : List UInt8) (R : Run σ) (c : Call) : ByteArray :=
  (c.pre ++ (x.drop R.read).take c.size ++ c.post).toByteArray

/-- A call's reply. -/
def Run.reply (D : Machine σ) (x : List UInt8) (R : Run σ) (c : Call) : Reply σ :=
  D.step R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final

/-- The run after a call. -/
def Run.after (D : Machine σ) (x : List UInt8) (R : Run σ) (c : Call) : Run σ :=
  { state := (R.reply D x c).state
    status := (R.reply D x c).status
    read := R.read + (R.reply D x c).used
    offered := max R.offered (R.read + c.size)
    emitted := R.emitted ++ (R.reply D x c).output.data.toList.drop c.buf.length
    ended := R.ended || c.final }

/-- A call the caller may make: the decoder hasn't stopped, the chunk is within the stream, and the end flag is
set only with the whole of the rest of the stream, and stays set. The input array fits the machine's addresses, as
every array that exists does. -/
structure Run.Allowed (x : List UInt8) (R : Run σ) (c : Call) : Prop where
  running : R.status.stopped = false
  inside : R.read + c.size ≤ x.length
  whole : c.final = true → R.read + c.size = x.length
  stays : R.ended = true → c.final = true
  fits : c.pre.length + c.size + c.post.length < USize.size

/-- The runs a machine can reach on the stream `x`, under every way of delivering it. -/
inductive Reaches (D : Machine σ) (limit : Nat) (x : List UInt8) : Run σ → Prop
  | start : Reaches D limit x (Run.initial D limit)
  | call {R : Run σ} {c : Call} : Reaches D limit x R → R.Allowed x c → Reaches D limit x (R.after D x c)

/-! ### The goals -/

/-- Soundness and completeness. A success gives exactly what `decode` gives, after the end signal and with the whole stream used,
and a rejection means `decode` rejects. `decode_valid` and `decode_invalid` give the other direction. -/
structure Correct (D : Machine σ) : Prop where
  done : ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .done →
    R.ended = true ∧ R.read = x.length ∧ decode x = some R.emitted
  rejected : ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .rejected → decode x = none

/-- A rejection's bytes used: the whole stream after the end signal, or bytes that no continuation makes valid. -/
def RejectUsed (D : Machine σ) : Prop :=
  ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .rejected →
    (R.ended = true ∧ R.read = x.length) ∨ ∀ t : List UInt8, decode (x.take R.read ++ t) = none

/-- Prefix soundness. What's been handed out is always a prefix of the output of a valid stream. `prefix_of_completion`
and `rejected_final` state it for every continuation of the input so far. -/
def NoWrongBytes (D : Machine σ) : Prop :=
  ∀ {limit x} {R : Run σ} {y}, Reaches D limit x R → decode x = some y → R.emitted <+: y

/-- Memory usage correctness, for a size measure on the state and a demand on the input so far. The size stays within the demand,
and within the limit unless the limit was reported, which happens only when the demand exceeds it. -/
structure Streams (D : Machine σ) (size : σ → Nat) (demand : List UInt8 → Nat) : Prop where
  within_demand : ∀ {limit x} {R : Run σ}, Reaches D limit x R → size R.state ≤ demand (x.take R.offered)
  within_limit : ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status ≠ .memoryLimit → size R.state ≤ limit
  honest_limit : ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .memoryLimit →
    limit < demand (x.take R.offered)
  honest_stream : ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .memoryLimit → limit < demand x

/-- The limit's bytes used: they alone demand more than the limit. -/
def LimitUsed (D : Machine σ) (demand : List UInt8 → Nat) : Prop :=
  ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .memoryLimit → limit < demand (x.take R.read)

/-- The limit, reported in time: nine bytes before the bytes used, the input didn't yet demand more than the limit. -/
def LimitPrompt (D : Machine σ) (demand : List UInt8 → Nat) : Prop :=
  ∀ {limit x} {R : Run σ}, Reaches D limit x R → R.status = .memoryLimit → ∀ n, n + 9 ≤ R.read → demand (x.take n) ≤ limit

/-- The window a stream declares: the window size its WBITS gives, or none before WBITS is read. -/
def declaredWindow (y : List UInt8) : Nat :=
  match readWBITS (bits y) with
  | some p => windowSize p.1
  | none => 0

/-- A demand that never exceeds the declared window by more than the constant `C`, whatever the stream. -/
def DemandCeiling (demand : List UInt8 → Nat) (C : Nat) : Prop := ∀ y, demand y ≤ declaredWindow y + C

/-- Two runs on the same stream, started with two limits, that have had the same calls. -/
inductive Twin (D : Machine σ) (l1 l2 : Nat) (x : List UInt8) : Run σ → Run σ → Prop
  | start : Twin D l1 l2 x (Run.initial D l1) (Run.initial D l2)
  | call {R1 R2 : Run σ} {c : Call} : Twin D l1 l2 x R1 R2 → R1.Allowed x c → R2.Allowed x c →
      Twin D l1 l2 x (R1.after D x c) (R2.after D x c)

/-- The limit changes nothing but whether the decoder stops: two runs with the same calls agree on everything a caller sees
until one of them reports the limit. -/
def LimitBlind (D : Machine σ) : Prop :=
  ∀ {l1 l2 x} {R1 R2 : Run σ}, Twin D l1 l2 x R1 R2 → R1.status ≠ .memoryLimit → R2.status ≠ .memoryLimit →
    R1.status = R2.status ∧ R1.read = R2.read ∧ R1.emitted = R2.emitted

/-- Two runs on the same stream and limit whose calls gave the same chunks, space and end flags, each chunk anywhere in
its array, with any bytes around it, and with any bytes in the output buffer. -/
inductive Relaid (D : Machine σ) (limit : Nat) (x : List UInt8) : Run σ → Run σ → Prop
  | start : Relaid D limit x (Run.initial D limit) (Run.initial D limit)
  | call {R1 R2 : Run σ} {c1 c2 : Call} : Relaid D limit x R1 R2 → R1.Allowed x c1 → R2.Allowed x c2 →
      c1.size = c2.size → c1.space = c2.space → c1.final = c2.final → Relaid D limit x (R1.after D x c1) (R2.after D x c2)

/-- What the caller sees depends only on the bytes and space given: two runs whose calls gave the same chunks, space and
end flags report the same statuses, use the same bytes and hand out the same bytes, wherever each chunk sat in its array,
whatever lay around it, and whatever the output buffer held. -/
def LayoutBlind (D : Machine σ) : Prop :=
  ∀ {limit x} {R1 R2 : Run σ}, Relaid D limit x R1 R2 → R1.status = R2.status ∧ R1.read = R2.read ∧ R1.emitted = R2.emitted

/-- Totality and progress, its truthful part. A call uses at most its chunk, keeps what the buffer held, and fills at most its
space. "Needs input" means the chunk was all used and the end hasn't been signalled, and "needs output" means the
space is full. -/
structure Truthful (D : Machine σ) : Prop where
  used_le : ∀ {limit x} {R : Run σ} {c}, Reaches D limit x R → R.Allowed x c → (R.reply D x c).used ≤ c.size
  keeps : ∀ {limit x} {R : Run σ} {c}, Reaches D limit x R → R.Allowed x c →
    c.buf <+: (R.reply D x c).output.data.toList
  output_le : ∀ {limit x} {R : Run σ} {c}, Reaches D limit x R → R.Allowed x c →
    (R.reply D x c).output.size ≤ c.buf.length + c.space
  needsInput : ∀ {limit x} {R : Run σ} {c}, Reaches D limit x R → R.Allowed x c →
    (R.reply D x c).status = .needsInput → (R.reply D x c).used = c.size ∧ c.final = false
  needsOutput : ∀ {limit x} {R : Run σ} {c}, Reaches D limit x R → R.Allowed x c →
    (R.reply D x c).status = .needsOutput → (R.reply D x c).output.size = c.buf.length + c.space

/-- A call that answers the last status: more input or the end after "needs input", and some space after "needs
output". -/
def Run.Answers (R : Run σ) (c : Call) : Prop :=
  (R.status = .needsInput → 0 < c.size ∨ c.final = true) ∧ (R.status = .needsOutput → 0 < c.space)

/-- `R'` follows `R` by a call that answers `R`'s status. -/
def Follows (D : Machine σ) (limit : Nat) (x : List UInt8) (R' R : Run σ) : Prop :=
  Reaches D limit x R ∧ ∃ c, R.Allowed x c ∧ R.Answers c ∧ R' = R.after D x c

/-- Totality and progress, its terminating part. No caller answering the signals can keep a machine running forever. Every call
returning is the type of `Machine.step`, whose definitions are total. -/
def Terminates (D : Machine σ) : Prop :=
  ∀ {limit x} {R : Run σ}, Reaches D limit x R → Acc (Follows D limit x) R

/-! ### What follows from them -/

/-- With a ceiling on the demand, what a state holds stays within the declared window plus that constant. -/
theorem Streams.within_window {D : Machine σ} {size : σ → Nat} {demand : List UInt8 → Nat} {C : Nat}
    (hs : Streams D size demand) (hc : DemandCeiling demand C) {limit : Nat} {x : List UInt8} {R : Run σ}
    (h : Reaches D limit x R) : size R.state ≤ declaredWindow (x.take R.offered) + C :=
  Nat.le_trans (hs.within_demand h) (hc _)

private theorem chunk_continuation {x t : List UInt8} {o r k : Nat} (h1 : r + k ≤ o) (h2 : r + k ≤ x.length) :
    ((x.take o ++ t).drop r).take k = (x.drop r).take k := by
  have hl : r + k ≤ (x.take o).length := by
    simp only [List.length_take]
    omega
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp only [List.length_drop]; omega),
    List.drop_take, List.take_take]
  congr 1
  omega

/-- A run is offered no more than the stream. -/
theorem Reaches.offered_le {D : Machine σ} {limit : Nat} {x : List UInt8} {R : Run σ} (h : Reaches D limit x R) : R.offered ≤ x.length := by
  induction h with
  | start => exact Nat.zero_le _
  | @call R c hR ha ih =>
    have := ha.inside
    simp only [Run.after]
    omega

/-- After the end signal, a run has been offered the whole stream. -/
theorem Reaches.offered_ended {D : Machine σ} {limit : Nat} {x : List UInt8} {R : Run σ} (h : Reaches D limit x R) : R.ended = true → R.offered = x.length := by
  induction h with
  | start => exact fun e => Bool.noConfusion e
  | @call R c hR ha ih =>
    intro he
    have hin := ha.inside
    have hle := hR.offered_le
    simp only [Run.after] at he ⊢
    by_cases hR2 : R.ended = true
    · have := ih hR2
      omega
    · have hc : c.final = true := by simpa [hR2] using he
      have := ha.whole hc
      omega

/-- A run that hasn't signalled the end is also a run on every stream that continues what it was offered. -/
theorem Reaches.continuation {D : Machine σ} {limit : Nat} {x : List UInt8} {R : Run σ}
    (h : Reaches D limit x R) (he : R.ended = false) {o : Nat} (ho : R.offered ≤ o) (t : List UInt8) :
    Reaches D limit (x.take o ++ t) R := by
  induction h with
  | start => exact .start
  | @call R c hR ha ih =>
    simp only [Run.after, Bool.or_eq_false_iff] at he
    have hk : R.read + c.size ≤ o := Nat.le_trans (Nat.le_max_right _ _) ho
    have heq : R.after D (x.take o ++ t) c = R.after D x c := by
      simp only [Run.after, Run.reply, Run.input, chunk_continuation hk ha.inside]
    rw [← heq]
    refine .call (ih he.1 (Nat.le_trans (Nat.le_max_left _ _) ho)) ⟨ha.running, ?_, ?_, ?_, ha.fits⟩
    · simp only [List.length_append, List.length_take]
      have := ha.inside
      omega
    · simp [he.2]
    · simp [he.1]

/-- Prefix soundness for every valid continuation of the input so far. -/
theorem prefix_of_completion {D : Machine σ} (h : NoWrongBytes D) {limit : Nat} {x : List UInt8} {R : Run σ}
    (hR : Reaches D limit x R) (he : R.ended = false) (t : List UInt8) {y : List UInt8}
    (hd : decode (x.take R.offered ++ t) = some y) : R.emitted <+: y :=
  h (hR.continuation he (Nat.le_refl _) t) hd

/-- An early rejection is final: no continuation of the input so far is valid. It follows from soundness. -/
theorem rejected_final {D : Machine σ} (h : Correct D) {limit : Nat} {x : List UInt8} {R : Run σ}
    (hR : Reaches D limit x R) (he : R.ended = false) (hs : R.status = .rejected) (t : List UInt8) :
    decode (x.take R.offered ++ t) = none :=
  h.rejected (hR.continuation he (Nat.le_refl _) t) hs

/-- The bytes used stay within the stream. -/
theorem Reaches.read_le {D : Machine σ} (ht : Truthful D) {limit : Nat} {x : List UInt8} {R : Run σ}
    (h : Reaches D limit x R) : R.read ≤ x.length := by
  induction h with
  | start => simp [Run.initial]
  | @call R c hR ha _ =>
    have := ht.used_le hR ha
    have := ha.inside
    simp only [Run.after]
    omega

/-- After the end signal, what's left of the stream fits one array. -/
private theorem Reaches.ended_rest {D : Machine σ} {limit : Nat} {x : List UInt8} {R : Run σ}
    (h : Reaches D limit x R) : R.ended = true → x.length - R.read < USize.size := by
  induction h with
  | start => simp [Run.initial]
  | @call R c hR ha ih =>
    intro he
    simp only [Run.after] at he ⊢
    by_cases hR2 : R.ended = true
    · have := ih hR2
      omega
    · have hc : c.final = true := by simpa [hR2] using he
      have h1 := ha.whole hc
      have h2 := ha.fits
      omega

private theorem reaches_stop_of_acc {D : Machine σ} (ht : Truthful D) {limit : Nat} {x : List UInt8}
    {R : Run σ} (hacc : Acc (Follows D limit x) R) :
    Reaches D limit x R → ∃ R', Reaches D limit x R' ∧ R'.status.stopped = true := by
  induction hacc with
  | intro R _ ih =>
    intro hR
    cases hs : R.status.stopped with
    | true => exact ⟨R, hR, hs⟩
    | false =>
      have hle := hR.read_le ht
      have hrest := hR.ended_rest
      have hsize := USize.size_pos
      let n := min (x.length - R.read) (USize.size - 1)
      let c : Call := ⟨[], [], [], n, 1, decide (x.length - R.read < USize.size)⟩
      have ha : R.Allowed x c := by
        refine ⟨hs, by simp only [c, n]; omega, fun hf => ?_, fun he => ?_, by simp only [c, n, List.length_nil]; omega⟩
        · have hf' : x.length - R.read < USize.size := by simpa [c] using hf
          simp only [c, n]
          omega
        · simpa [c] using hrest he
      have hans : R.Answers c := by
        refine ⟨fun _ => ?_, fun _ => by simp only [c]; omega⟩
        by_cases h0 : x.length - R.read = 0
        · exact Or.inr (by simp only [c]; simp only [decide_eq_true_eq]; omega)
        · exact Or.inl (by simp only [c, n]; have := USize.le_size; omega)
      exact ih _ ⟨hR, c, ha, hans, rfl⟩ (.call hR ha)

/-- From anywhere in a run, a caller answering the signals can reach a stopped decoder. -/
theorem reaches_stop {D : Machine σ} (ht : Truthful D) (hd : Terminates D) {limit : Nat} {x : List UInt8}
    {R : Run σ} (hR : Reaches D limit x R) : ∃ R', Reaches D limit x R' ∧ R'.status.stopped = true :=
  reaches_stop_of_acc ht (hd hR) hR

/-- Completeness for a valid stream: from anywhere in a run, the decoder can reach success with
exactly `decode`'s output, or a reported memory limit. -/
theorem decode_valid {D : Machine σ} (hc : Correct D) (ht : Truthful D) (hd : Terminates D) {limit : Nat}
    {x y : List UInt8} (hv : decode x = some y) {R : Run σ} (hR : Reaches D limit x R) :
    ∃ R', Reaches D limit x R' ∧ (R'.status = .memoryLimit ∨ (R'.status = .done ∧ R'.emitted = y)) := by
  obtain ⟨R', hR', hs⟩ := reaches_stop ht hd hR
  refine ⟨R', hR', ?_⟩
  cases hst : R'.status with
  | needsInput => simp [hst, Status.stopped] at hs
  | needsOutput => simp [hst, Status.stopped] at hs
  | memoryLimit => exact Or.inl rfl
  | rejected =>
    have := hc.rejected hR' hst
    simp [hv] at this
  | done =>
    have := (hc.done hR' hst).2.2
    rw [hv] at this
    exact Or.inr ⟨rfl, by simpa using this.symm⟩

/-- Completeness for an invalid stream: from anywhere in a run, the decoder can reach a rejection
or a reported memory limit. -/
theorem decode_invalid {D : Machine σ} (hc : Correct D) (ht : Truthful D) (hd : Terminates D) {limit : Nat}
    {x : List UInt8} (hv : decode x = none) {R : Run σ} (hR : Reaches D limit x R) :
    ∃ R', Reaches D limit x R' ∧ (R'.status = .memoryLimit ∨ R'.status = .rejected) := by
  obtain ⟨R', hR', hs⟩ := reaches_stop ht hd hR
  refine ⟨R', hR', ?_⟩
  cases hst : R'.status with
  | needsInput => simp [hst, Status.stopped] at hs
  | needsOutput => simp [hst, Status.stopped] at hs
  | memoryLimit => exact Or.inl rfl
  | rejected => exact Or.inr rfl
  | done =>
    have := (hc.done hR' hst).2.2
    simp [hv] at this

/-! ### Every caller that answers the signals -/

/-- A caller: from each run, the call it makes next. -/
def Caller (σ : Type) := Run σ → Call

/-- A caller that, until the decoder stops, always makes a call it may make, answering the last status. -/
def Caller.Answering (D : Machine σ) (limit : Nat) (x : List UInt8) (k : Caller σ) : Prop :=
  ∀ R, Reaches D limit x R → R.status.stopped = false → R.Allowed x (k R) ∧ R.Answers (k R)

/-- The run after a caller's next `n` calls, which stops calling once the decoder stops. -/
def Run.follow (D : Machine σ) (x : List UInt8) (k : Caller σ) : Nat → Run σ → Run σ
  | 0, R => R
  | n + 1, R => if R.status.stopped then R else Run.follow D x k n (R.after D x (k R))

/-- A caller that answers the signals keeps the run reachable. -/
theorem Run.follow_reaches {D : Machine σ} {limit : Nat} {x : List UInt8} {k : Caller σ} (hk : k.Answering D limit x) :
    ∀ (n : Nat) {R : Run σ}, Reaches D limit x R → Reaches D limit x (Run.follow D x k n R)
  | 0, _, hR => hR
  | n + 1, R, hR => by
    unfold Run.follow
    split
    · exact hR
    · rename_i hs
      exact Run.follow_reaches hk n (.call hR (hk R hR (by simpa using hs)).1)

/-- Every caller that answers the signals stops the decoder, after finitely many calls. -/
theorem caller_stops {D : Machine σ} (hd : Terminates D) {limit : Nat} {x : List UInt8} {k : Caller σ}
    (hk : k.Answering D limit x) {R : Run σ} (hR : Reaches D limit x R) :
    ∃ n, (Run.follow D x k n R).status.stopped = true := by
  induction hd hR with
  | intro R _ ih =>
    cases hs : R.status.stopped with
    | true => exact ⟨0, hs⟩
    | false =>
      obtain ⟨ha, hans⟩ := hk R hR hs
      obtain ⟨n, hn⟩ := ih _ ⟨hR, k R, ha, hans, rfl⟩ (.call hR ha)
      refine ⟨n + 1, ?_⟩
      unfold Run.follow
      rw [hs]
      exact hn

/-- A stopped run's verdict: on a valid stream, exactly `decode`'s output or a reported memory limit; on an invalid one, a
rejection or a reported memory limit. -/
theorem stopped_verdict {D : Machine σ} (hc : Correct D) {limit : Nat} {x : List UInt8} {R : Run σ}
    (hR : Reaches D limit x R) (hn : R.status.stopped = true) :
    (∀ y, decode x = some y → R.status = .memoryLimit ∨ (R.status = .done ∧ R.emitted = y)) ∧
      (decode x = none → R.status = .memoryLimit ∨ R.status = .rejected) := by
  refine ⟨fun y hy => ?_, fun hy => ?_⟩
  · cases hst : R.status with
    | needsInput => simp [hst, Status.stopped] at hn
    | needsOutput => simp [hst, Status.stopped] at hn
    | memoryLimit => exact Or.inl rfl
    | rejected =>
      have := hc.rejected hR hst
      simp [hy] at this
    | done =>
      have := (hc.done hR hst).2.2
      rw [hy] at this
      exact Or.inr ⟨rfl, by simpa using this.symm⟩
  · cases hst : R.status with
    | needsInput => simp [hst, Status.stopped] at hn
    | needsOutput => simp [hst, Status.stopped] at hn
    | memoryLimit => exact Or.inl rfl
    | rejected => exact Or.inr rfl
    | done =>
      have := (hc.done hR hst).2.2
      simp [hy] at this

/-- Soundness and completeness for every caller that answers the signals: it stops the decoder, and the stopped run's
verdict is `decode`'s. -/
theorem caller_verdict {D : Machine σ} (hc : Correct D) (hd : Terminates D) {limit : Nat} {x : List UInt8} {k : Caller σ}
    (hk : k.Answering D limit x) :
    ∃ n, (Run.follow D x k n (Run.initial D limit)).status.stopped = true ∧
      (∀ y, decode x = some y → (Run.follow D x k n (Run.initial D limit)).status = .memoryLimit ∨
        ((Run.follow D x k n (Run.initial D limit)).status = .done ∧ (Run.follow D x k n (Run.initial D limit)).emitted = y)) ∧
      (decode x = none → (Run.follow D x k n (Run.initial D limit)).status = .memoryLimit ∨
        (Run.follow D x k n (Run.initial D limit)).status = .rejected) := by
  obtain ⟨n, hn⟩ := caller_stops hd hk .start
  exact ⟨n, hn, stopped_verdict hc (Run.follow_reaches hk n .start) hn⟩

/-- With a limit that covers the stream's demand, every caller that answers the signals gets exactly `decode`'s output. -/
theorem caller_succeeds {D : Machine σ} {size : σ → Nat} {demand : List UInt8 → Nat} (hc : Correct D) (hd : Terminates D)
    (hs : Streams D size demand) {limit : Nat} {x y : List UInt8} (hv : decode x = some y) (hl : demand x ≤ limit)
    {k : Caller σ} (hk : k.Answering D limit x) :
    ∃ n, (Run.follow D x k n (Run.initial D limit)).status = .done ∧ (Run.follow D x k n (Run.initial D limit)).emitted = y := by
  obtain ⟨n, _, hval, _⟩ := caller_verdict hc hd hk (limit := limit)
  refine ⟨n, ?_⟩
  rcases hval y hv with h | h
  · have := hs.honest_stream (Run.follow_reaches hk n .start) h
    omega
  · exact h

end Brotli.Decoder
