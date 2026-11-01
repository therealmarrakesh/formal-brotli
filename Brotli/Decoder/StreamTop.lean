import Brotli.Decoder.StreamCall

/-!
# The decoder

The streaming decoder as a `Machine`, and the invariant over every run that ties it to `decode`. Goal 1 and the truthful part
of goal 4 follow from it.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The decoder's state between calls. -/
abbrev DState := { D : Dec // ∃ p, DRel D p }

/-- What the state costs apart from its window and its tables: the buffers a header's reading needs, and the fields. -/
def fixedCost : Nat := 1048576

/-- A state at a stream's start, with what the limit leaves for the window and the tables. -/
def liveD (limit : Nat) : Dec := { deadD with limit := UInt64.ofNat (min (limit - fixedCost) 4294835199) }

theorem liveD_rel (limit : Nat) : DRel (liveD limit) .wbits := by
  refine ⟨rfl, deadD_rel.2.1, ?_, rfl⟩
  show (UInt64.ofNat (min (limit - fixedCost) 4294835199)).toNat + 132096 < 2 ^ 32
  rw [u64_ofNat (by omega)]
  omega

/-- A decoder at a stream's start. The limit must cover the fixed cost. -/
def decStart (limit : Nat) : DState × Status :=
  if limit < fixedCost then (⟨deadD, _, deadD_rel⟩, .memoryLimit)
  else (⟨liveD limit, _, liveD_rel limit⟩, .needsInput)

private theorem usize_of {n : Nat} (h : n < USize.size) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt h

/-- A state at a chunk's start. -/
@[inline] def atPos (D : Dec) (start : Nat) : Dec := { D with pos := USize.ofNat start }

theorem atPos_rel {D : Dec} {p : SPhase} (h : DRel D p) (start : Nat) : DRel (atPos D start) p :=
  h.congr rfl rfl rfl rfl rfl rfl rfl rfl

theorem atPos_inv {start stop : Nat} (D : { D : Dec // ∃ p, DRel D p }) (hl : start ≤ stop) (hu : stop < USize.size) :
    DInv (USize.ofNat stop) (atPos D.val start) := by
  obtain ⟨D, p, hrel⟩ := D
  refine ⟨⟨p, atPos_rel hrel start⟩, ?_⟩
  show (USize.ofNat start).toNat ≤ _
  rw [usize_of (by omega), usize_of hu]
  exact hl

/-- What a call leaves is a state with a place. -/
theorem callD_rel {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} {D : Dec} (h : DInv stop D) (buf : ByteArray) (space : Nat) :
    ∃ p, DRel (callD a stop hs final D h buf space).D p := by
  obtain ⟨p, hrel⟩ := h.1
  exact (callD_ok (hs := hs) (final := final) space D h p _ buf hrel rfl).rel

/-- One call. An input array and a chunk that don't fit each other can't come from a caller the goals allow. -/
def decStep (s : DState) (a : ByteArray) (start stop : Nat) (buf : ByteArray) (space : Nat) (final : Bool) : Reply DState :=
  if h : stop ≤ a.size ∧ start ≤ stop ∧ stop < USize.size then
    have hs : (USize.ofNat stop).toNat ≤ a.size := by
      rw [usize_of h.2.2]
      exact h.1
    let o := callD a (USize.ofNat stop) hs final (atPos s.val start) (atPos_inv s h.2.1 h.2.2) buf space
    { state := ⟨o.D, callD_rel _ _ _⟩, used := o.pos.toNat - start, output := o.buf, status := o.status }
  else { state := ⟨deadD, _, deadD_rel⟩, used := 0, output := buf, status := .rejected }

/-- The streaming decoder. -/
def decoder : Machine DState := ⟨decStart, decStep⟩

/-! ### A call's array -/

section
variable {x : List UInt8} {R : Run DState} {c : Call}

private theorem input_list :
    (R.input x c).data.toList = c.pre ++ ((x.drop R.read).take c.size ++ c.post) := by
  simp [Run.input, List.data_toByteArray]

private theorem take_length (h : R.read + c.size ≤ x.length) : ((x.drop R.read).take c.size).length = c.size := by
  simp only [List.length_take, List.length_drop]
  omega

private theorem input_size (h : R.read + c.size ≤ x.length) : (R.input x c).size = c.pre.length + c.size + c.post.length := by
  show (R.input x c).data.size = _
  rw [← Array.length_toList, input_list]
  simp only [List.length_append, take_length h]
  omega

/-- What's left of a call's chunk from a place in it, with what follows the chunk, is what's left of the stream. -/
private theorem chunk_rest (h : R.read + c.size ≤ x.length) {q : Nat} (hq : q ≤ c.size) :
    chunkBits (R.input x c) (c.pre.length + q) (c.pre.length + c.size) ++ bits (x.drop (R.read + c.size)) = bits (x.drop (R.read + q)) := by
  have hT := take_length h
  have e1 : chunk (R.input x c) (c.pre.length + q) (c.pre.length + c.size) = ((x.drop R.read).take c.size).drop q := by
    unfold chunk
    rw [input_list, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show c.pre.length + q - c.pre.length = q by omega, List.drop_append_of_le_length (by omega),
      show c.pre.length + c.size - (c.pre.length + q) = c.size - q by omega]
    exact List.take_left' (by rw [List.length_drop, hT])
  have e2 : x.drop (R.read + q) = ((x.drop R.read).take c.size).drop q ++ x.drop (R.read + c.size) := by
    conv => lhs; rw [← List.drop_drop]; rw [← List.take_append_drop c.size (x.drop R.read)]
    rw [List.drop_append_of_le_length (by omega), List.drop_drop]
  unfold chunkBits
  rw [e1, ← bits_append, ← e2]

end

/-! ### The invariant -/

/-- What every run of the decoder holds, for its stream. -/
structure TopInv (x : List UInt8) (R : Run DState) : Prop where
  read : R.read ≤ x.length
  starts : ∀ y, decode x = some y → R.emitted <+: y
  running : R.status.stopped = false → ∃ p, DRel R.state.val p ∧ Pend p R.state.val (R.emitted.map UInt8.toNat) ∧
    decode x = srest specSem p (R.state.val.held ++ bits (x.drop R.read))
  rejected : R.status = .rejected → decode x = none
  done : R.status = .done → R.ended = true ∧ R.read = x.length ∧ decode x = some R.emitted

private theorem map_roundtrip (l : List UInt8) : (l.map UInt8.toNat).map Nat.toUInt8 = l := by
  rw [List.map_map]
  conv => rhs; rw [← List.map_id l]
  apply List.map_congr_left
  intro b _
  exact UInt8.ofNat_toNat

/-- Bytes whose numbers start with a list's numbers start with that list. -/
private theorem map_split : ∀ (A L : List UInt8) (n : List Nat), L.map UInt8.toNat = A.map UInt8.toNat ++ n → ∃ L2, L = A ++ L2 ∧ L2.map UInt8.toNat = n
  | [], L, n, h => ⟨L, rfl, by simpa using h⟩
  | b :: A, [], n, h => by simp at h
  | b :: A, b2 :: L, n, h => by
    simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
    obtain ⟨L2, h1, h2⟩ := map_split A L n h.2
    refine ⟨L2, ?_, h2⟩
    rw [h1, UInt8.toNat_inj.mp h.1]
    rfl

/-- The reply to a call the caller may make, from a state at a place. -/
theorem reply_ok {x : List UInt8} {R : Run DState} {c : Call} {p : SPhase} (ha : R.Allowed x c) (hrel : DRel R.state.val p) (hE : Pend p R.state.val (R.emitted.map UInt8.toNat)) :
    ∃ o : Out, (R.reply decoder x c).state.val = o.D ∧ (R.reply decoder x c).used = o.pos.toNat - c.pre.length ∧ (R.reply decoder x c).output = o.buf ∧
      (R.reply decoder x c).status = o.status ∧
      CallOk (R.input x c) (USize.ofNat (c.pre.length + c.size)) c.final p (atPos R.state.val c.pre.length) (R.emitted.map UInt8.toNat) c.buf.toByteArray c.space o := by
  have hin := ha.inside
  have hfit := ha.fits
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  refine ⟨callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) c.buf.toByteArray c.space, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).state.val = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).used = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).output = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).status = _
    unfold decStep
    rw [dite_eq_left hg]
  · exact callD_ok _ _ _ p _ _ (atPos_rel hrel _) hE

/-- A state's bits at a place in a call's chunk, with what follows the chunk. -/
private theorem bits_at {x : List UInt8} {R : Run DState} {c : Call} (h : R.read + c.size ≤ x.length) (D' : Dec) {pos stop : USize} {q : Nat}
    (hq : pos.toNat = c.pre.length + q) (hqs : q ≤ c.size) (hstop : stop.toNat = c.pre.length + c.size) :
    D'.bits (R.input x c) pos stop (bits (x.drop (R.read + c.size))) = D'.held ++ bits (x.drop (R.read + q)) := by
  show D'.held ++ (chunkBits (R.input x c) pos.toNat stop.toNat ++ _) = _
  rw [hq, hstop, chunk_rest h hqs]

private theorem buf_list (l : List UInt8) : l.toByteArray.data.toList = l := by
  simp [List.data_toByteArray]

/-- Every run of the decoder holds the invariant. -/
theorem top_inv {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) : TopInv x R := by
  induction h with
  | start =>
    show TopInv x { state := (decStart limit).1, status := (decStart limit).2, read := 0, offered := 0, emitted := [], ended := false }
    by_cases hl : limit < fixedCost
    · have e : decStart limit = (⟨deadD, _, deadD_rel⟩, .memoryLimit) := by
        unfold decStart
        rw [ite_eq_left hl]
      rw [e]
      exact ⟨Nat.zero_le _, fun _ _ => List.nil_prefix, fun hs => Bool.noConfusion hs, fun hs => Status.noConfusion hs, fun hs => Status.noConfusion hs⟩
    · have e : decStart limit = (⟨liveD limit, _, liveD_rel limit⟩, .needsInput) := by
        unfold decStart
        rw [ite_eq_right hl]
      rw [e]
      refine ⟨Nat.zero_le _, fun _ _ => List.nil_prefix, fun _ => ⟨.wbits, liveD_rel limit, rfl, ?_⟩, fun hs => Status.noConfusion hs, fun hs => Status.noConfusion hs⟩
      rw [decode_srest]
      rfl
  | @call R c hR ha ih =>
    obtain ⟨p, hrel, hE, hdec⟩ := ih.running ha.running
    obtain ⟨o, e1, e2, e3, e4, hok⟩ := reply_ok ha hrel hE
    obtain ⟨c1, c2, _, n, c3, c4, c5, c6, c7, c8, c9⟩ := hok
    have hin := ha.inside
    have hfit := ha.fits
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
    rw [buf_list] at c3
    have hq : o.pos.toNat = c.pre.length + (o.pos.toNat - c.pre.length) := by
      rw [hpos0] at c1
      omega
    have hqs : o.pos.toNat - c.pre.length ≤ c.size := by
      rw [hstop] at c2
      omega
    have hb0 : (atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
        R.state.val.held ++ bits (x.drop R.read) := by
      have := bits_at (R := R) (c := c) hin (atPos R.state.val c.pre.length) hpos0 (Nat.zero_le _) hstop
      rw [this]
      rfl
    have hbn : o.D.bits (R.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
        o.D.held ++ bits (x.drop (R.read + (o.pos.toNat - c.pre.length))) := bits_at hin o.D hq hqs hstop
    obtain ⟨L2, hL, hLn⟩ := map_split c.buf _ n c3
    have hdrop : o.buf.data.toList.drop c.buf.length = L2 := by
      rw [hL]
      simp
    have hmap : (R.emitted ++ L2).map UInt8.toNat = R.emitted.map UInt8.toNat ++ n := by
      rw [List.map_append, hLn]
    have hstate : (R.after decoder x c).state.val = o.D := e1
    have hstatus : (R.after decoder x c).status = o.status := e4
    have hread : (R.after decoder x c).read = R.read + (o.pos.toNat - c.pre.length) := by
      show R.read + (R.reply decoder x c).used = _
      rw [e2]
    have hemit : (R.after decoder x c).emitted = R.emitted ++ L2 := by
      show R.emitted ++ (R.reply decoder x c).output.data.toList.drop c.buf.length = _
      rw [e3, hdrop]
    have hrestt : R.read + c.size = x.length → x.drop (R.read + c.size) = [] := fun e => by
      rw [e]
      exact List.drop_length
    have hdec' : decode x = srest specSem p ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size)))) := by
      rw [hb0, hdec]
    have hstart : ∀ (p' : SPhase) (y : List UInt8), Pend p' o.D (R.emitted.map UInt8.toNat ++ n) → srest specSem p' (o.D.held ++ bits (x.drop (R.read + (o.pos.toNat - c.pre.length)))) = some y →
        (R.emitted ++ L2) <+: y := by
      intro p' y hP hs
      have := hP.prefix (srest_out hs)
      rwa [← hmap, map_roundtrip] at this
    refine ⟨?_, fun y hy => ?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
    · rw [hread]
      omega
    · rw [hemit]
      cases hst : o.status with
      | needsInput =>
        obtain ⟨_, _, _, p', _, d5, d6⟩ := c5 hst
        rw [hdec', d6, hbn] at hy
        exact hstart p' y d5 hy
      | needsOutput =>
        obtain ⟨_, _, p', _, d5, d6⟩ := c6 hst
        rw [hdec', d6, hbn] at hy
        exact hstart p' y d5 hy
      | done =>
        obtain ⟨d1, _, d3⟩ := c7 hst
        rw [hdec', hrestt (ha.whole d1), d3, Option.some.injEq] at hy
        rw [← hy, ← hmap, map_roundtrip]
        exact List.prefix_refl _
      | rejected =>
        have := c8 hst (x.drop (R.read + c.size)) (fun f => hrestt (ha.whole f))
        rw [hdec', this] at hy
        cases hy
      | memoryLimit =>
        rw [hdec'] at hy
        have := c9 hst _ y hy
        rwa [← hmap, map_roundtrip] at this
    · rw [hstatus] at hs
      rw [hstate, hemit, hread, hmap]
      cases hst : o.status with
      | needsInput =>
        obtain ⟨_, _, _, p', d4, d5, d6⟩ := c5 hst
        exact ⟨p', d4, d5, by rw [hdec', d6, hbn]⟩
      | needsOutput =>
        obtain ⟨_, _, p', d4, d5, d6⟩ := c6 hst
        exact ⟨p', d4, d5, by rw [hdec', d6, hbn]⟩
      | done => rw [hst] at hs; cases hs
      | rejected => rw [hst] at hs; cases hs
      | memoryLimit => rw [hst] at hs; cases hs
    · rw [hstatus] at hs
      rw [hdec']
      exact c8 hs _ (fun f => hrestt (ha.whole f))
    · rw [hstatus] at hs
      obtain ⟨d1, d2, d3⟩ := c7 hs
      have hposv : o.pos.toNat = c.pre.length + c.size := by rw [d2]; exact hstop
      refine ⟨by simp [Run.after, d1], ?_, ?_⟩
      · rw [hread, hposv]
        have := ha.whole d1
        omega
      · rw [hemit, hdec', hrestt (ha.whole d1), d3, ← hmap, map_roundtrip]

/-- The reply to an allowed call, in the caller's terms. -/
private theorem reply_list {limit : Nat} {x : List UInt8} {R : Run DState} {c : Call} (hR : Reaches decoder limit x R) (ha : R.Allowed x c) :
    ∃ L2, (R.reply decoder x c).output.data.toList = c.buf ++ L2 ∧ L2.length ≤ c.space ∧ (R.reply decoder x c).used ≤ c.size ∧
      ((R.reply decoder x c).status = .needsInput → (R.reply decoder x c).used = c.size ∧ c.final = false) ∧
      ((R.reply decoder x c).status = .needsOutput → L2.length = c.space) := by
  obtain ⟨p, hrel, hE, _⟩ := (top_inv hR).running ha.running
  obtain ⟨o, _, e2, e3, e4, hok⟩ := reply_ok ha hrel hE
  obtain ⟨_, c2, _, n, c3, c4, c5, c6, _, _, _⟩ := hok
  have hfit := ha.fits
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
  rw [buf_list] at c3
  obtain ⟨L2, hL, hLn⟩ := map_split c.buf _ n c3
  have hlen : L2.length = n.length := by rw [← hLn, List.length_map]
  rw [hstop] at c2
  refine ⟨L2, by rw [e3, hL], by omega, by rw [e2]; omega, fun e => ?_, fun e => ?_⟩
  · rw [e4] at e
    obtain ⟨d1, d2, _⟩ := c5 e
    refine ⟨?_, d1⟩
    rw [e2, d2, hstop]
    omega
  · rw [e4] at e
    obtain ⟨d1, _⟩ := c6 e
    omega

private theorem size_data (b : ByteArray) : b.size = b.data.toList.length := by
  show b.data.size = _
  rw [Array.length_toList]

/-! ### Goals 1 and 4 -/

/-- Goal 1: a success gives exactly what `decode` gives, and a rejection means `decode` rejects. -/
theorem decoder_correct : Correct decoder where
  done h hs := (top_inv h).done hs
  rejected h hs := (top_inv h).rejected hs

/-- Goal 2: what's been handed out is always the start of a valid stream's output. -/
theorem decoder_noWrongBytes : NoWrongBytes decoder := fun h hd => (top_inv h).starts _ hd

/-- Goal 4, its truthful part. -/
theorem decoder_truthful : Truthful decoder where
  used_le hR ha := by
    obtain ⟨_, _, _, h, _⟩ := reply_list hR ha
    exact h
  keeps {_ _ _ c} hR ha := by
    obtain ⟨L2, h, _⟩ := reply_list hR ha
    exact ⟨L2, h.symm⟩
  output_le {_ _ _ c} hR ha := by
    obtain ⟨L2, h, h2, _⟩ := reply_list hR ha
    rw [size_data, h, List.length_append]
    omega
  needsInput hR ha hs := by
    obtain ⟨_, _, _, _, h, _⟩ := reply_list hR ha
    exact h hs
  needsOutput {_ _ _ c} hR ha hs := by
    obtain ⟨L2, h, _, _, _, h2⟩ := reply_list hR ha
    rw [size_data, h, List.length_append, h2 hs]

/-! ### Goal 4, its terminating part -/

/-- The reply to a call the caller may make, in the measure's terms. -/
private theorem reply_down {x : List UInt8} {R : Run DState} {c : Call} {p : SPhase} (ha : R.Allowed x c) (hrel : DRel R.state.val p) :
    ∃ o : Out, (R.reply decoder x c).state.val = o.D ∧ (R.reply decoder x c).used = o.pos.toNat - c.pre.length ∧ (R.reply decoder x c).status = o.status ∧
      o.pos.toNat ≤ c.pre.length + c.size ∧ c.pre.length ≤ o.pos.toNat ∧
      CallM (R.input x c) (USize.ofNat (c.pre.length + c.size)) p (atPos R.state.val c.pre.length) c.space o := by
  have hin := ha.inside
  have hfit := ha.fits
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hinv := atPos_inv (start := c.pre.length) R.state hg.2.1 hg.2.2
  have hok := callD_ok (hs := hs) (final := c.final) c.space _ hinv p _ c.buf.toByteArray (atPos_rel hrel _) rfl
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
  have h1 := hok.posLe
  have h2 := hok.posStop
  rw [hpos0] at h1
  rw [hstop] at h2
  refine ⟨callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length) hinv c.buf.toByteArray c.space, ?_, ?_, ?_, h2, h1, ?_⟩
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).state.val = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).used = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).status = _
    unfold decStep
    rw [dite_eq_left hg]
  · exact callD_down _ _ _ p _ (atPos_rel hrel _)

/-- What's left of a run: the measure, then the bytes waiting, then the stream's bytes not used. -/
private def runMeas (x : List UInt8) (p : SPhase) (R : Run DState) : Meas × (Nat × Nat) :=
  (mOf p (R.state.val.held ++ bits (x.drop R.read)), (R.state.val.cmd.pend.toNat, x.length - R.read))

/-- Lower in what's left of a run. -/
private def RunLt (a b : Meas × (Nat × Nat)) : Prop := MLt a.1 b.1 ∨ (a.1 = b.1 ∧ LexLt a.2 b.2)

private theorem runLt_wf : WellFounded RunLt := plex_wf mlt_wf lexLt_wf

/-- Goal 4, its terminating part: no caller answering the signals can keep the decoder running forever. -/
theorem decoder_terminates : Terminates decoder := by
  intro limit x R hR
  have key : ∀ (m : Meas × (Nat × Nat)) (R : Run DState) (p : SPhase), Reaches decoder limit x R → DRel R.state.val p →
      (R.status = .needsInput → R.state.val.cmd.pend = 0) → (R.status = .needsOutput → R.state.val.cmd.pend ≠ 0) → runMeas x p R = m →
      Acc (Follows decoder limit x) R := by
    intro m
    induction m using runLt_wf.induction with
    | _ m ih =>
      intro R p hR hrel hin hout hm
      refine Acc.intro R fun R' hf => ?_
      obtain ⟨_, c, ha, hans, rfl⟩ := hf
      obtain ⟨o, e1, e2, e4, h1, h2, hM⟩ := reply_down ha hrel
      have hinside := ha.inside
      have hfit := ha.fits
      have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
      have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
      have hq : o.pos.toNat = c.pre.length + (o.pos.toNat - c.pre.length) := by omega
      have hb0 : (atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
          R.state.val.held ++ bits (x.drop R.read) := by
        have := bits_at (R := R) (c := c) hinside (atPos R.state.val c.pre.length) hpos0 (Nat.zero_le _) hstop
        rw [this]
        rfl
      have hbn : o.D.bits (R.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
          o.D.held ++ bits (x.drop (R.read + (o.pos.toNat - c.pre.length))) := bits_at hinside o.D hq (by omega) hstop
      have hstate : (R.after decoder x c).state.val = o.D := e1
      have hstatus : (R.after decoder x c).status = o.status := e4
      have hread : (R.after decoder x c).read = R.read + (o.pos.toNat - c.pre.length) := by
        show R.read + (R.reply decoder x c).used = _
        rw [e2]
      have hdead : o.status.stopped = true → Acc (Follows decoder limit x) (R.after decoder x c) := by
        intro hs
        refine Acc.intro _ fun R2 hf => ?_
        obtain ⟨_, c2, ha2, _⟩ := hf
        have := ha2.running
        rw [hstatus, hs] at this
        cases this
      have hlist := reply_list hR ha
      -- From what a call did to the measure, what's left of the run is lower.
      have hgo : ∀ (p' : SPhase), MCall (R.input x c) (USize.ofNat (c.pre.length + c.size)) p p' (atPos R.state.val c.pre.length) c.space o →
          (o.status = .needsInput → o.D.cmd.pend = 0) → (o.status = .needsOutput → o.D.cmd.pend ≠ 0) → (o.status = .needsInput ∨ o.status = .needsOutput) →
          RunLt (runMeas x p' (R.after decoder x c)) m := by
        intro p' hc hi ho hrun
        rw [← hm]
        have ha1 : (runMeas x p' (R.after decoder x c)).1 = mOf p' (o.D.bits (R.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size)))) := by
          rw [hbn]
          show mOf p' ((R.after decoder x c).state.val.held ++ bits (x.drop (R.after decoder x c).read)) = _
          rw [hstate, hread]
        have ha2 : (runMeas x p R).1 = mOf p ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size)))) := by
          rw [hb0]
          rfl
        have hp1 : (runMeas x p' (R.after decoder x c)).2.1 = o.D.cmd.pend.toNat := by
          show (R.after decoder x c).state.val.cmd.pend.toNat = _
          rw [hstate]
        have hp2 : (runMeas x p R).2.1 = R.state.val.cmd.pend.toNat := rfl
        have hu1 : (runMeas x p' (R.after decoder x c)).2.2 = x.length - (R.read + (o.pos.toNat - c.pre.length)) := by
          show x.length - (R.after decoder x c).read = _
          rw [hread]
        have hu2 : (runMeas x p R).2.2 = x.length - R.read := rfl
        rcases hc with hc | ⟨hc1, hc2, hc3⟩
        · exact Or.inl (by rw [ha1, ha2]; exact hc _)
        · refine Or.inr ⟨by rw [ha1, ha2]; exact hc1 _, ?_⟩
          have hc2' : o.D.cmd.pend.toNat ≤ R.state.val.cmd.pend.toNat := hc2
          have hc3' : R.state.val.cmd.pend.toNat ≠ 0 → c.space ≠ 0 → o.D.cmd.pend.toNat < R.state.val.cmd.pend.toNat := hc3
          cases hsR : R.status with
          | needsOutput =>
            have hne : R.state.val.cmd.pend.toNat ≠ 0 := fun e => hout hsR (USize.toNat_inj.mp e)
            have hsp := hans.2 hsR
            exact Or.inl (by rw [hp1, hp2]; exact hc3' hne (by omega))
          | needsInput =>
            have h0 : R.state.val.cmd.pend.toNat = 0 := by rw [hin hsR]; rfl
            rcases hrun with hst | hst
            · obtain ⟨_, _, _, _, hIn, _⟩ := hlist
              obtain ⟨hu, hf⟩ := hIn (e4.trans hst)
              rw [e2] at hu
              have hsize : 0 < c.size := by
                rcases hans.1 hsR with h | h
                · exact h
                · rw [hf] at h
                  cases h
              have h3 : o.D.cmd.pend.toNat = 0 := by rw [hi hst]; rfl
              exact Or.inr ⟨by rw [hp1, hp2]; omega, by rw [hu1, hu2]; omega⟩
            · have hne : o.D.cmd.pend.toNat ≠ 0 := fun e => ho hst (USize.toNat_inj.mp e)
              omega
          | done => have := ha.running; rw [hsR] at this; cases this
          | rejected => have := ha.running; rw [hsR] at this; cases this
          | memoryLimit => have := ha.running; rw [hsR] at this; cases this
      cases hst : o.status with
      | done => exact hdead (by rw [hst]; rfl)
      | rejected => exact hdead (by rw [hst]; rfl)
      | memoryLimit => exact hdead (by rw [hst]; rfl)
      | needsInput =>
        obtain ⟨b1, p', b2, b3⟩ := hM.needsInput hst
        exact ih _ (hgo p' b3 (fun _ => b1) (fun e => by rw [hst] at e; cases e) (Or.inl hst)) _ p' (.call hR ha) (by rw [hstate]; exact b2)
          (fun _ => by rw [hstate]; exact b1) (fun e => by rw [hstatus, hst] at e; cases e) rfl
      | needsOutput =>
        obtain ⟨b1, p', b2, b3⟩ := hM.needsOutput hst
        exact ih _ (hgo p' b3 (fun e => by rw [hst] at e; cases e) (fun _ => b1) (Or.inr hst)) _ p' (.call hR ha) (by rw [hstate]; exact b2)
          (fun e => by rw [hstatus, hst] at e; cases e) (fun _ => by rw [hstate]; exact b1) rfl
  have hpend : ∀ {R : Run DState}, Reaches decoder limit x R → (R.status = .needsInput → R.state.val.cmd.pend = 0) ∧ (R.status = .needsOutput → R.state.val.cmd.pend ≠ 0) := by
    intro R hR
    cases hR with
    | start =>
      show ((decStart limit).2 = .needsInput → (decStart limit).1.val.cmd.pend = 0) ∧ ((decStart limit).2 = .needsOutput → (decStart limit).1.val.cmd.pend ≠ 0)
      by_cases hl : limit < fixedCost
      · have e : decStart limit = (⟨deadD, _, deadD_rel⟩, .memoryLimit) := by
          unfold decStart
          rw [ite_eq_left hl]
        rw [e]
        exact ⟨fun h => Status.noConfusion h, fun h => Status.noConfusion h⟩
      · have e : decStart limit = (⟨liveD limit, _, liveD_rel limit⟩, .needsInput) := by
          unfold decStart
          rw [ite_eq_right hl]
        rw [e]
        exact ⟨fun _ => rfl, fun h => Status.noConfusion h⟩
    | @call R0 c hR0 ha =>
      obtain ⟨p, hrel, _⟩ := (top_inv hR0).running ha.running
      obtain ⟨o, e1, _, e4, _, _, hM⟩ := reply_down ha hrel
      have hstate : (R0.after decoder x c).state.val = o.D := e1
      have hstatus : (R0.after decoder x c).status = o.status := e4
      rw [hstate, hstatus]
      exact ⟨fun e => (hM.needsInput e).1, fun e => (hM.needsOutput e).1⟩
  cases hs : R.status.stopped with
  | true =>
    refine Acc.intro R fun R2 hf => ?_
    obtain ⟨_, c2, ha2, _⟩ := hf
    have := ha2.running
    rw [hs] at this
    cases this
  | false =>
    obtain ⟨p, hrel, _⟩ := (top_inv hR).running hs
    exact key _ R p hR hrel (hpend hR).1 (hpend hR).2 rfl

end Brotli.Decoder
