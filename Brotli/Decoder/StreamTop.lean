module

public import Brotli.Decoder.StreamMem
public import Brotli.Decoder.StreamLimit
public import Brotli.Decoder.Restrict

@[expose] public section

/-!
# The decoder

The streaming decoder as a `Machine`, and the invariants over every run that tie it to `decode` and to what the stream demands.
The correctness goals follow from them.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The decoder's state between calls. -/
abbrev DState := { D : Dec // ∃ p, DRel D p }

/-- A state at a stream's start, with what the limit leaves for the window and the tables. -/
def liveD (limit : Nat) : Dec := { deadD with limit := UInt64.ofNat (min (limit - fixedCost) 4294958151) }

theorem liveD_rel (limit : Nat) : DRel (liveD limit) .wbits := by
  refine ⟨rfl, deadD_rel.2.1, ?_, rfl, rfl⟩
  show (UInt64.ofNat (min (limit - fixedCost) 4294958151)).toNat + 9144 < 2 ^ 32
  rw [u64_ofNat (by omega)]
  omega

/-- A decoder at a stream's start. The limit must cover the fixed cost. -/
def decStart (limit : Nat) : DState × Status :=
  if limit < fixedCost then (⟨deadD, _, deadD_rel⟩, .memoryLimit)
  else (⟨liveD limit, _, liveD_rel limit⟩, .needsInput)

theorem usize_of {n : Nat} (h : n < USize.size) : (USize.ofNat n).toNat = n := by
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

theorem input_list :
    (R.input x c).data.toList = c.pre ++ ((x.drop R.read).take c.size ++ c.post) := by
  simp [Run.input, List.data_toByteArray]

theorem take_length (h : R.read + c.size ≤ x.length) : ((x.drop R.read).take c.size).length = c.size := by
  simp only [List.length_take, List.length_drop]
  omega

theorem input_size (h : R.read + c.size ≤ x.length) : (R.input x c).size = c.pre.length + c.size + c.post.length := by
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
theorem bits_at {x : List UInt8} {R : Run DState} {c : Call} (h : R.read + c.size ≤ x.length) (D' : Dec) {pos stop : USize} {q : Nat}
    (hq : pos.toNat = c.pre.length + q) (hqs : q ≤ c.size) (hstop : stop.toNat = c.pre.length + c.size) :
    D'.bits (R.input x c) pos stop (bits (x.drop (R.read + c.size))) = D'.held ++ bits (x.drop (R.read + q)) := by
  show D'.held ++ (chunkBits (R.input x c) pos.toNat stop.toNat ++ _) = _
  rw [hq, hstop, chunk_rest h hqs]

private theorem buf_list (l : List UInt8) : l.toByteArray.data.toList = l := by
  simp [List.data_toByteArray]

/-- What's left of a call's chunk from a place in it. -/
theorem chunk_input {x : List UInt8} {R : Run DState} {c : Call} (h : R.read + c.size ≤ x.length) {q : Nat} (hqs : q ≤ c.size) :
    chunk (R.input x c) (c.pre.length + q) (c.pre.length + c.size) = ((x.drop R.read).take c.size).drop q := by
  have hT := take_length (R := R) (c := c) h
  unfold chunk
  rw [input_list, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    show c.pre.length + q - c.pre.length = q by omega, List.drop_append_of_le_length (by omega),
    show c.pre.length + c.size - (c.pre.length + q) = c.size - q by omega]
  exact List.take_left' (by rw [List.length_drop, hT])

/-- A state's bits at a place in a call's chunk, with any bytes after the chunk. -/
theorem bits_at' {x : List UInt8} {R : Run DState} {c : Call} (h : R.read + c.size ≤ x.length) (D' : Dec) {pos stop : USize} {q : Nat}
    (hq : pos.toNat = c.pre.length + q) (hqs : q ≤ c.size) (hstop : stop.toNat = c.pre.length + c.size) (t : List UInt8) :
    D'.bits (R.input x c) pos stop (bits t) = D'.held ++ bits (((x.drop R.read).take c.size).drop q ++ t) := by
  have e1 := chunk_input (R := R) (c := c) h hqs
  show D'.held ++ (chunkBits (R.input x c) pos.toNat stop.toNat ++ _) = _
  rw [hq, hstop]
  unfold chunkBits
  rw [e1, ← bits_append]

/-- A stream's first bytes, cut further on. -/
private theorem take_split {α : Type} (x : List α) {i j : Nat} (h : i ≤ j) : x.take j = x.take i ++ (x.take j).drop i := by
  conv => lhs; rw [← List.take_append_drop i (x.take j)]
  rw [List.take_take, Nat.min_eq_left h]

/-- The bytes between two places, cut at a third. -/
private theorem seg_split {α : Type} (x : List α) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) (hi : i ≤ x.length) :
    (x.take k).drop i = (x.take j).drop i ++ (x.take k).drop j := by
  conv => lhs; rw [← List.take_append_drop j (x.take k)]
  rw [List.take_take, Nat.min_eq_left hjk, List.drop_append_of_le_length (by rw [List.length_take]; omega)]

/-- A chunk's bytes from a place in it, then the bytes up to further on. -/
private theorem chunk_seg {α : Type} (x : List α) {r s u H : Nat} (hu : u ≤ s) (hs : r + s ≤ H) (hx : r + s ≤ x.length) :
    ((x.drop r).take s).drop u ++ (x.take H).drop (r + s) = (x.take H).drop (r + u) := by
  rw [seg_split x (show r + u ≤ r + s by omega) hs (by omega)]
  congr 1
  rw [List.drop_take, List.drop_drop, List.drop_take]
  congr 1
  omega

/-- The reading in order of the bytes offered before a call, then of a call's chunk up to a place in it. -/
private theorem chain_reach {x : List UInt8} {R : Run DState} {c : Call} (hin : R.read + c.size ≤ x.length)
    (hfit : c.pre.length + c.size + c.post.length < USize.size) (hro : R.read ≤ R.offered) {p p' : SPhase} {D' : Dec}
    (hreach : ∀ u : List UInt8, Reach sStep .wbits (bits (x.take R.offered ++ u)) p (R.state.val.held ++ bits ((x.take R.offered).drop R.read ++ u)))
    (hq1 : c.pre.length ≤ D'.pos.toNat) (hq2 : D'.pos.toNat ≤ c.pre.length + c.size)
    (hj : ∀ t : List UInt8, Reach sStep p ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos
      (USize.ofNat (c.pre.length + c.size)) (bits t)) p' (D'.bits (R.input x c) D'.pos (USize.ofNat (c.pre.length + c.size)) (bits t))) :
    ∀ u : List UInt8, Reach sStep .wbits (bits (x.take (max R.offered (R.read + c.size)) ++ u)) p'
      (D'.held ++ bits ((x.take (max R.offered (R.read + c.size))).drop (R.read + (D'.pos.toNat - c.pre.length)) ++ u)) := by
  intro u
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
  have hq : D'.pos.toNat = c.pre.length + (D'.pos.toNat - c.pre.length) := by omega
  have hqs : D'.pos.toNat - c.pre.length ≤ c.size := by omega
  generalize hH : max R.offered (R.read + c.size) = H
  have h1 := hreach ((x.take H).drop R.offered ++ u)
  rw [← List.append_assoc, ← take_split x (show R.offered ≤ H by omega), ← List.append_assoc,
    ← seg_split x hro (show R.offered ≤ H by omega) (by omega)] at h1
  have h2 := hj ((x.take H).drop (R.read + c.size) ++ u)
  rw [bits_at' hin _ hpos0 (Nat.zero_le _) hstop, bits_at' hin _ hq hqs hstop, ← List.append_assoc, ← List.append_assoc,
    chunk_seg x (Nat.zero_le _) (show R.read + c.size ≤ H by omega) hin, chunk_seg x hqs (show R.read + c.size ≤ H by omega) hin,
    Nat.add_zero] at h2
  have e0 : (atPos R.state.val c.pre.length).held = R.state.val.held := rfl
  rw [e0] at h2
  exact h1.trans h2

/-- What every run of the decoder holds of the spec's reading in order: a running state stands for a place where the
reading in order takes the bytes offered so far, with the bytes offered but not used still to read, whatever bytes follow;
and needing input means the reading in order pauses there with the bits the state holds. -/
structure OrderInv (x : List UInt8) (R : Run DState) : Prop where
  running : R.status.stopped = false → ∃ p, DRel R.state.val p ∧ Pend p R.state.val (R.emitted.map UInt8.toNat) ∧
    R.read ≤ R.offered ∧
    (∀ u : List UInt8, Reach sStep .wbits (bits (x.take R.offered ++ u)) p (R.state.val.held ++ bits ((x.take R.offered).drop R.read ++ u))) ∧
    (R.status = .needsInput → SPause p R.state.val.held ∧ R.state.val.cmd.pend = 0) ∧
    (R.status = .needsOutput → R.state.val.cmd.pend ≠ 0)

/-- A reply that needs input has no bytes waiting, and one that needs output has some. -/
private theorem reply_pend {x : List UInt8} {R : Run DState} {c : Call} {p : SPhase} (ha : R.Allowed x c) (hrel : DRel R.state.val p) :
    ((R.reply decoder x c).status = .needsInput → (R.reply decoder x c).state.val.cmd.pend = 0) ∧
    ((R.reply decoder x c).status = .needsOutput → (R.reply decoder x c).state.val.cmd.pend ≠ 0) := by
  have hin := ha.inside
  have hfit := ha.fits
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs' : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hm := callD_down (hs := hs') (final := c.final) c.space (atPos R.state.val c.pre.length) (atPos_inv R.state hg.2.1 hg.2.2) p
    c.buf.toByteArray (atPos_rel hrel _)
  show ((decStep R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final).status = .needsInput →
      (decStep R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final).state.val.cmd.pend = 0) ∧
    ((decStep R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final).status = .needsOutput →
      (decStep R.state (R.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final).state.val.cmd.pend ≠ 0)
  unfold decStep
  rw [dite_eq_left hg]
  exact ⟨fun hs2 => (hm.needsInput hs2).1, fun hs2 => (hm.needsOutput hs2).1⟩

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
    obtain ⟨c1, c2, _, ⟨n, c3, c4, c5, c6, c7, c8, c9⟩, _⟩ := hok
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
        obtain ⟨_, _, _, p', _, d5, d6, _⟩ := c5 hst
        rw [hdec', d6, hbn] at hy
        exact hstart p' y d5 hy
      | needsOutput =>
        obtain ⟨_, _, p', _, d5, d6, _⟩ := c6 hst
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
        have := (c9 hst).1 _ y hy
        rwa [← hmap, map_roundtrip] at this
    · rw [hstatus] at hs
      rw [hstate, hemit, hread, hmap]
      cases hst : o.status with
      | needsInput =>
        obtain ⟨_, _, _, p', d4, d5, d6, _⟩ := c5 hst
        exact ⟨p', d4, d5, by rw [hdec', d6, hbn]⟩
      | needsOutput =>
        obtain ⟨_, _, p', d4, d5, d6, _⟩ := c6 hst
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

/-- Every run of the decoder holds the invariant of the spec's reading in order. -/
theorem order_inv {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) : OrderInv x R := by
  induction h with
  | start =>
    show OrderInv x { state := (decStart limit).1, status := (decStart limit).2, read := 0, offered := 0, emitted := [], ended := false }
    by_cases hl : limit < fixedCost
    · have e : decStart limit = (⟨deadD, _, deadD_rel⟩, .memoryLimit) := by
        unfold decStart
        rw [ite_eq_left hl]
      rw [e]
      exact ⟨fun hs => Bool.noConfusion hs⟩
    · have e : decStart limit = (⟨liveD limit, _, liveD_rel limit⟩, .needsInput) := by
        unfold decStart
        rw [ite_eq_right hl]
      rw [e]
      refine ⟨fun _ => ⟨.wbits, liveD_rel limit, rfl, Nat.le_refl _, fun u => ?_, fun _ => ⟨⟨.wbits, [], .refl _ _, rfl, Or.inl rfl⟩, rfl⟩,
        fun e => Status.noConfusion e⟩⟩
      exact .refl _ _
  | @call R c hR ha ih =>
    have hin := ha.inside
    have hfit := ha.fits
    have hox := hR.offered_le
    cases hs0 : (R.after decoder x c).status.stopped with
    | true => exact ⟨fun e => by rw [hs0] at e; cases e⟩
    | false =>
    obtain ⟨p, hrel, hE, hro, hreach, _⟩ := ih.running ha.running
    obtain ⟨o, e1, e2, e3, e4, hok⟩ := reply_ok ha hrel hE
    obtain ⟨c1, c2, _, ⟨n, c3, _, c5, c6, _, _, _⟩, _⟩ := hok
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
    rw [buf_list] at c3
    have hq : o.pos.toNat = c.pre.length + (o.pos.toNat - c.pre.length) := by
      rw [hpos0] at c1
      omega
    have hqs : o.pos.toNat - c.pre.length ≤ c.size := by
      rw [hstop] at c2
      omega
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
    have hoff : (R.after decoder x c).offered = max R.offered (R.read + c.size) := rfl
    -- The reading in order, from the bytes offered before the call to those offered after it.
    have hgo : ∀ p' : SPhase, (∀ t : List UInt8, Reach sStep p ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos
        (USize.ofNat (c.pre.length + c.size)) (bits t)) p' (o.D.bits (R.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits t))) →
        ∀ u : List UInt8, Reach sStep .wbits (bits (x.take (R.after decoder x c).offered ++ u)) p'
          ((R.after decoder x c).state.val.held ++ bits ((x.take (R.after decoder x c).offered).drop (R.after decoder x c).read ++ u)) := by
      intro p' hj u
      rw [hstate, hread, hoff]
      generalize hH : max R.offered (R.read + c.size) = H
      have h1 := hreach ((x.take H).drop R.offered ++ u)
      rw [← List.append_assoc, ← take_split x (show R.offered ≤ H by omega), ← List.append_assoc,
        ← seg_split x hro (show R.offered ≤ H by omega) (by omega)] at h1
      have h2 := hj ((x.take H).drop (R.read + c.size) ++ u)
      rw [bits_at' hin _ hpos0 (Nat.zero_le _) hstop, bits_at' hin _ hq hqs hstop, ← List.append_assoc, ← List.append_assoc,
        chunk_seg x (Nat.zero_le _) (show R.read + c.size ≤ H by omega) hin, chunk_seg x hqs (show R.read + c.size ≤ H by omega) hin,
        Nat.add_zero] at h2
      have e0 : (atPos R.state.val c.pre.length).held = R.state.val.held := rfl
      rw [e0] at h2
      exact h1.trans h2
    have hro' : (R.after decoder x c).read ≤ (R.after decoder x c).offered := by
      rw [hread, hoff]
      omega
    refine ⟨fun _ => ?_⟩
    rw [hstatus] at hs0 ⊢
    cases hst : o.status with
    | needsInput =>
      obtain ⟨_, _, _, p', d4, d5, _, d7, d8⟩ := c5 hst
      have hz := (reply_pend ha hrel).1 (e4.trans hst)
      rw [e1] at hz
      refine ⟨p', by rw [hstate]; exact d4, by rw [hstate, hemit, hmap]; exact d5, hro', hgo p' d7, fun _ => by rw [hstate]; exact ⟨d8, hz⟩,
        fun e => Status.noConfusion e⟩
    | needsOutput =>
      obtain ⟨_, _, p', d4, d5, _, d7⟩ := c6 hst
      have hz := (reply_pend ha hrel).2 (e4.trans hst)
      rw [e1] at hz
      refine ⟨p', by rw [hstate]; exact d4, by rw [hstate, hemit, hmap]; exact d5, hro', hgo p' d7, fun e => Status.noConfusion e,
        fun _ => by rw [hstate]; exact hz⟩
    | done => rw [hst] at hs0; cases hs0
    | rejected => rw [hst] at hs0; cases hs0
    | memoryLimit => rw [hst] at hs0; cases hs0

/-- A decoder that reports the memory limit has handed out every byte the spec's reading in order of the bytes offered has
produced up to where the limit binds: for the window, at the stream's first meta-block with data, where nothing has been
produced, so as at WBITS; or in a meta-block's header, for its tables. -/
theorem decoder_limitHandsOut {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .memoryLimit) :
    ∃ p, (p = .wbits ∨ ∃ w st last mlen g q, p = .hdr w st last mlen g q) ∧ p.out.reverse.map Nat.toUInt8 = R.emitted ∧
      ∀ u : List UInt8, ∃ bs, Reach sStep .wbits (bits (x.take R.offered ++ u)) p bs := by
  cases h with
  | start => exact ⟨.wbits, Or.inl rfl, rfl, fun u => ⟨_, .refl _ _⟩⟩
  | @call R0 c hR ha =>
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨p, hrel, hE, hro, hreach, _⟩ := (order_inv hR).running ha.running
    obtain ⟨o, _, _, e3, e4, hok⟩ := reply_ok ha hrel hE
    obtain ⟨_, _, _, ⟨n, c3, _, _, _, _, _, c9⟩, _⟩ := hok
    have hst : o.status = .memoryLimit := by rw [← e4]; exact hs
    obtain ⟨p2, D2, _, d2, d3, d4, d5, d6, d7⟩ := (c9 hst).2
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R0.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
    rw [hpos0] at d2
    rw [hstop] at d3
    have key : p2.out.reverse.map Nat.toUInt8 = (R0.after decoder x c).emitted := by
      rw [buf_list] at c3
      obtain ⟨L2, hL, hLn⟩ := map_split c.buf _ n c3
      have hdrop : o.buf.data.toList.drop c.buf.length = L2 := by
        rw [hL]
        simp
      have hemit : (R0.after decoder x c).emitted = R0.emitted ++ L2 := by
        show R0.emitted ++ (R0.reply decoder x c).output.data.toList.drop c.buf.length = _
        rw [e3, hdrop]
      unfold Pend at d4
      have hz : D2.cmd.pend.toNat = 0 := by rw [d6]; rfl
      rw [hz, List.drop_zero] at d4
      rw [d4, hemit, ← hLn, ← List.map_append, map_roundtrip]
    -- At a meta-block's start with nothing produced, where the window doesn't fit, the stream's start stands for it.
    rcases d7 with ⟨w, rfl⟩ | hh
    · exact ⟨.wbits, Or.inl rfl, key, fun u => ⟨_, .refl _ _⟩⟩
    · exact ⟨p2, Or.inr hh, key, fun u => ⟨_, chain_reach hin hfit hro hreach d2 d3 d5 u⟩⟩

/-- The reading in order of the bytes offered, cut back to the bytes used. -/
theorem reach_used {x : List UInt8} {R : Run DState} {p : SPhase} (hro : R.read ≤ R.offered)
    (hreach : ∀ u : List UInt8, Reach sStep .wbits (bits (x.take R.offered ++ u)) p (R.state.val.held ++ bits ((x.take R.offered).drop R.read ++ u))) :
    Reach sStep .wbits (bits (x.take R.read)) p R.state.val.held := by
  have h1 := hreach []
  simp only [List.append_nil] at h1
  have e : bits (x.take R.offered) = bits (x.take R.read) ++ bits ((x.take R.offered).drop R.read) := by
    rw [← bits_append, ← take_split x hro]
  rw [e] at h1
  exact reach_restrict nfaith_sStep h1 _ _ _ rfl rfl (by rw [bits_length]; omega)

/-- A decoder that needs input stands where the spec's reading in order of the bytes it has used comes to, holding the
bits that reading has left; from there the reading in order, producing nothing more, comes to too few bits or to the
stream's end; and every byte the reading in order has produced has been handed out. -/
theorem decoder_inOrder {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .needsInput) :
    ∃ p, Reach sStep .wbits (bits (x.take R.read)) p R.state.val.held ∧ SPause p R.state.val.held ∧
      p.out.reverse.map Nat.toUInt8 = R.emitted := by
  obtain ⟨p, _, hE, hro, hreach, hpause, _⟩ := (order_inv h).running (by rw [hs]; rfl)
  obtain ⟨hsp, hz⟩ := hpause hs
  refine ⟨p, reach_used hro hreach, hsp, ?_⟩
  unfold Pend at hE
  simp only [hz, USize.toNat_zero, List.drop_zero] at hE
  rw [hE, map_roundtrip]

/-- A decoder that needs output space stands where the spec's reading in order of the bytes it has used comes to, and that
reading has produced more bytes than have been handed out, which start with them. -/
theorem decoder_waits {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .needsOutput) :
    ∃ p, Reach sStep .wbits (bits (x.take R.read)) p R.state.val.held ∧ R.emitted.length < p.out.length ∧
      R.emitted <+: p.out.reverse.map Nat.toUInt8 := by
  obtain ⟨p, hrel, hE, hro, hreach, _, hout⟩ := (order_inv h).running (by rw [hs]; rfl)
  have hz : R.state.val.cmd.pend.toNat ≠ 0 := fun e => hout hs (USize.toNat_inj.mp e)
  have hle := hrel.pendOut
  unfold Pend at hE
  refine ⟨p, reach_used hro hreach, ?_, ?_⟩
  · have hl := congrArg List.length hE
    simp only [List.length_reverse, List.length_drop, List.length_map] at hl
    omega
  · rw [← List.take_append_drop R.state.val.cmd.pend.toNat p.out, List.reverse_append, List.map_append, hE, map_roundtrip]
    exact List.prefix_append _ _

/-- A decoder never asks for input where the spec's reading in order of the bytes it has used rejects. -/
theorem decoder_noLateReject {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .needsInput) :
    ¬ ∃ q c, Reach sStep .wbits (bits (x.take R.read)) q c ∧ sStep q c = .bad := by
  obtain ⟨p, h1, ⟨q0, c0, h2, _, h3⟩, _⟩ := decoder_inOrder h hs
  rintro ⟨q, c, h4, h5⟩
  have hn0 : ∀ p' a', sStep q0 c0 ≠ .next p' a' := by
    intro p' a' e
    rcases h3 with h3 | ⟨y, h3⟩ <;> rw [h3] at e <;> cases e
  rcases Reach.total (h1.trans h2) h4 with h6 | h6
  · obtain ⟨rfl, rfl⟩ := Reach.stuck h6 hn0
    rcases h3 with h3 | ⟨y, h3⟩ <;> rw [h3] at h5 <;> cases h5
  · obtain ⟨rfl, rfl⟩ := Reach.stuck h6 (fun p' a' e => by rw [h5] at e; cases e)
    rcases h3 with h3 | ⟨y, h3⟩ <;> rw [h3] at h5 <;> cases h5

/-- The reply to an allowed call, in the caller's terms. -/
private theorem reply_list {limit : Nat} {x : List UInt8} {R : Run DState} {c : Call} (hR : Reaches decoder limit x R) (ha : R.Allowed x c) :
    ∃ L2, (R.reply decoder x c).output.data.toList = c.buf ++ L2 ∧ L2.length ≤ c.space ∧ (R.reply decoder x c).used ≤ c.size ∧
      ((R.reply decoder x c).status = .needsInput → (R.reply decoder x c).used = c.size ∧ c.final = false) ∧
      ((R.reply decoder x c).status = .needsOutput → L2.length = c.space) := by
  obtain ⟨p, hrel, hE, _⟩ := (top_inv hR).running ha.running
  obtain ⟨o, _, e2, e3, e4, hok⟩ := reply_ok ha hrel hE
  obtain ⟨_, c2, _, ⟨n, c3, c4, c5, c6, _, _, _⟩, _⟩ := hok
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

/-- Soundness and completeness: a success gives exactly what `decode` gives, and a rejection means `decode` rejects. -/
theorem decoder_correct : Correct decoder where
  done h hs := (top_inv h).done hs
  rejected h hs := (top_inv h).rejected hs

/-- Prefix soundness: what's been handed out is always the start of a valid stream's output. -/
theorem decoder_noWrongBytes : NoWrongBytes decoder := fun h hd => (top_inv h).starts _ hd

/-- Totality and progress, its truthful part. -/
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

/-! ### Totality and progress, the terminating part -/

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

/-- Totality and progress, its terminating part: no caller answering the signals can keep the decoder running forever. -/
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

/-! ### Memory usage correctness -/

/-- What the limit leaves for the window and the tables. -/
def roomOf (limit : Nat) : Nat := min (limit - fixedCost) 4294958151

/-- What every run of the decoder holds, for its stream. -/
structure MemTop (limit : Nat) (x : List UInt8) (R : Run DState) : Prop where
  running : R.status.stopped = false → fixedCost ≤ limit ∧
    MemD (winSem.first (bits x)) ((demandSem.first (bits x)).getD 0) (roomOf limit) R.state.val (R.state.val.held ++ bits (x.drop R.read))
  stopped : R.status.stopped = true → R.state.val = deadD
  why : R.status = .memoryLimit → limit < demand x
  fine : R.status ≠ .memoryLimit → fixedCost ≤ limit

/-- A state with no window, no header's reading and no fast header holds no more than the fixed cost. -/
private theorem holds_small {D : Dec} (c1 : D.cmd.ring.size = 0) (c3 : D.cmd.wordBuf.size = 0)
    (h1 : D.hd = Hd.none) (h2 : D.H = Hdr.none) : D.holds ≤ fixedCost := by
  unfold Dec.holds fixedCost fieldBytes
  rw [h1, h2, hdNone_holds, hdrNone_holds]
  omega

/-- A state with nothing in it holds no more than the fixed cost. -/
theorem deadD_holds : deadD.holds ≤ fixedCost :=
  holds_small rfl rfl rfl rfl

/-- A state at a stream's start. -/
theorem liveD_mem (limit : Nat) (x : List UInt8) :
    MemD (winSem.first (bits x)) ((demandSem.first (bits x)).getD 0) (roomOf limit) (liveD limit) (bits x) := by
  refine ⟨⟨.wbits, liveD_rel limit, Nat.le_refl _⟩, fun e => DTag.noConfusion e, fun e => DTag.noConfusion e, fun e => DTag.noConfusion e, fun _ => rfl, fun _ => rfl,
    hsize_none, hsmall_none, Or.inl ⟨rfl, rfl, ?_, .wbits, liveD_rel limit, rfl⟩⟩
  show (UInt64.ofNat (min (limit - fixedCost) 4294958151)).toNat = _
  rw [u64_ofNat (by omega)]
  rfl

/-- The reply to a call the caller may make, for what a state holds. -/
private theorem reply_mem {Ws : Option Nat} {X L : Nat} {x : List UInt8} {R : Run DState} {c : Call} (ha : R.Allowed x c)
    (M : MemD Ws X L R.state.val (R.state.val.held ++ bits (x.drop R.read))) :
    ∃ o : Out, (R.reply decoder x c).state.val = o.D ∧ (R.reply decoder x c).used = o.pos.toNat - c.pre.length ∧ (R.reply decoder x c).status = o.status ∧
      o.pos.toNat ≤ c.pre.length + c.size ∧ c.pre.length ≤ o.pos.toNat ∧
      CallMem Ws X L (R.input x c) (USize.ofNat (c.pre.length + c.size)) (x.drop (R.read + c.size)) o := by
  have hin := ha.inside
  have hfit := ha.fits
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hinv := atPos_inv (start := c.pre.length) R.state hg.2.1 hg.2.2
  obtain ⟨p, hrel, hw⟩ := M.place
  have hok := callD_ok (hs := hs) (final := c.final) c.space _ hinv p _ c.buf.toByteArray (atPos_rel hrel _) rfl
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
  have hpos1 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := hpos0
  have h1 := hok.posLe
  have h2 := hok.posStop
  rw [hpos0] at h1
  rw [hstop] at h2
  have hb0 : (atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
      R.state.val.held ++ bits (x.drop R.read) := by
    have := bits_at (R := R) (c := c) hin (atPos R.state.val c.pre.length) hpos1 (Nat.zero_le _) hstop
    rw [this]
    rfl
  have M0 : MemD Ws X L (atPos R.state.val c.pre.length)
      ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size)))) :=
    M.move hb0 ⟨p, atPos_rel hrel _, by rw [hb0]; exact hw⟩ (fun q h => atPos_rel h _) rfl rfl rfl rfl rfl rfl rfl
  refine ⟨callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length) hinv c.buf.toByteArray c.space, ?_, ?_, ?_, h2, h1, callD_mem _ _ _ _ M0⟩
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

/-- The limit, from why it was reached. -/
private theorem limit_why {limit : Nat} {x : List UInt8} (hl : fixedCost ≤ limit) (h : MemWhy (winSem.first (bits x)) ((demandSem.first (bits x)).getD 0) (roomOf limit)) :
    limit < demand x := by
  obtain ⟨h1, h2⟩ := h
  rw [window_eq] at h1
  unfold demand
  unfold roomOf at h1 h2
  omega

/-- Every run of the decoder holds the invariant. -/
theorem mem_top {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) : MemTop limit x R := by
  induction h with
  | start =>
    show MemTop limit x { state := (decStart limit).1, status := (decStart limit).2, read := 0, offered := 0, emitted := [], ended := false }
    by_cases hl : limit < fixedCost
    · have e : decStart limit = (⟨deadD, _, deadD_rel⟩, .memoryLimit) := by
        unfold decStart
        rw [ite_eq_left hl]
      rw [e]
      exact ⟨fun hs => Bool.noConfusion hs, fun _ => rfl, fun _ => by unfold demand; omega, fun hs => absurd rfl hs⟩
    · have e : decStart limit = (⟨liveD limit, _, liveD_rel limit⟩, .needsInput) := by
        unfold decStart
        rw [ite_eq_right hl]
      rw [e]
      exact ⟨fun _ => ⟨Nat.le_of_not_lt hl, liveD_mem limit x⟩, fun hs => Bool.noConfusion hs, fun hs => Status.noConfusion hs, fun _ => Nat.le_of_not_lt hl⟩
  | @call R c hR ha ih =>
    obtain ⟨hlim, M⟩ := ih.running ha.running
    obtain ⟨o, e1, e2, e4, h1, h2, hC⟩ := reply_mem ha M
    have hin := ha.inside
    have hfit := ha.fits
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hq : o.pos.toNat = c.pre.length + (o.pos.toNat - c.pre.length) := by omega
    have hbn : o.D.bits (R.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
        o.D.held ++ bits (x.drop (R.read + (o.pos.toNat - c.pre.length))) := bits_at hin o.D hq (by omega) hstop
    have hstate : (R.after decoder x c).state.val = o.D := e1
    have hstatus : (R.after decoder x c).status = o.status := e4
    have hread : (R.after decoder x c).read = R.read + (o.pos.toNat - c.pre.length) := by
      show R.read + (R.reply decoder x c).used = _
      rw [e2]
    refine ⟨fun hs => ⟨hlim, ?_⟩, fun hs => ?_, fun hs => ?_, fun _ => hlim⟩
    · rw [hstatus] at hs
      rw [hstate, hread, ← hbn]
      exact hC.running hs
    · rw [hstatus] at hs
      rw [hstate]
      exact hC.stopped hs
    · rw [hstatus] at hs
      exact limit_why hlim (hC.why hs)

/-- The invariant, for the input a run has been offered. -/
private theorem mem_offered {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) : MemTop limit (x.take R.offered) R := by
  cases he : R.ended with
  | false =>
    have h' := h.continuation he (Nat.le_refl _) []
    rw [List.append_nil] at h'
    exact mem_top h'
  | true =>
    rw [h.offered_ended he, List.take_length]
    exact mem_top h

/-- Memory usage correctness: what the state holds stays within what the stream so far demands, and within the limit unless the limit was reported, which happens only
when the demand exceeds it. What a state holds is `Dec.holds`, with `fixedCost` in the demand; the decoder's constant
arrays (`constArrays_size`) are the program's and are not counted. -/
theorem decoder_streams : Streams decoder (fun s => s.val.holds) demand where
  within_demand {limit x R} h := by
    have hT := mem_offered h
    show R.state.val.holds ≤ _
    cases hs : R.status.stopped with
    | true =>
      rw [hT.stopped hs]
      have := deadD_holds
      unfold demand
      omega
    | false =>
      have := (hT.running hs).2.holds_le.1
      rw [window_eq] at this
      unfold demand
      omega
  within_limit {limit x R} h hn := by
    have hT := mem_top h
    show R.state.val.holds ≤ _
    cases hs : R.status.stopped with
    | true =>
      rw [hT.stopped hs]
      have := deadD_holds
      have := hT.fine hn
      omega
    | false =>
      obtain ⟨hl, M⟩ := hT.running hs
      have := M.holds_le.2
      unfold roomOf at this
      omega
  honest_limit h hs := (mem_offered h).why hs
  honest_stream h hs := (mem_top h).why hs

/-- What the state holds stays within the window the stream declares plus a constant: the fixed cost, the ring's 16 bytes
beyond the window, and the most a header reserves for its groups' tables. The decoder's constant arrays
(`constArrays_size`) are not counted. -/
theorem decoder_ceiling : DemandCeiling demand (fixedCost + 16 + resMax) := demand_ceiling

/-! ### The limit changes nothing but whether the decoder stops -/

/-- A call from two states that differ only in their limit and table room: one of them reports the limit, or the two reply
alike. -/
private theorem decStep_lim {s1 s2 : DState} {l a : UInt64} (hs : s1.val = decSet s2.val l a) (ar : ByteArray) (start stop : Nat)
    (buf : ByteArray) (space : Nat) (final : Bool) :
    (decStep s1 ar start stop buf space final).status = .memoryLimit ∨ (decStep s2 ar start stop buf space final).status = .memoryLimit ∨
      ((decStep s1 ar start stop buf space final).status = (decStep s2 ar start stop buf space final).status ∧
        (decStep s1 ar start stop buf space final).used = (decStep s2 ar start stop buf space final).used ∧
        (decStep s1 ar start stop buf space final).output = (decStep s2 ar start stop buf space final).output ∧
        ∃ l a, (decStep s1 ar start stop buf space final).state.val = decSet (decStep s2 ar start stop buf space final).state.val l a) := by
  unfold decStep
  split
  · rename_i h
    have := callD_lim ar (USize.ofNat stop) (by rw [usize_of h.2.2]; exact h.1) final space (atPos s2.val start)
      (atPos_inv s2 h.2.1 h.2.2) (atPos s1.val start) (atPos_inv s1 h.2.1 h.2.2) buf ⟨l, a, by rw [hs]; rfl⟩
    rcases this with h1 | h1 | ⟨e1, e2, e3, l', a', e4⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr ⟨e1, by dsimp only; rw [e3], e2, l', a', e4⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl, rfl, 0, 0, rfl⟩)

/-- What two runs with the same calls hold, from two limits. -/
private theorem twin_inv {l1 l2 : Nat} {x : List UInt8} {R1 R2 : Run DState} (h : Twin decoder l1 l2 x R1 R2) :
    R1.status = .memoryLimit ∨ R2.status = .memoryLimit ∨
      (R1.status = R2.status ∧ R1.read = R2.read ∧ R1.emitted = R2.emitted ∧ ∃ l a, R1.state.val = decSet R2.state.val l a) := by
  induction h with
  | start =>
    show (decStart l1).2 = .memoryLimit ∨ (decStart l2).2 = .memoryLimit ∨
      ((decStart l1).2 = (decStart l2).2 ∧ 0 = 0 ∧ ([] : List UInt8) = [] ∧ ∃ l a, (decStart l1).1.val = decSet (decStart l2).1.val l a)
    unfold decStart
    by_cases h1 : l1 < fixedCost
    · exact Or.inl (by rw [ite_eq_left h1])
    · by_cases h2 : l2 < fixedCost
      · exact Or.inr (Or.inl (by rw [ite_eq_left h2]))
      · rw [ite_eq_right h1, ite_eq_right h2]
        exact Or.inr (Or.inr ⟨rfl, rfl, rfl, UInt64.ofNat (min (l1 - fixedCost) 4294958151), 0, rfl⟩)
  | @call R1 R2 c _ ha1 ha2 ih =>
    rcases ih with h | h | ⟨e1, e2, e3, l, a, e4⟩
    · have := ha1.running
      rw [h] at this
      cases this
    · have := ha2.running
      rw [h] at this
      cases this
    · have hin : R1.input x c = R2.input x c := by simp only [Run.input, e2]
      have hr := decStep_lim e4 (R2.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final
      have hrep1 : R1.reply decoder x c = decStep R1.state (R2.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final := by
        rw [← hin]; rfl
      have hrep2 : R2.reply decoder x c = decStep R2.state (R2.input x c) c.pre.length (c.pre.length + c.size) c.buf.toByteArray c.space c.final := rfl
      rcases hr with h | h | ⟨f1, f2, f3, l', a', f4⟩
      · exact Or.inl (by show (R1.reply decoder x c).status = _; rw [hrep1]; exact h)
      · exact Or.inr (Or.inl (by show (R2.reply decoder x c).status = _; rw [hrep2]; exact h))
      · refine Or.inr (Or.inr ⟨?_, ?_, ?_, l', a', ?_⟩)
        · show (R1.reply decoder x c).status = (R2.reply decoder x c).status
          rw [hrep1, hrep2, f1]
        · show R1.read + (R1.reply decoder x c).used = R2.read + (R2.reply decoder x c).used
          rw [hrep1, hrep2, f2, e2]
        · show R1.emitted ++ (R1.reply decoder x c).output.data.toList.drop c.buf.length =
            R2.emitted ++ (R2.reply decoder x c).output.data.toList.drop c.buf.length
          rw [hrep1, hrep2, f3, e3]
        · show (R1.reply decoder x c).state.val = decSet (R2.reply decoder x c).state.val l' a'
          rw [hrep1, hrep2]
          exact f4

/-- Memory usage correctness, its limit part: the limit changes nothing but whether the decoder stops. -/
theorem decoder_limitBlind : LimitBlind decoder := by
  intro l1 l2 x R1 R2 h hn1 hn2
  rcases twin_inv h with h1 | h2 | ⟨e1, e2, e3, _⟩
  · exact absurd h1 hn1
  · exact absurd h2 hn2
  · exact ⟨e1, e2, e3⟩

/-- With a limit that covers the stream's demand, every caller that answers the signals gets exactly `decode`'s output. -/
theorem decoder_succeeds {limit : Nat} {x y : List UInt8} (hv : decode x = some y) (hl : demand x ≤ limit)
    {k : Caller DState} (hk : k.Answering decoder limit x) :
    ∃ n, (Run.follow decoder x k n (Run.initial decoder limit)).status = .done ∧
      (Run.follow decoder x k n (Run.initial decoder limit)).emitted = y :=
  caller_succeeds decoder_correct decoder_terminates decoder_streams hv hl hk

end Brotli.Decoder
