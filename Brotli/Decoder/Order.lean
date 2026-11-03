import Brotli.Decoder.Rest

/-!
# The spec's reading, in order

The spec read one field at a time, in the order it reads them, from each place `rest` names. A step reads a field from a
place and gives the next place with the bits after the field, the end of what the layer reads, a rejection, or too few
bits. A read that fails on fewer bits than the most it can take has too few bits; one that fails on that many or more is a
rejection. So a stream's reading in order has decided nothing at a place where it has too few bits, and every read is at
most a fixed number of bits, so the decision comes at most that many bits after the field's first one.

The streaming goals are stated with it: the decoder pauses for input only where the reading in order has too few bits,
and what it has produced is what the reading in order has.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- A step of the reading in order, from a place of type `P`, in a layer whose reading ends with an `E`. -/
inductive ORes (P E : Type) where
  | next (p : P) (bs : List Bool)
  | exit (e : E) (bs : List Bool)
  | bad
  | short

section
variable {A P E : Type}

/-- A read, in order: if it finishes, `k` of its value and the bits after it; if it fails, too few bits when fewer than
`room` bits were there, and a rejection otherwise. -/
def readIn (room : Nat) (rd : List Bool → Option (A × List Bool)) (bs : List Bool) (k : A → List Bool → ORes P E) : ORes P E :=
  match rd bs with
  | some (v, b) => k v b
  | none => if bs.length < room then .short else .bad

/-- A value looked up, not read: if it isn't there, a rejection. -/
def lookIn (o : Option A) (k : A → ORes P E) : ORes P E :=
  match o with
  | some v => k v
  | none => .bad

theorem readIn_some {room : Nat} {rd : List Bool → Option (A × List Bool)} {bs : List Bool} {k : A → List Bool → ORes P E}
    {v : A} {b : List Bool} (h : rd bs = some (v, b)) : readIn room rd bs k = k v b := by
  unfold readIn
  rw [h]

theorem readIn_short {room : Nat} {rd : List Bool → Option (A × List Bool)} {bs : List Bool} {k : A → List Bool → ORes P E}
    (h : rd bs = none) (hl : bs.length < room) : readIn room rd bs k = .short := by
  unfold readIn
  rw [h]
  exact ite_eq_left hl

theorem lookIn_some {o : Option A} {k : A → ORes P E} {v : A} (h : o = some v) : lookIn o k = k v := by
  unfold lookIn
  rw [h]

/-- The places the reading in order reaches from a place, with the bits left there. -/
inductive Reach (step : P → List Bool → ORes P E) : P → List Bool → P → List Bool → Prop
  | refl (p : P) (bs : List Bool) : Reach step p bs p bs
  | next {p : P} {bs : List Bool} {p' : P} {bs' : List Bool} {q : P} {c : List Bool} :
      step p bs = .next p' bs' → Reach step p' bs' q c → Reach step p bs q c

variable {step : P → List Bool → ORes P E}

theorem Reach.trans {p q r : P} {a b c : List Bool} (h1 : Reach step p a q b) (h2 : Reach step q b r c) :
    Reach step p a r c := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem Reach.one {p p' : P} {bs bs' : List Bool} (h : step p bs = .next p' bs') : Reach step p bs p' bs' :=
  .next h (.refl _ _)

/-- The reading in order goes one way: of two places it reaches from the same place, one reaches the other. -/
theorem Reach.total {p q r : P} {a b c : List Bool} (h1 : Reach step p a q b) (h2 : Reach step p a r c) :
    Reach step q b r c ∨ Reach step r c q b := by
  induction h1 generalizing r c with
  | refl => exact Or.inl h2
  | next hs _ ih =>
    cases h2 with
    | refl => exact Or.inr (.next hs ‹_›)
    | next hs' h2' =>
      rw [hs] at hs'
      cases hs'
      exact ih h2'

/-- A place where the reading stops reaches nothing further. -/
theorem Reach.stuck {p q : P} {a b : List Bool} (h : Reach step p a q b) (hs : ∀ p' a', step p a ≠ .next p' a') :
    q = p ∧ b = a := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | next h1 _ => exact absurd h1 (hs _ _)

theorem Reach.ofEq {p : P} {a a' : List Bool} (h : a' = a) : Reach step p a p a' := by
  subst h
  exact .refl _ _

end

/-! ### A meta-block's commands -/

/-- An insert-and-copy element's symbol and insert extra bits: the symbol, the insert length, and the copy length's
extra bits and base. -/
def readInsertHalf (code : PrefixCode) (bs : List Bool) : Option ((Nat × Nat × Nat × Nat) × List Bool) := do
  let (c, bs) ← decodeSymbol code bs
  let (insertCode, copyCode) ← insertCopyCodes c
  let (insertBits, insertBase, _) ← insertLengthCodes[insertCode]?
  let (copyBits, copyBase, _) ← copyLengthCodes[copyCode]?
  let (insertExtra, bs) ← readInt insertBits bs
  some ((c, insertBase + insertExtra, copyBits, copyBase), bs)

/-- A distance's symbol and extra bits. -/
def readDistanceParts (npostfix ndirect : Nat) (code : PrefixCode) (bs : List Bool) : Option ((Nat × Nat) × List Bool) := do
  let (dcode, bs) ← decodeSymbol code bs
  let (e, bs) ← readInt (distanceExtraBits npostfix ndirect dcode) bs
  some ((dcode, e), bs)

/-- An element's block switch, read in order: with the count not zero there is none, with one block type the switch is
a rejection, and otherwise it is read. -/
def nextIn {P E : Type} (c : BlockCategory) (st : BlockState) (bs : List Bool) (k : BlockState → List Bool → ORes P E) : ORes P E :=
  if st.count = 0 ∧ c.n < 2 then .bad else readIn 54 (nextElement c st) bs k

/-- A step of a meta-block's commands read in order, from each place `rest` names, with `w` the window size and `m`
the meta-block's header. A command's start at MLEN ends the commands. An insert length past MLEN is a rejection
before the copy extra bits, which can't change it. A literal's block switch is a step of its own,
which leaves the new block's count with its first literal still to come. A block switch is at most 54 bits, a symbol 15,
and a symbol with its extra bits 39. -/
def cStep (w : Nat) (m : MetaBlockHeader) : Phase → List Bool → ORes Phase CommandState
  | .command s, bs =>
    if s.remaining = 0 then .exit s bs
    else nextIn m.insertCopy s.insertCopy bs fun ic b => .next (.insertCopy s ic) b
  | .insertCopy s ic, bs =>
    lookIn m.insertCopyCodes[ic.types.cur]? fun code =>
    readIn 39 (readInsertHalf code) bs fun v b => .next (.copyLength s ic v.1 v.2.1 v.2.2.1 v.2.2.2) b
  | .copyLength s ic c ilen copyBits copyBase, bs =>
    if s.remaining < ilen then .bad
    else readIn 24 (readInt copyBits) bs fun e b => .next (.literals s ic c ilen (copyBase + e) ilen s.literal s.output) b
  | .literals s ic c ilen clen 0 lit out, bs => .next (.distance (withLiterals s ic lit out ilen) c clen) bs
  | .literals s ic c ilen clen (n + 1) lit out, bs =>
    if lit.count = 0 then
      nextIn m.literal lit bs fun lit b => .next (.literals s ic c ilen clen (n + 1) { lit with count := lit.count + 1 } out) b
    else .next (.literalSymbol s ic c ilen clen n { lit with count := lit.count - 1 } out) bs
  | .literalSymbol s ic c ilen clen n lit out, bs =>
    lookIn m.contextModes[lit.types.cur]? fun mode =>
    lookIn (literalPrefixCodeIndex m.literalMap lit.types.cur (contextId mode (contextBytes out).1 (contextBytes out).2))
      fun index =>
    lookIn m.literalCodes[index]? fun code =>
    readIn 15 (decodeSymbol code) bs fun byte b => .next (.literals s ic c ilen clen n lit (byte :: out)) b
  | .distance s c clen, bs =>
    if s.remaining = 0 then .next (.command s) bs
    else if implicitZeroDistance c then
      lookIn (distanceOf m.npostfix m.ndirect s.distances 0 0) fun d =>
      lookIn (copyPhase w s clen 0 d) fun q => .next q bs
    else nextIn m.distance s.distance bs fun dist b => .next (.distanceSymbol s clen dist) b
  | .distanceSymbol s clen dist, bs =>
    lookIn (distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen)) fun index =>
    lookIn m.distanceCodes[index]? fun code =>
    readIn 39 (readDistanceParts m.npostfix m.ndirect code) bs fun v b =>
    lookIn (distanceOf m.npostfix m.ndirect s.distances v.1 v.2) fun d =>
    lookIn (copyPhase w { s with distance := dist } clen v.1 d) fun q => .next q b
  | .copy s _ 0, bs => .next (.command s) bs
  | .copy s d (n + 1), bs => .next (.copy { s with output := s.output.getD (d - 1) 0 :: s.output } d n) bs
  | .word s [], bs => .next (.command s) bs
  | .word s (b :: pending), bs => .next (.word { s with output := b :: s.output } pending) bs

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

/-- From a place with its bits, the reading in order comes, producing nothing more, to a place where it has too few
bits. -/
def CShort (w : Nat) (m : MetaBlockHeader) (p : Phase) (bs : List Bool) : Prop :=
  ∃ q c, Reach (cStep w m) p bs q c ∧ cStep w m q c = .short ∧ q.out = p.out

theorem CShort.here {w : Nat} {m : MetaBlockHeader} {p : Phase} {bs : List Bool} (h : cStep w m p bs = .short) : CShort w m p bs :=
  ⟨p, bs, .refl _ _, h, rfl⟩

theorem nextIn_some {P E : Type} {c : BlockCategory} {st : BlockState} {bs : List Bool} {k : BlockState → List Bool → ORes P E}
    {v : BlockState} {b : List Bool} (h0 : ¬ (st.count = 0 ∧ c.n < 2)) (h : nextElement c st bs = some (v, b)) : nextIn c st bs k = k v b := by
  unfold nextIn
  rw [ite_eq_right h0, readIn_some h]

theorem nextIn_short {P E : Type} {c : BlockCategory} {st : BlockState} {bs : List Bool} {k : BlockState → List Bool → ORes P E}
    (h0 : ¬ (st.count = 0 ∧ c.n < 2)) (h : nextElement c st bs = none) (hl : bs.length < 54) : nextIn c st bs k = .short := by
  unfold nextIn
  rw [ite_eq_right h0, readIn_short h hl]

theorem cStep_command {w : Nat} {m : MetaBlockHeader} {s : CommandState} (bs : List Bool) (h0 : s.remaining ≠ 0) :
    cStep w m (.command s) bs = nextIn m.insertCopy s.insertCopy bs fun ic b => .next (.insertCopy s ic) b := by
  show (if s.remaining = 0 then _ else _) = _
  rw [ite_eq_right h0]

theorem cStep_distance_end {w : Nat} {m : MetaBlockHeader} {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining = 0) :
    cStep w m (.distance s c clen) bs = .next (.command s) bs := by
  show (if s.remaining = 0 then _ else _) = _
  rw [ite_eq_left h0]

theorem cStep_distance_implicit {w : Nat} {m : MetaBlockHeader} {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining ≠ 0)
    (hc : implicitZeroDistance c = true) :
    cStep w m (.distance s c clen) bs =
      lookIn (distanceOf m.npostfix m.ndirect s.distances 0 0) fun d => lookIn (copyPhase w s clen 0 d) fun q => .next q bs := by
  show (if s.remaining = 0 then _ else _) = _
  rw [ite_eq_right h0]
  show (if implicitZeroDistance c = true then _ else _) = _
  rw [ite_eq_left hc]

theorem cStep_distance_switch {w : Nat} {m : MetaBlockHeader} {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining ≠ 0)
    (hc : implicitZeroDistance c = false) :
    cStep w m (.distance s c clen) bs =
      nextIn m.distance s.distance bs fun dist b => .next (.distanceSymbol s clen dist) b := by
  show (if s.remaining = 0 then _ else _) = _
  rw [ite_eq_right h0]
  show (if implicitZeroDistance c = true then _ else _) = _
  rw [ite_eq_right (by rw [hc]; decide)]

/-- A backward copy, `j` bytes at a time. -/
theorem cReach_copy (w : Nat) (m : MetaBlockHeader) (d : Nat) (bs : List Bool) :
    ∀ (j n : Nat) (s : CommandState), j ≤ n →
      Reach (cStep w m) (.copy s d n) bs (.copy { s with output := copyBytes d j s.output } d (n - j)) bs
  | 0, n, s, _ => by
    simp only [copyBytes, Nat.sub_zero]
    exact .refl _ _
  | j + 1, n + 1, s, h => by
    refine .next rfl ?_
    have := cReach_copy w m d bs j n { s with output := s.output.getD (d - 1) 0 :: s.output } (by omega)
    simpa [copyBytes] using this
  | _ + 1, 0, _, h => by omega

/-- A dictionary word, a part at a time. -/
theorem cReach_word (w : Nat) (m : MetaBlockHeader) (bs : List Bool) :
    ∀ (j : Nat) (s : CommandState) (pending : List Nat),
      Reach (cStep w m) (.word s pending) bs
        (.word { s with output := (pending.take j).reverse ++ s.output } (pending.drop j)) bs
  | 0, s, pending => by
    simp only [List.take_zero, List.reverse_nil, List.nil_append, List.drop_zero]
    exact .refl _ _
  | j + 1, s, [] => by
    simp only [List.take_nil, List.reverse_nil, List.nil_append, List.drop_nil]
    exact .refl _ _
  | j + 1, s, b :: pending => by
    refine .next rfl ?_
    have := cReach_word w m bs j { s with output := b :: s.output } pending
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using this

end Brotli.Decoder
