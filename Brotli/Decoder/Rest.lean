import Brotli.Spec.Stream

/-!
# What the spec still has to do

The bridge's `rest` for a meta-block's commands: for each place the decoder can pause, what the spec still has to
do from there, written with the spec's own readers. It computes nothing of its own. Each equation below takes one
small read from one place to the next.

`rest` takes what follows a finished command as a parameter `K`, so fuel appears only in `commandsFrom`.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Lexicographically lower. -/
def LexLt (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- Lexicographically lower, on two pairs. -/
def Lex4 (a b : (Nat × Nat) × (Nat × Nat)) : Prop := LexLt a.1 b.1 ∨ (a.1 = b.1 ∧ LexLt a.2 b.2)

/-! ### The commands without fuel -/

private theorem readCommandsWith_fuel (w : Nat) (h : MetaBlockHeader) : ∀ (f f' : Nat) (s : CommandState)
    (bs : List Bool), commandMeasure s bs < f → commandMeasure s bs < f' →
    readCommandsWith w h none f s bs = readCommandsWith w h none f' s bs
  | 0, _, _, _, hf, _ => by omega
  | _ + 1, 0, _, _, _, hf' => by omega
  | f + 1, f' + 1, s, bs, hf, hf' => by
    simp only [readCommandsWith]
    split
    · rfl
    · cases hc : readCommand w h s bs with
      | none => rfl
      | some p =>
        obtain ⟨s1, b1⟩ := p
        have := readCommand_measure hc
        exact readCommandsWith_fuel w h f f' s1 b1 (by omega) (by omega)

/-- A meta-block's commands, from a state, with fuel settled. -/
def commandsFrom (w : Nat) (h : MetaBlockHeader) (s : CommandState) (bs : List Bool) :
    Option (CommandState × List Bool) :=
  readCommands w h (commandMeasure s bs + 1) s bs

/-- The commands stop once MLEN is reached. -/
theorem commandsFrom_stop {w : Nat} {h : MetaBlockHeader} {s : CommandState} (bs : List Bool)
    (h0 : s.remaining = 0) : commandsFrom w h s bs = some (s, bs) := by
  have key : ∀ f, readCommands w h (f + 1) s bs = some (s, bs) := by
    intro f
    simp [readCommands, readCommandsWith, h0]
  exact key _

/-- Otherwise they read one command and go on. -/
theorem commandsFrom_step {w : Nat} {h : MetaBlockHeader} {s : CommandState} (bs : List Bool)
    (h0 : s.remaining ≠ 0) :
    commandsFrom w h s bs = readCommand w h s bs >>= fun (s1, b) => commandsFrom w h s1 b := by
  -- The fuel stays abstract here, because the kernel can't reduce `commandMeasure`'s multiplication.
  have key : ∀ F : CommandState → List Bool → Nat, (∀ s bs, commandMeasure s bs < F s bs) →
      readCommandsWith w h none (F s bs) s bs =
        readCommand w h s bs >>= fun (s1, b) => readCommandsWith w h none (F s1 b) s1 b := by
    intro F hF
    have hlt := hF s bs
    cases hf : F s bs with
    | zero => omega
    | succ f =>
      simp only [readCommandsWith, h0, ↓reduceIte]
      cases hc : readCommand w h s bs with
      | none => rfl
      | some p =>
        obtain ⟨s1, b1⟩ := p
        have hm := readCommand_measure hc
        exact readCommandsWith_fuel w h f _ s1 b1 (by omega) (hF s1 b1)
  exact key (fun s bs => commandMeasure s bs + 1) (fun _ _ => Nat.lt_succ_self _)

private theorem readMetaBlocksWith_fuel (w : Nat) : ∀ (f f' : Nat) (st : StreamState) (bs : List Bool),
    bs.length < f → bs.length < f' →
    readMetaBlocksWith w none f st bs = readMetaBlocksWith w none f' st bs
  | 0, _, _, _, hf, _ => by omega
  | _ + 1, 0, _, _, _, hf' => by omega
  | f + 1, f' + 1, st, bs, hf, hf' => by
    simp only [readMetaBlocksWith]
    cases hm : readMetaBlock w st bs with
    | none => rfl
    | some p =>
      obtain ⟨⟨st1, islast⟩, b1⟩ := p
      have := readMetaBlock_lt hm
      dsimp only [bind, Option.bind]
      split
      · rfl
      · exact readMetaBlocksWith_fuel w f f' st1 b1 (by omega) (by omega)

/-- The meta-blocks, from a state, with fuel settled. -/
def metaBlocksFrom (w : Nat) (st : StreamState) (bs : List Bool) : Option (StreamState × List Bool) :=
  readMetaBlocks w (bs.length + 1) st bs

/-- One meta-block, then the others unless it was the last. -/
theorem metaBlocksFrom_step (w : Nat) (st : StreamState) (bs : List Bool) :
    metaBlocksFrom w st bs = readMetaBlock w st bs >>= fun ((st1, islast), b) =>
      if islast then some (st1, b) else metaBlocksFrom w st1 b := by
  have key : ∀ f, bs.length ≤ f → readMetaBlocksWith w none (f + 1) st bs =
      readMetaBlock w st bs >>= fun ((st1, islast), b) =>
        if islast then some (st1, b) else metaBlocksFrom w st1 b := by
    intro f hf
    simp only [readMetaBlocksWith]
    cases hm : readMetaBlock w st bs with
    | none => rfl
    | some p =>
      obtain ⟨⟨st1, islast⟩, b1⟩ := p
      have := readMetaBlock_lt hm
      dsimp only [bind, Option.bind]
      split
      · rfl
      · exact readMetaBlocksWith_fuel w f _ st1 b1 (by omega) (Nat.lt_succ_self _)
  exact key _ (Nat.le_refl _)

/-- `decode`, with fuel settled. -/
theorem decode_eq (input : List UInt8) :
    decode input = readWBITS (bits input) >>= fun (wbits, bs) =>
      metaBlocksFrom (windowSize wbits) ⟨[], 0, initialDistances⟩ bs >>= fun (st, bs) =>
      readEnd bs >>= fun _ => some (st.output.reverse.map Nat.toUInt8) :=
  rfl

/-! ### The places to pause -/

/-- The state once a command's literals are done. -/
def withLiterals (s : CommandState) (ic lit : BlockState) (out : List Nat) (ilen : Nat) : CommandState :=
  { s with
    insertCopy := ic, literal := lit, output := out
    produced := s.produced + ilen
    remaining := s.remaining - ilen }

/-- The places a meta-block's commands can pause. -/
inductive Phase where
  /-- At the start of a command. -/
  | command (s : CommandState)
  /-- The insert-and-copy element's block switch is done; its symbol and extra bits are next. -/
  | insertCopy (s : CommandState) (ic : BlockState)
  /-- The element's symbol and insert extra bits are read; its copy extra bits are next. -/
  | copyLength (s : CommandState) (ic : BlockState) (c ilen copyBits copyBase : Nat)
  /-- In the literals, with `n` left. -/
  | literals (s : CommandState) (ic : BlockState) (c ilen clen n : Nat) (lit : BlockState) (out : List Nat)
  /-- A literal's block switch is done; its symbol is next, with `n` more after it. -/
  | literalSymbol (s : CommandState) (ic : BlockState) (c ilen clen n : Nat) (lit : BlockState) (out : List Nat)
  /-- The literals are done and the distance is next. -/
  | distance (s : CommandState) (c clen : Nat)
  /-- The distance's block switch is done; its symbol and extra bits are next. -/
  | distanceSymbol (s : CommandState) (clen : Nat) (dist : BlockState)
  /-- In a backward copy, with `n` bytes left, which `s.output` has yet to take. -/
  | copy (s : CommandState) (d n : Nat)
  /-- In a dictionary word, with `pending` left, which `s.output` has yet to take. -/
  | word (s : CommandState) (pending : List Nat)

variable {α : Type}

/-- What the spec does after a command's literals, with `K` what follows the command. -/
def afterLiterals (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (c clen : Nat) (bs : List Bool) : Option α :=
  if s.remaining = 0 then K s bs
  else
    readCommandDistance h s.distance s.distances c clen bs >>= fun ((distance, dcode, d), bs) =>
    copyCommand w { s with distance } clen dcode d >>= fun s => K s bs

/-- `rest`: what the spec still has to do from each place, with `K` what follows the command. -/
def rest (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α) :
    Phase → List Bool → Option α
  | .command s, bs => K s bs
  | .insertCopy s ic, bs =>
    h.insertCopyCodes[ic.types.cur]? >>= fun code =>
    readInsertCopy code bs >>= fun ((c, ilen, clen), bs) =>
    if s.remaining < ilen then none
    else
      readLiterals h ilen s.literal s.output bs >>= fun (lit, out, bs) =>
      afterLiterals w h K (withLiterals s ic lit out ilen) c clen bs
  | .copyLength s ic c ilen copyBits copyBase, bs =>
    readInt copyBits bs >>= fun (copyExtra, bs) =>
    if s.remaining < ilen then none
    else
      readLiterals h ilen s.literal s.output bs >>= fun (lit, out, bs) =>
      afterLiterals w h K (withLiterals s ic lit out ilen) c (copyBase + copyExtra) bs
  | .literals s ic c ilen clen n lit out, bs =>
    readLiterals h n lit out bs >>= fun (lit, out, bs) =>
    afterLiterals w h K (withLiterals s ic lit out ilen) c clen bs
  | .literalSymbol s ic c ilen clen n lit out, bs =>
    h.contextModes[lit.types.cur]? >>= fun mode =>
    literalPrefixCodeIndex h.literalMap lit.types.cur
      (contextId mode (contextBytes out).1 (contextBytes out).2) >>= fun index =>
    h.literalCodes[index]? >>= fun code =>
    decodeSymbol code bs >>= fun (byte, bs) =>
    readLiterals h n lit (byte :: out) bs >>= fun (lit, out, bs) =>
    afterLiterals w h K (withLiterals s ic lit out ilen) c clen bs
  | .distance s c clen, bs => afterLiterals w h K s c clen bs
  | .distanceSymbol s clen dist, bs =>
    distancePrefixCodeIndex h.distanceMap dist.types.cur (distanceContextId clen) >>= fun index =>
    h.distanceCodes[index]? >>= fun code =>
    readDistance h.npostfix h.ndirect code s.distances bs >>= fun ((dcode, d), bs) =>
    copyCommand w { s with distance := dist } clen dcode d >>= fun s => K s bs
  | .copy s d n, bs => K { s with output := copyBytes d n s.output } bs
  | .word s pending, bs => K { s with output := pending.reverse ++ s.output } bs

/-! ### One small read at a time -/

/-- A command is the insert-and-copy element's block switch, then the rest from there. -/
theorem readCommand_rest (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (bs : List Bool) :
    (readCommand w h s bs >>= fun (s1, b) => K s1 b) =
      (nextElement h.insertCopy s.insertCopy bs >>= fun (ic, b) => rest w h K (.insertCopy s ic) b) := by
  unfold readCommand
  simp only [rest, bind_assoc]
  congr 1
  funext ⟨ic, b1⟩
  dsimp only
  congr 1
  funext code
  congr 1
  funext ⟨⟨c, ilen, clen⟩, b2⟩
  dsimp only
  split
  · rfl
  · rw [bind_assoc]
    congr 1
    funext ⟨lit, out, b3⟩
    unfold afterLiterals withLiterals
    dsimp only
    split
    · rfl
    · simp only [bind_assoc]
      rfl

/-- After the block switch come the element's symbol and insert extra bits. They fit the bit buffer together, and
the copy extra bits may not fit with them. -/
theorem rest_insertCopy (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (ic : BlockState) (bs : List Bool) :
    rest w h K (.insertCopy s ic) bs =
      h.insertCopyCodes[ic.types.cur]? >>= fun code =>
      decodeSymbol code bs >>= fun (c, bs) =>
      insertCopyCodes c >>= fun (insertCode, copyCode) =>
      insertLengthCodes[insertCode]? >>= fun (insertBits, insertBase, _) =>
      copyLengthCodes[copyCode]? >>= fun (copyBits, copyBase, _) =>
      readInt insertBits bs >>= fun (insertExtra, bs) =>
      rest w h K (.copyLength s ic c (insertBase + insertExtra) copyBits copyBase) bs := by
  simp only [rest, readInsertCopy, bind_assoc]
  rfl

/-- The copy extra bits, which begin the literals. -/
theorem rest_copyLength (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (ic : BlockState) (c ilen copyBits copyBase : Nat) (bs : List Bool) :
    rest w h K (.copyLength s ic c ilen copyBits copyBase) bs =
      readInt copyBits bs >>= fun (copyExtra, bs) =>
      if s.remaining < ilen then none
      else rest w h K (.literals s ic c ilen (copyBase + copyExtra) ilen s.literal s.output) bs :=
  rfl

/-- One more literal starts with its block switch. -/
theorem rest_literal (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (ic : BlockState) (c ilen clen n : Nat) (lit : BlockState) (out : List Nat)
    (bs : List Bool) :
    rest w h K (.literals s ic c ilen clen (n + 1) lit out) bs =
      nextElement h.literal lit bs >>= fun (lit, bs) =>
      rest w h K (.literalSymbol s ic c ilen clen n lit out) bs := by
  simp only [rest, readLiterals, bind_assoc]

/-- A literal's symbol. -/
theorem rest_literalSymbol (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (ic : BlockState) (c ilen clen n : Nat) (lit : BlockState) (out : List Nat)
    (bs : List Bool) :
    rest w h K (.literalSymbol s ic c ilen clen n lit out) bs =
      h.contextModes[lit.types.cur]? >>= fun mode =>
      literalPrefixCodeIndex h.literalMap lit.types.cur
        (contextId mode (contextBytes out).1 (contextBytes out).2) >>= fun index =>
      h.literalCodes[index]? >>= fun code =>
      decodeSymbol code bs >>= fun (byte, bs) =>
      rest w h K (.literals s ic c ilen clen n lit (byte :: out)) bs :=
  rfl

/-- The literals done, with MLEN reached: the command ignores its copy. -/
theorem rest_literals_end {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {c ilen clen : Nat} {lit : BlockState} {out : List Nat} (bs : List Bool)
    (h0 : (withLiterals s ic lit out ilen).remaining = 0) :
    rest w h K (.literals s ic c ilen clen 0 lit out) bs = K (withLiterals s ic lit out ilen) bs := by
  show afterLiterals w h K (withLiterals s ic lit out ilen) c clen bs = _
  unfold afterLiterals
  rw [ite_eq_left h0]

/-- The literals done, with MLEN not reached: the distance is next. -/
theorem rest_literals_distance {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {ic : BlockState} {c ilen clen : Nat} {lit : BlockState} {out : List Nat} (bs : List Bool) :
    rest w h K (.literals s ic c ilen clen 0 lit out) bs =
      rest w h K (.distance (withLiterals s ic lit out ilen) c clen) bs :=
  rfl

/-- With MLEN not reached and an explicit distance, the distance's block switch is next. -/
theorem rest_distance_switch {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining ≠ 0) (hc : implicitZeroDistance c = false) :
    rest w h K (.distance s c clen) bs =
      nextElement h.distance s.distance bs >>= fun (dist, bs) =>
      rest w h K (.distanceSymbol s clen dist) bs := by
  simp only [rest, afterLiterals, h0, ↓reduceIte, readCommandDistance, hc, Bool.false_eq_true, bind_assoc]
  rfl

/-- What a command's copy becomes, once its distance is known: a backward copy, a dictionary word, or a
rejection. -/
def copyPhase (w : Nat) (s : CommandState) (clen dcode d : Nat) : Option Phase :=
  let maxDistance := maxBackwardDistance w s.produced
  let dictionary := isDictionaryReference d maxDistance
  let s := { s with distances := pushDistance s.distances dcode d dictionary }
  if dictionary then
    (dictionaryWord clen d maxDistance).bind fun word =>
      if s.remaining < word.length then none
      else some (.word { s with
        produced := s.produced + word.length
        remaining := s.remaining - word.length } word)
  else if s.remaining < clen then none
  else some (.copy { s with
    produced := s.produced + clen
    remaining := s.remaining - clen } d clen)

/-- A command's copy is the place `copyPhase` gives, then `rest` from there. -/
theorem copyCommand_phase (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (clen dcode d : Nat) (b : List Bool) :
    (copyCommand w s clen dcode d >>= fun s => K s b) =
      (copyPhase w s clen dcode d >>= fun p => rest w h K p b) := by
  unfold copyCommand copyPhase
  dsimp only
  by_cases hd : isDictionaryReference d (maxBackwardDistance w s.produced) = true
  · simp only [hd, ↓reduceIte]
    cases dictionaryWord clen d (maxBackwardDistance w s.produced) with
    | none => rfl
    | some word =>
      dsimp only [bind, Option.bind]
      by_cases hr : s.remaining < word.length
      · simp only [hr, ↓reduceIte]
      · simp only [hr, ↓reduceIte]
        rfl
  · simp only [hd, Bool.false_eq_true, ↓reduceIte]
    by_cases hr : s.remaining < clen
    · simp only [hr, ↓reduceIte]
      rfl
    · simp only [hr, ↓reduceIte]
      rfl

/-- The distance, then the copy it selects. -/
theorem rest_distance {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining ≠ 0) :
    rest w h K (.distance s c clen) bs =
      readCommandDistance h s.distance s.distances c clen bs >>= fun ((distance, dcode, d), bs) =>
      copyPhase w { s with distance } clen dcode d >>= fun p => rest w h K p bs := by
  simp only [rest, afterLiterals, h0, ↓reduceIte]
  congr 1
  funext ⟨⟨dst, dcode, d⟩, b⟩
  exact copyCommand_phase w h K _ clen dcode d b

/-- With MLEN reached, a command has no distance. -/
theorem rest_distance_end {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining = 0) :
    rest w h K (.distance s c clen) bs = rest w h K (.command s) bs := by
  simp only [rest, afterLiterals, h0, ↓reduceIte]

/-- With MLEN not reached and an implied distance symbol 0, there is nothing to read. -/
theorem rest_distance_implicit {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {c clen : Nat} (bs : List Bool) (h0 : s.remaining ≠ 0) (hc : implicitZeroDistance c = true) :
    rest w h K (.distance s c clen) bs =
      distanceOf h.npostfix h.ndirect s.distances 0 0 >>= fun d =>
      copyPhase w s clen 0 d >>= fun p => rest w h K p bs := by
  rw [rest_distance bs h0]
  unfold readCommandDistance
  rw [ite_eq_left hc]
  cases distanceOf h.npostfix h.ndirect s.distances 0 0 with
  | none => rfl
  | some d => rfl

/-- A distance's symbol and extra bits, once the symbol is read. -/
theorem rest_distanceSymbol {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {clen : Nat} {dist : BlockState} {tree dcode : Nat} {code : PrefixCode} {bs r : List Bool}
    (hindex : distancePrefixCodeIndex h.distanceMap dist.types.cur (distanceContextId clen) = some tree)
    (hcode : h.distanceCodes[tree]? = some code) (hd : decodeSymbol code bs = some (dcode, r)) :
    rest w h K (.distanceSymbol s clen dist) bs =
      readInt (distanceExtraBits h.npostfix h.ndirect dcode) r >>= fun (e, b) =>
      distanceOf h.npostfix h.ndirect s.distances dcode e >>= fun d =>
      copyPhase w { s with distance := dist } clen dcode d >>= fun p => rest w h K p b := by
  simp only [rest, hindex, bind, Option.bind, hcode, readDistance, hd]
  cases readInt (distanceExtraBits h.npostfix h.ndirect dcode) r with
  | none => rfl
  | some q =>
    obtain ⟨e, b⟩ := q
    dsimp only
    cases distanceOf h.npostfix h.ndirect s.distances dcode e with
    | none => rfl
    | some d => exact copyCommand_phase w h K _ clen dcode d b

/-- With nothing more than these bits, a distance's symbol can't be read. -/
theorem rest_distanceSymbol_none {w : Nat} {h : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {s : CommandState} {clen : Nat} {dist : BlockState} {tree : Nat} {code : PrefixCode} {bs : List Bool}
    (hindex : distancePrefixCodeIndex h.distanceMap dist.types.cur (distanceContextId clen) = some tree)
    (hcode : h.distanceCodes[tree]? = some code) (hd : decodeSymbol code bs = none) :
    rest w h K (.distanceSymbol s clen dist) bs = none := by
  simp only [rest, hindex, bind, Option.bind, hcode, readDistance, hd]

/-- `copyPhase` for a dictionary reference. -/
theorem copyPhase_word {w : Nat} {s : CommandState} {clen dcode d : Nat} (h : maxBackwardDistance w s.produced < d) :
    copyPhase w s clen dcode d = (dictionaryWord clen d (maxBackwardDistance w s.produced)).bind fun word =>
      if s.remaining < word.length then none
      else some (.word { s with
        produced := s.produced + word.length
        remaining := s.remaining - word.length } word) := by
  simp [copyPhase, isDictionaryReference, pushDistance, h]

/-- `copyPhase` for a backward copy. -/
theorem copyPhase_copy {w : Nat} {s : CommandState} {clen dcode d : Nat} (h : ¬ maxBackwardDistance w s.produced < d) :
    copyPhase w s clen dcode d =
      if s.remaining < clen then none
      else some (.copy { s with
        distances := pushDistance s.distances dcode d false
        produced := s.produced + clen
        remaining := s.remaining - clen } d clen) := by
  simp [copyPhase, isDictionaryReference, h]

/-- One byte of a backward copy. -/
theorem rest_copy (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (d n : Nat) (bs : List Bool) :
    rest w h K (.copy s d (n + 1)) bs =
      rest w h K (.copy { s with output := s.output.getD (d - 1) 0 :: s.output } d n) bs :=
  rfl

/-- A backward copy done: the next command. -/
theorem rest_copy_end (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (d : Nat) (bs : List Bool) : rest w h K (.copy s d 0) bs = rest w h K (.command s) bs :=
  rfl

/-- One byte of a dictionary word. -/
theorem rest_word (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (b : Nat) (pending : List Nat) (bs : List Bool) :
    rest w h K (.word s (b :: pending)) bs = rest w h K (.word { s with output := b :: s.output } pending) bs := by
  simp [rest]

/-- A dictionary word done: the next command. -/
theorem rest_word_end (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (bs : List Bool) : rest w h K (.word s []) bs = rest w h K (.command s) bs := by
  simp [rest]

/-! ### At the start of a command -/

/-- At the start of a command is what follows the last one. -/
theorem rest_command (w : Nat) (h : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (s : CommandState) (bs : List Bool) : rest w h K (.command s) bs = K s bs :=
  rfl

/-- `commandsFrom` stops at MLEN. -/
theorem rest_command_stop {w : Nat} {h : MetaBlockHeader} {s : CommandState} (bs : List Bool)
    (h0 : s.remaining = 0) : rest w h (commandsFrom w h) (.command s) bs = some (s, bs) := by
  rw [rest_command, commandsFrom_stop bs h0]

/-- Otherwise a command starts with the insert-and-copy element's block switch. -/
theorem rest_command_step {w : Nat} {h : MetaBlockHeader} {s : CommandState} (bs : List Bool)
    (h0 : s.remaining ≠ 0) :
    rest w h (commandsFrom w h) (.command s) bs =
      nextElement h.insertCopy s.insertCopy bs >>= fun (ic, b) =>
        rest w h (commandsFrom w h) (.insertCopy s ic) b := by
  rw [rest_command, commandsFrom_step bs h0, readCommand_rest]

/-! ### Pausing -/

/-- A symbol read from the bits at hand is final: more bits can't change it, whatever `rest` does next. -/
theorem commit_symbol {c : PrefixCode} {p r : List Bool} {sym : Nat} (hd : decodeSymbol c p = some (sym, r))
    (future : List Bool) : decodeSymbol c (p ++ future) = some (sym, r ++ future) :=
  decodeSymbol_ext future hd

end Brotli.Decoder
