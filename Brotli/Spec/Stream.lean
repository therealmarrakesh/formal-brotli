module

public import Brotli.Spec.PrefixCode
public import Brotli.Spec.Distance
public import Brotli.Spec.InsertCopy
public import Brotli.Spec.BlockSwitch
public import Brotli.Spec.Context
public import Brotli.Spec.Dictionary

@[expose] public section

/-!
# Compressed data format

RFC 7932 §9, with §2 and §10, and the entry point `decode`.
-/

namespace Brotli.Spec

/-! ### The stream header (§9.1) -/

/-- The code of WBITS: value, number of bits, pattern as printed, which is its bits read as an integer
(§9.1). -/
def wbitsCode : List (Nat × Nat × Nat) :=
  [(10, 7, 0b0100001), (11, 7, 0b0110001), (12, 7, 0b1000001), (13, 7, 0b1010001),
   (14, 7, 0b1100001), (15, 7, 0b1110001), (16, 1, 0b0), (17, 7, 0b0000001),
   (18, 4, 0b0011), (19, 4, 0b0101), (20, 4, 0b0111), (21, 4, 0b1001),
   (22, 4, 0b1011), (23, 4, 0b1101), (24, 4, 0b1111)]

/-- No code of `wbitsCode`, as read, begins with another. -/
theorem wbitsCode_prefixFree :
    ∀ e ∈ wbitsCode, ∀ f ∈ wbitsCode, e ≠ f → e.2.1 ≤ f.2.1 → f.2.2 % 2 ^ e.2.1 ≠ e.2.2 := by
  decide +kernel

/-- WBITS is in 10..24 (§9.1). -/
theorem wbitsCode_range : ∀ e ∈ wbitsCode, 10 ≤ e.1 ∧ e.1 ≤ 24 := by
  decide +kernel

/-- WBITS, the stream header's one field; the invalid pattern 0010001 has no row (§9.1). -/
def readWBITS (bs : List Bool) : Option (Nat × List Bool) :=
  wbitsCode.findSome? fun (wbits, n, printed) =>
    match readInt n bs with
    | some (v, rest) => if v = printed then some (wbits, rest) else none
    | none => none

/-- The window size (§9.1). -/
def windowSize (wbits : Nat) : Nat :=
  (1 <<< wbits) - 16

/-! ### The meta-block header (§9.2) -/

/-- The variable-length code of NBLTYPESL and the other counts (§9.2). -/
def readVarLen (bs : List Bool) : Option (Nat × List Bool) := do
  let (first, bs) ← readInt 1 bs
  if first = 0 then some (1, bs)
  else
    let (n, bs) ← readInt 3 bs
    if n = 0 then some (2, bs)
    else
      let (x, bs) ← readInt n bs
      some ((1 <<< n) + 1 + x, bs)

/-- The code's values are 1 to 256 (§9.2). -/
theorem readVarLen_range {bs r : List Bool} {v : Nat} (h : readVarLen bs = some (v, r)) :
    1 ≤ v ∧ v ≤ 256 := by
  unfold readVarLen at h
  cases h1 : readInt 1 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨first, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    cases h2 : readInt 3 bs1 with
    | none => rw [h2] at h; simp at h
    | some q =>
      obtain ⟨n, bs2⟩ := q
      rw [h2] at h
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        omega
      cases h3 : readInt n bs2 with
      | none => rw [h3] at h; simp at h
      | some t =>
        obtain ⟨x, bs3⟩ := t
        rw [h3] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hn : n < 8 := by simpa using readInt_lt 3 bs1 n bs2 h2
        have hx := readInt_lt n bs2 x bs3 h3
        have hpow : 2 ^ n ≤ 128 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show n ≤ 7 by omega)
          simpa using this
        rw [Nat.shiftLeft_eq, Nat.one_mul] at h
        omega

/-- MNIBBLES: 0, 4, 5 or 6 (§9.2). -/
def readMNIBBLES (bs : List Bool) : Option (Nat × List Bool) := do
  let (v, bs) ← readInt 2 bs
  some (if v = 3 then 0 else v + 4, bs)

/-- MLEN; with more than 4 nibbles, a last nibble of zero is invalid (§9.2). -/
def readMLEN (mnibbles : Nat) (bs : List Bool) : Option (Nat × List Bool) := do
  let (v, bs) ← readInt (mnibbles * 4) bs
  if 4 < mnibbles ∧ v >>> ((mnibbles - 1) * 4) = 0 then none else some (v + 1, bs)

/-- MLEN is 1 to 16,777,216, with at most 6 nibbles. -/
theorem readMLEN_range {mnibbles v : Nat} {bs r : List Bool} (hm : mnibbles ≤ 6)
    (h : readMLEN mnibbles bs = some (v, r)) : 1 ≤ v ∧ v ≤ 16777216 := by
  unfold readMLEN at h
  cases h1 : readInt (mnibbles * 4) bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨x, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      have hx := readInt_lt _ _ _ _ h1
      have hpow : 2 ^ (mnibbles * 4) ≤ 2 ^ 24 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have : (2 : Nat) ^ 24 = 16777216 := by decide
      omega

/-- `readMNIBBLES` gives at most 6 nibbles. -/
theorem readMNIBBLES_le {bs r : List Bool} {m : Nat} (h : readMNIBBLES bs = some (m, r)) : m ≤ 6 := by
  unfold readMNIBBLES at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨v, bs1⟩ := p
    rw [h1] at h
    simp only [bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
    have hv : v < 4 := by simpa using readInt_lt 2 bs v bs1 h1
    split at h <;> omega

/-- The bits up to the next byte boundary, which must be zeros (§9.2). -/
def readFill (bs : List Bool) : Option (List Bool) := do
  let (v, bs) ← readInt (bs.length % 8) bs
  if v = 0 then some bs else none

/-- What follows MNIBBLES 0, up to and past the metadata, none of which reaches the output (§9.2). -/
def readMetadata (bs : List Bool) : Option (List Bool) := do
  let (reserved, bs) ← readInt 1 bs
  if reserved ≠ 0 then none
  else
    let (mskipbytes, bs) ← readInt 2 bs
    let (v, bs) ← readInt (mskipbytes * 8) bs
    if 1 < mskipbytes ∧ v >>> ((mskipbytes - 1) * 8) = 0 then none
    else
      let mskiplen := if mskipbytes = 0 then 0 else v + 1
      let bs ← readFill bs
      if bs.length < mskiplen * 8 then none else some (bs.drop (mskiplen * 8))

/-- The `n` bytes of an uncompressed meta-block (§9.2). -/
def readBytes : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (b, bs) ← readInt 8 bs
    let (rest, bs) ← readBytes n bs
    some (b :: rest, bs)

/-- A category's block switch fields in the meta-block header. -/
structure BlockCategory where
  n : Nat
  typeCode : PrefixCode
  countCode : PrefixCode
  firstCount : Nat
  deriving DecidableEq

/-- A category's fields (§9.2); with fewer than 2 block types, the count is 16777216 (§10). -/
def readBlockCategory (bs : List Bool) : Option (BlockCategory × List Bool) := do
  let (n, bs) ← readVarLen bs
  if n < 2 then some (⟨n, .single 0, .single 0, 16777216⟩, bs)
  else
    let (typeCode, bs) ← readPrefixCode (blockTypeAlphabetSize n) bs
    let (countCode, bs) ← readPrefixCode blockCountAlphabetSize bs
    let (firstCount, bs) ← readBlockCount countCode bs
    some (⟨n, typeCode, countCode, firstCount⟩, bs)

/-- NTREES and its context map of `size` values, all zero below 2 trees (§9.2). -/
def readTreesAndMap (size : Nat) (bs : List Bool) : Option ((Nat × List Nat) × List Bool) := do
  let (ntrees, bs) ← readVarLen bs
  if ntrees < 2 then some ((ntrees, List.replicate size 0), bs)
  else
    let (cmap, bs) ← readContextMap size ntrees bs
    some ((ntrees, cmap), bs)

/-- Each value of a context map read from the header is below 256 (§7.3). -/
theorem readTreesAndMap_lt {size : Nat} {bs r : List Bool} {ntrees : Nat} {cmap : List Nat}
    (h : readTreesAndMap size bs = some ((ntrees, cmap), r)) : ∀ v ∈ cmap, v < 256 := by
  unfold readTreesAndMap at h
  cases h1 : readVarLen bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨n, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    have hrange := readVarLen_range h1
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      intro v hv
      rw [← h.1.2] at hv
      rw [(List.mem_replicate.mp hv).2]
      decide
    · cases h2 : readContextMap size n bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨m, bs2⟩ := q
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        intro v hv
        rw [← h.1.2] at hv
        have := readContextMap_lt (show 0 < n by omega) h2 v hv
        omega

/-- `n` prefix codes over an alphabet of `size` symbols, in order. -/
def readPrefixCodes (size : Nat) : Nat → List Bool → Option (List PrefixCode × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => do
    let (code, bs) ← readPrefixCode size bs
    let (codes, bs) ← readPrefixCodes size n bs
    some (code :: codes, bs)

/-- The literal code alphabet's size (§3.3). -/
def literalAlphabetSize : Nat := 256

/-- The fields of a compressed meta-block's header after ISUNCOMPRESSED. -/
structure MetaBlockHeader where
  literal : BlockCategory
  insertCopy : BlockCategory
  distance : BlockCategory
  npostfix : Nat
  ndirect : Nat
  contextModes : List Nat
  literalMap : List Nat
  distanceMap : List Nat
  literalCodes : List PrefixCode
  insertCopyCodes : List PrefixCode
  distanceCodes : List PrefixCode

/-- The header's fields after ISUNCOMPRESSED, in order (§9.2). -/
def readMetaBlockHeader (bs : List Bool) : Option (MetaBlockHeader × List Bool) := do
  let (literal, bs) ← readBlockCategory bs
  let (insertCopy, bs) ← readBlockCategory bs
  let (distance, bs) ← readBlockCategory bs
  let (npostfix, bs) ← readInt 2 bs
  let (ndirectHigh, bs) ← readInt 4 bs
  let ndirect := ndirectHigh <<< npostfix
  let (contextModes, bs) ← readContextModes literal.n bs
  let ((ntreesL, literalMap), bs) ← readTreesAndMap (literalContextMapSize literal.n) bs
  let ((ntreesD, distanceMap), bs) ← readTreesAndMap (distanceContextMapSize distance.n) bs
  let (literalCodes, bs) ← readPrefixCodes literalAlphabetSize ntreesL bs
  let (insertCopyCodes, bs) ← readPrefixCodes insertCopyAlphabetSize insertCopy.n bs
  let (distanceCodes, bs) ← readPrefixCodes (distanceAlphabetSize npostfix ndirect) ntreesD bs
  some (⟨literal, insertCopy, distance, npostfix, ndirect, contextModes, literalMap, distanceMap,
    literalCodes, insertCopyCodes, distanceCodes⟩, bs)

/-! ### The meta-block data (§9.3) -/

/-- A category's block types, the elements left of the current block, and the types that occurred. -/
structure BlockState where
  types : BlockTypes
  count : Nat
  seen : List Nat

/-- The state at the start of a meta-block's data (§6). -/
def BlockState.initial (c : BlockCategory) : BlockState :=
  ⟨initialBlockTypes, c.firstCount, [0]⟩

/-- The block switch before an element of a category, if its count is zero, and the element's count
(§9.3, §6). -/
def nextElement (c : BlockCategory) (st : BlockState) (bs : List Bool) :
    Option (BlockState × List Bool) :=
  if st.count = 0 then
    if c.n < 2 then none
    else do
      let (types, bs) ← readBlockType c.n c.typeCode st.types bs
      let (count, bs) ← readBlockCount c.countCode bs
      some (⟨types, count - 1, types.cur :: st.seen⟩, bs)
  else some ({ st with count := st.count - 1 }, bs)

/-- `n` literals, each pushed onto `output`, most recent first (§9.3). -/
def readLiterals (h : MetaBlockHeader) :
    Nat → BlockState → List Nat → List Bool → Option (BlockState × List Nat × List Bool)
  | 0, st, output, bs => some (st, output, bs)
  | n + 1, st, output, bs => do
    let (st, bs) ← nextElement h.literal st bs
    let mode ← h.contextModes[st.types.cur]?
    let index ← literalPrefixCodeIndex h.literalMap st.types.cur
      (contextId mode (contextBytes output).1 (contextBytes output).2)
    let code ← h.literalCodes[index]?
    let (byte, bs) ← decodeSymbol code bs
    readLiterals h n st (byte :: output) bs

/-- A command's distance symbol and distance, implicitly symbol 0 for some codes (§9.3, §5, with erratum
6977). -/
def readCommandDistance (h : MetaBlockHeader) (st : BlockState) (r : Distances) (c clen : Nat)
    (bs : List Bool) : Option ((BlockState × Nat × Nat) × List Bool) :=
  if implicitZeroDistance c then do
    let d ← distanceOf h.npostfix h.ndirect r 0 0
    some ((st, 0, d), bs)
  else do
    let (st, bs) ← nextElement h.distance st bs
    let index ← distancePrefixCodeIndex h.distanceMap st.types.cur (distanceContextId clen)
    let code ← h.distanceCodes[index]?
    let ((dcode, d), bs) ← readDistance h.npostfix h.ndirect code r bs
    some ((st, dcode, d), bs)

/-- The output after copying `n` bytes from `distance` back, one at a time, so a copy may overlap (§10). -/
def copyBytes (distance : Nat) : Nat → List Nat → List Nat
  | 0, output => output
  | n + 1, output => copyBytes distance n (output.getD (distance - 1) 0 :: output)

/-- The state of a meta-block's data. `output`, most recent first, `produced` and `distances` carry over
between meta-blocks (§7.1, §4). `remaining` is the bytes left of MLEN. -/
structure CommandState where
  output : List Nat
  produced : Nat
  distances : Distances
  remaining : Nat
  insertCopy : BlockState
  literal : BlockState
  distance : BlockState

/-- The copy of a command, a backward copy or a dictionary word, with `w` the window size (§9.3). -/
def copyCommand (w : Nat) (s : CommandState) (clen dcode d : Nat) : Option CommandState :=
  let maxDistance := maxBackwardDistance w s.produced
  let dictionary := isDictionaryReference d maxDistance
  let s := { s with distances := pushDistance s.distances dcode d dictionary }
  if dictionary then do
    let word ← dictionaryWord clen d maxDistance
    if s.remaining < word.length then none
    else
      some { s with
        output := word.reverse ++ s.output
        produced := s.produced + word.length
        remaining := s.remaining - word.length }
  else if s.remaining < clen then none
  else
    some { s with
      output := copyBytes d clen s.output
      produced := s.produced + clen
      remaining := s.remaining - clen }

/-- One command (§9.3). If its literals reach MLEN, its copy is ignored; literals past MLEN are invalid. -/
def readCommand (w : Nat) (h : MetaBlockHeader) (s : CommandState) (bs : List Bool) :
    Option (CommandState × List Bool) := do
  let (insertCopy, bs) ← nextElement h.insertCopy s.insertCopy bs
  let code ← h.insertCopyCodes[insertCopy.types.cur]?
  let ((c, ilen, clen), bs) ← readInsertCopy code bs
  if s.remaining < ilen then none
  else
    let (literal, output, bs) ← readLiterals h ilen s.literal s.output bs
    let s := { s with
      insertCopy, literal, output
      produced := s.produced + ilen
      remaining := s.remaining - ilen }
    if s.remaining = 0 then some (s, bs)
    else
      let ((distance, dcode, d), bs) ← readCommandDistance h s.distance s.distances c clen bs
      let s ← copyCommand w { s with distance } clen dcode d
      some (s, bs)

/-- The loop of `readCommands`, with `out` the out-of-fuel result. -/
def readCommandsWith (w : Nat) (h : MetaBlockHeader) (out : Option (CommandState × List Bool)) :
    Nat → CommandState → List Bool → Option (CommandState × List Bool)
  | 0, _, _ => out
  | fuel + 1, s, bs =>
    if s.remaining = 0 then some (s, bs)
    else do
      let (s, bs) ← readCommand w h s bs
      readCommandsWith w h out fuel s bs

/-- The fuel quantity: the bits left times one more than the largest block count, plus the
insert-and-copy block count left. -/
def commandMeasure (s : CommandState) (bs : List Bool) : Nat :=
  bs.length * 16793841 + s.insertCopy.count

/-- A meta-block's commands, until MLEN bytes are produced (§9.3). Block counts need not reach zero (§6).
Fuel: `commandMeasure` plus 1 (`readCommands_out`). -/
def readCommands (w : Nat) (h : MetaBlockHeader) :
    Nat → CommandState → List Bool → Option (CommandState × List Bool) :=
  readCommandsWith w h none

/-- The state of the stream between meta-blocks. -/
structure StreamState where
  output : List Nat
  produced : Nat
  distances : Distances

/-- Every block type of a category occurred (§6). -/
def usesEveryType (c : BlockCategory) (st : BlockState) : Bool :=
  (List.range c.n).all st.seen.contains

/-- A compressed meta-block after ISUNCOMPRESSED: its header, then its commands. -/
def readCompressed (w : Nat) (st : StreamState) (mlen : Nat) (bs : List Bool) :
    Option (StreamState × List Bool) := do
  let (h, bs) ← readMetaBlockHeader bs
  let s : CommandState :=
    ⟨st.output, st.produced, st.distances, mlen, .initial h.insertCopy, .initial h.literal,
      .initial h.distance⟩
  let (s, bs) ← readCommands w h (commandMeasure s bs + 1) s bs
  if usesEveryType h.literal s.literal && usesEveryType h.insertCopy s.insertCopy &&
      usesEveryType h.distance s.distance then
    some (⟨s.output, s.produced, s.distances⟩, bs)
  else none

/-- ISUNCOMPRESSED, present only if ISLAST is not set (§9.2). -/
def readIsUncompressed (islast : Bool) (bs : List Bool) : Option (Nat × List Bool) :=
  if islast then some (0, bs) else readInt 1 bs

/-- A meta-block after ISLAST and ISLASTEMPTY: metadata, uncompressed or compressed (§9.2). -/
def readMetaBlockBody (w : Nat) (st : StreamState) (islast : Bool) (bs : List Bool) :
    Option (StreamState × List Bool) := do
  let (mnibbles, bs) ← readMNIBBLES bs
  if mnibbles = 0 then
    let bs ← readMetadata bs
    some (st, bs)
  else
    let (mlen, bs) ← readMLEN mnibbles bs
    let (isuncompressed, bs) ← readIsUncompressed islast bs
    if isuncompressed = 1 then
      let bs ← readFill bs
      let (bytes, bs) ← readBytes mlen bs
      some (⟨bytes.reverse ++ st.output, st.produced + mlen, st.distances⟩, bs)
    else readCompressed w st mlen bs

/-- A meta-block (§9.2). Returns whether it was the last. -/
def readMetaBlock (w : Nat) (st : StreamState) (bs : List Bool) :
    Option ((StreamState × Bool) × List Bool) := do
  let (islast, bs) ← readInt 1 bs
  if islast = 0 then
    let (st, bs) ← readMetaBlockBody w st false bs
    some ((st, false), bs)
  else
    let (islastempty, bs) ← readInt 1 bs
    if islastempty = 1 then some ((st, true), bs)
    else
      let (st, bs) ← readMetaBlockBody w st true bs
      some ((st, true), bs)

/-- The loop of `readMetaBlocks`, with `out` the out-of-fuel result. -/
def readMetaBlocksWith (w : Nat) (out : Option (StreamState × List Bool)) :
    Nat → StreamState → List Bool → Option (StreamState × List Bool)
  | 0, _, _ => out
  | fuel + 1, st, bs => do
    let ((st, islast), bs) ← readMetaBlock w st bs
    if islast then some (st, bs) else readMetaBlocksWith w out fuel st bs

/-- The meta-blocks, until one is the last (§9.2). Fuel: the bits left, plus 1 (`readMetaBlocks_out`). -/
def readMetaBlocks (w : Nat) :
    Nat → StreamState → List Bool → Option (StreamState × List Bool) :=
  readMetaBlocksWith w none

/-- The stream's end: zero fill bits and nothing more (§9.2, §9.3). -/
def readEnd (bs : List Bool) : Option Unit := do
  let bs ← readFill bs
  if bs.isEmpty then some () else none

/-- The format's entry point: `some y` for a valid stream with output `y`, `none` otherwise. -/
def decode (input : List UInt8) : Option (List UInt8) := do
  let (wbits, bs) ← readWBITS (bits input)
  let (st, bs) ← readMetaBlocks (windowSize wbits) (bs.length + 1) ⟨[], 0, initialDistances⟩ bs
  let _ ← readEnd bs
  some (st.output.reverse.map Nat.toUInt8)

/-! ### No reader adds bits -/

private theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => simp [bind] at h
  | some a => exact ⟨a, rfl, h⟩

/-- An integer value of `n` bits takes `n` bits. -/
theorem readInt_length : ∀ (n : Nat) (bs : List Bool) (v : Nat) (r : List Bool),
    readInt n bs = some (v, r) → r.length + n = bs.length
  | 0, _, _, _, h => by
    simp only [readInt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp
  | _ + 1, [], _, _, h => by simp [readInt] at h
  | n + 1, b :: bs, v, r, h => by
    simp only [readInt] at h
    cases hr : readInt n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨w, r'⟩ := p
      have := readInt_length n bs w r' hr
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [List.length_cons]
      omega

theorem readInt_le {n : Nat} {bs r : List Bool} {v : Nat} (h : readInt n bs = some (v, r)) :
    r.length ≤ bs.length := by
  have := readInt_length n bs v r h
  omega

theorem decodeSymbol_le {c : PrefixCode} {bs r : List Bool} {s : Nat}
    (h : decodeSymbol c bs = some (s, r)) : r.length ≤ bs.length := by
  cases c with
  | single sym =>
    simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | canonical lens =>
    obtain ⟨_, _, w, _, _, _, _, rfl⟩ := decodeLengths_sound lens 15 1 bs s r (by decide) h
    simp

theorem readSimpleSymbols_le (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (bs : List Bool) (out : List Nat) (r : List Bool),
    readSimpleSymbols size bits n syms bs = some (out, r) → r.length ≤ bs.length
  | 0, _, _, _, _, h => by
    simp only [readSimpleSymbols, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | n + 1, syms, bs, out, r, h => by
    simp only [readSimpleSymbols] at h
    obtain ⟨⟨v, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    split at h
    · simp at h
    · exact Nat.le_trans (readSimpleSymbols_le size bits n _ bs1 out r h) (readInt_le h1)

theorem readSimple_le {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readSimple size bs = some (c, r)) : r.length ≤ bs.length := by
  unfold readSimple at h
  obtain ⟨⟨nsym, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨syms, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_le h1
  have l2 := readSimpleSymbols_le size _ _ _ _ _ _ h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · obtain ⟨⟨ts, bs3⟩, h3, h⟩ := bind_some h
    dsimp only at h
    have l3 := readInt_le h3
    split at h <;>
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      omega
  · simp at h

theorem readCodeLengthCodeLength_le' {bs r : List Bool} {v : Nat}
    (h : readCodeLengthCodeLength bs = some (v, r)) : r.length ≤ bs.length := by
  unfold readCodeLengthCodeLength at h
  obtain ⟨⟨sym, n, printed⟩, _, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only at hf
  split at hf
  · rename_i hr
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl⟩ := hf
      exact readInt_le hr
    · simp at hf
  · simp at hf

theorem readCodeLengthCodeLengths_le : ∀ (order : List Nat) (acc : List (Nat × Nat))
    (sum : Nat) (bs : List Bool) (pairs : List (Nat × Nat)) (r : List Bool),
    readCodeLengthCodeLengths order acc sum bs = some (pairs, r) → r.length ≤ bs.length
  | [], _, _, bs, _, r, h => by
    simp only [readCodeLengthCodeLengths] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_refl _
    · simp at h
  | sym :: order, acc, sum, bs, pairs, r, h => by
    simp only [readCodeLengthCodeLengths] at h
    obtain ⟨⟨len, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    have l1 := readCodeLengthCodeLength_le' h1
    split at h
    · exact Nat.le_trans (readCodeLengthCodeLengths_le order _ _ bs1 pairs r h) l1
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        exact l1
      · split at h
        · simp at h
        · exact Nat.le_trans (readCodeLengthCodeLengths_le order _ _ bs1 pairs r h) l1

theorem readSymbolLengths_le (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
    (st : LengthState) (bs : List Bool) (lens : List Nat) (r : List Bool),
    readSymbolLengths size clc fuel st bs = some (lens, r) → r.length ≤ bs.length
  | 0, _, _, _, _, h => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, bs, lens, r, h => by
    simp only [readSymbolLengths, readSymbolLengthsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_refl _
    split at h
    · simp at h
    obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨e, bs2⟩, h2, h⟩ := bind_some h
    dsimp only at h
    have l1 := decodeSymbol_le h1
    have l2 := readInt_le h2
    split at h
    · simp at h
    split at h
    · simp at h
    have := readSymbolLengths_le size clc f _ bs2 lens r h
    omega

theorem readPrefixCode_le {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) : r.length ≤ bs.length := by
  unfold readPrefixCode at h
  obtain ⟨⟨hskip, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_le h1
  split at h
  · exact Nat.le_trans (readSimple_le h) l1
  · unfold readComplex at h
    obtain ⟨⟨pairs, bs2⟩, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨lens, bs3⟩, h3, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readCodeLengthCodeLengths_le _ _ _ _ _ _ h2
    have := readSymbolLengths_le _ _ _ _ _ _ _ h3
    omega

theorem readContextModes_le : ∀ (n : Nat) (bs : List Bool) (modes : List Nat) (r : List Bool),
    readContextModes n bs = some (modes, r) → r.length ≤ bs.length
  | 0, _, _, _, h => by
    simp only [readContextModes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | n + 1, bs, modes, r, h => by
    simp only [readContextModes] at h
    obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨ms, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_trans (readContextModes_le n bs1 ms _ h2) (readInt_le h1)

theorem readContextMapValues_le (rlemax : Nat) (code : PrefixCode) : ∀ (fuel left : Nat)
    (bs : List Bool) (vals : List Nat) (r : List Bool),
    readContextMapValues rlemax code fuel left bs = some (vals, r) → r.length ≤ bs.length
  | 0, _, _, _, _, h => by simp [readContextMapValues, readContextMapValuesWith] at h
  | f + 1, left, bs, vals, r, h => by
    simp only [readContextMapValues, readContextMapValuesWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_refl _
    obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    have l1 := decodeSymbol_le h1
    split at h
    · obtain ⟨⟨vs, bs2⟩, h2, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_trans (readContextMapValues_le rlemax code f _ bs1 vs _ h2) l1
    · obtain ⟨⟨e, bs2⟩, h2, h⟩ := bind_some h
      dsimp only at h
      have l2 := readInt_le h2
      split at h
      · simp at h
      · obtain ⟨⟨vs, bs3⟩, h3, h⟩ := bind_some h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := readContextMapValues_le rlemax code f _ bs2 vs _ h3
        omega

theorem readRLEMAX_le {bs r : List Bool} {v : Nat} (h : readRLEMAX bs = some (v, r)) :
    r.length ≤ bs.length := by
  unfold readRLEMAX at h
  obtain ⟨⟨flag, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_le h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact l1
  · obtain ⟨⟨x, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_trans (readInt_le h2) l1

theorem readContextMap_le {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
    (h : readContextMap size ntrees bs = some (cmap, r)) : r.length ≤ bs.length := by
  unfold readContextMap at h
  obtain ⟨⟨rlemax, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨code, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨vals, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨imtf, bs4⟩, h4, h⟩ := bind_some h
  dsimp only at h
  have := readRLEMAX_le h1
  have := readPrefixCode_le h2
  have := readContextMapValues_le _ _ _ _ _ _ _ h3
  have := readInt_le h4
  generalize (if imtf = 0 then vals else inverseMoveToFront vals) = final at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · simp at h

theorem readVarLen_le {bs r : List Bool} {v : Nat} (h : readVarLen bs = some (v, r)) :
    r.length ≤ bs.length := by
  unfold readVarLen at h
  obtain ⟨⟨first, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_le h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact l1
  obtain ⟨⟨n, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have l2 := readInt_le h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  obtain ⟨⟨x, bs3⟩, h3, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have := readInt_le h3
  omega

/-- A block count takes at least 2 bits, and is at most 16793840. -/
theorem readBlockCount_bound {code : PrefixCode} {bs r : List Bool} {v : Nat}
    (h : readBlockCount code bs = some (v, r)) : r.length + 2 ≤ bs.length ∧ v ≤ 16793840 := by
  unfold readBlockCount at h
  obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨bits, lowest, highest⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨extra, bs2⟩, h3, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hmem := List.mem_of_getElem? h2
  have hb := (blockCountCodes_extraBits.1 _ hmem).1
  have hm := blockCountCodes_largest.1 _ hmem
  have hr := blockCountCodes_ranges _ hmem
  simp only at hb hm hr
  have l1 := decodeSymbol_le h1
  have l3 := readInt_length _ _ _ _ h3
  have hx := readInt_lt _ _ _ _ h3
  omega

theorem readBlockType_le {n : Nat} {code : PrefixCode} {bt bt' : BlockTypes}
    {bs r : List Bool} (h : readBlockType n code bt bs = some (bt', r)) : r.length ≤ bs.length := by
  unfold readBlockType at h
  obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact decodeSymbol_le h1

theorem readBlockCategory_le {bs r : List Bool} {c : BlockCategory}
    (h : readBlockCategory bs = some (c, r)) : r.length ≤ bs.length := by
  unfold readBlockCategory at h
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readVarLen_le h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact l1
  obtain ⟨⟨tc, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cc, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨fc, bs4⟩, h4, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have := readPrefixCode_le h2
  have := readPrefixCode_le h3
  have := (readBlockCount_bound h4).1
  omega

theorem readTreesAndMap_le {size : Nat} {bs r : List Bool} {p : Nat × List Nat}
    (h : readTreesAndMap size bs = some (p, r)) : r.length ≤ bs.length := by
  unfold readTreesAndMap at h
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readVarLen_le h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact l1
  obtain ⟨⟨m, bs2⟩, h2, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact Nat.le_trans (readContextMap_le h2) l1

theorem readPrefixCodes_le (size : Nat) : ∀ (n : Nat) (bs : List Bool)
    (codes : List PrefixCode) (r : List Bool),
    readPrefixCodes size n bs = some (codes, r) → r.length ≤ bs.length
  | 0, _, _, _, h => by
    simp only [readPrefixCodes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | n + 1, bs, codes, r, h => by
    simp only [readPrefixCodes] at h
    obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨cs, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_trans (readPrefixCodes_le size n bs1 cs _ h2) (readPrefixCode_le h1)

theorem readMetaBlockHeader_le {bs r : List Bool} {m : MetaBlockHeader}
    (h : readMetaBlockHeader bs = some (m, r)) : r.length ≤ bs.length := by
  unfold readMetaBlockHeader at h
  obtain ⟨⟨c1, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c2, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c3, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨np, bs4⟩, h4, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨nd, bs5⟩, h5, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ms, bs6⟩, h6, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨tl, ml⟩, bs7⟩, h7, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨td, md⟩, bs8⟩, h8, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cl, bs9⟩, h9, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ci, bs10⟩, h10, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cd, bs11⟩, h11, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have := readBlockCategory_le h1
  have := readBlockCategory_le h2
  have := readBlockCategory_le h3
  have := readInt_le h4
  have := readInt_le h5
  have := readContextModes_le _ _ _ _ h6
  have := readTreesAndMap_le h7
  have := readTreesAndMap_le h8
  have := readPrefixCodes_le _ _ _ _ _ h9
  have := readPrefixCodes_le _ _ _ _ _ h10
  have := readPrefixCodes_le _ _ _ _ _ h11
  omega

/-- NPOSTFIX is at most 3 and NDIRECT at most 120, the ranges `readMetaBlockHeader` cites. -/
theorem readMetaBlockHeader_range {bs r : List Bool} {m : MetaBlockHeader}
    (h : readMetaBlockHeader bs = some (m, r)) : m.npostfix < 4 ∧ m.ndirect ≤ 120 := by
  unfold readMetaBlockHeader at h
  obtain ⟨⟨c1, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c2, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c3, bs3⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨np, bs4⟩, h4, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨nd, bs5⟩, h5, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ms, bs6⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨tl, ml⟩, bs7⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨td, md⟩, bs8⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cl, bs9⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ci, bs10⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cd, bs11⟩, _, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hnp : np < 4 := by simpa using readInt_lt 2 _ _ _ h4
  have hnd : nd < 16 := by simpa using readInt_lt 4 _ _ _ h5
  have key : ∀ a < 4, ∀ b < 16, b <<< a ≤ 120 := by decide
  exact ⟨hnp, key np hnp nd hnd⟩

theorem nextElement_le {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
    (h : nextElement c st bs = some (st', r)) : r.length ≤ bs.length := by
  unfold nextElement at h
  split at h
  · split at h
    · simp at h
    obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨cnt, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readBlockType_le h1
    have := (readBlockCount_bound h2).1
    omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _

/-- The measure of the insert-and-copy category falls at each element. -/
theorem nextElement_measure {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
    (h : nextElement c st bs = some (st', r)) :
    r.length * 16793841 + st'.count < bs.length * 16793841 + st.count := by
  unfold nextElement at h
  split at h
  · split at h
    · simp at h
    obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨cnt, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have := readBlockType_le h1
    have := readBlockCount_bound h2
    simp only
    omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only
    omega

theorem readLiterals_le (h : MetaBlockHeader) : ∀ (n : Nat) (st : BlockState)
    (output : List Nat) (bs : List Bool) (st' : BlockState) (o : List Nat) (r : List Bool),
    readLiterals h n st output bs = some (st', o, r) → r.length ≤ bs.length
  | 0, _, _, _, _, _, _, hr => by
    simp only [readLiterals, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨-, -, rfl⟩ := hr
    exact Nat.le_refl _
  | n + 1, st, output, bs, st', o, r, hr => by
    simp only [readLiterals] at hr
    obtain ⟨⟨st1, bs1⟩, h1, hr⟩ := bind_some hr
    dsimp only at hr
    obtain ⟨mode, _, hr⟩ := bind_some hr
    obtain ⟨index, _, hr⟩ := bind_some hr
    obtain ⟨code, _, hr⟩ := bind_some hr
    obtain ⟨⟨byte, bs2⟩, h2, hr⟩ := bind_some hr
    dsimp only at hr
    have := nextElement_le h1
    have := decodeSymbol_le h2
    have := readLiterals_le h n _ _ bs2 st' o r hr
    omega

theorem readInsertCopy_le {code : PrefixCode} {bs r : List Bool} {v : Nat × Nat × Nat}
    (h : readInsertCopy code bs = some (v, r)) : r.length ≤ bs.length := by
  unfold readInsertCopy at h
  obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ic, cc⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ib, ibase, _⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cb, cbase, _⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ie, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ce, bs3⟩, h3, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have := decodeSymbol_le h1
  have := readInt_le h2
  have := readInt_le h3
  omega

theorem readCommandDistance_le {m : MetaBlockHeader} {st : BlockState} {d : Distances}
    {c clen : Nat} {bs r : List Bool} {v : BlockState × Nat × Nat}
    (h : readCommandDistance m st d c clen bs = some (v, r)) : r.length ≤ bs.length := by
  unfold readCommandDistance at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  · obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨⟨⟨dcode, dist⟩, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := nextElement_le h1
    unfold readDistance at h2
    obtain ⟨⟨sym, bs3⟩, h3, h2⟩ := bind_some h2
    dsimp only at h2
    obtain ⟨⟨e, bs4⟩, h4, h2⟩ := bind_some h2
    dsimp only at h2
    obtain ⟨_, _, h2⟩ := bind_some h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h2
    have := decodeSymbol_le h3
    have := readInt_le h4
    omega

theorem copyCommand_insertCopy {w clen dcode d : Nat} {s s' : CommandState}
    (h : copyCommand w s clen dcode d = some s') : s'.insertCopy = s.insertCopy := by
  unfold copyCommand at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_some h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]

/-- A command's insert-and-copy element, and what follows it. -/
theorem readCommand_spec {w : Nat} {m : MetaBlockHeader} {s s' : CommandState}
    {bs r : List Bool} (h : readCommand w m s bs = some (s', r)) :
    ∃ bs1, nextElement m.insertCopy s.insertCopy bs = some (s'.insertCopy, bs1) ∧
      r.length ≤ bs1.length := by
  unfold readCommand at h
  obtain ⟨⟨ic, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨code, _, h⟩ := bind_some h
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  have l2 := readInsertCopy_le h2
  have l3 := readLiterals_le _ _ _ _ _ _ _ _ h3
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨bs1, h1, by omega⟩
  · obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, h4, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have l4 := readCommandDistance_le h4
    refine ⟨bs1, ?_, by omega⟩
    rw [copyCommand_insertCopy h5]
    exact h1

/-- Each command lowers `commandMeasure`. -/
theorem readCommand_measure {w : Nat} {m : MetaBlockHeader} {s s' : CommandState} {bs r : List Bool}
    (h : readCommand w m s bs = some (s', r)) : commandMeasure s' r < commandMeasure s bs := by
  obtain ⟨bs1, h1, l⟩ := readCommand_spec h
  unfold commandMeasure
  exact Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_right 16793841 l) _)
    (nextElement_measure h1)

/-- While the fuel exceeds `commandMeasure`, the loop never reaches its out-of-fuel result: the result
is the same whatever that result is. -/
theorem readCommandsWith_out (w : Nat) (m : MetaBlockHeader) : ∀ (fuel : Nat) (s : CommandState)
    (bs : List Bool), commandMeasure s bs < fuel → ∀ out out',
    readCommandsWith w m out fuel s bs = readCommandsWith w m out' fuel s bs
  | 0, _, _, hf, _, _ => by omega
  | f + 1, s, bs, hf, out, out' => by
    simp only [readCommandsWith]
    split
    · rfl
    cases hc : readCommand w m s bs with
    | none => rfl
    | some p =>
      obtain ⟨s1, bs1⟩ := p
      have := readCommand_measure hc
      exact readCommandsWith_out w m f s1 bs1 (by omega) out out'

/-- With the fuel `readCompressed` gives it, `readCommands` never reaches its out-of-fuel result: any
other value in its place gives the same result. -/
theorem readCommands_out (w : Nat) (m : MetaBlockHeader) (s : CommandState) (bs : List Bool)
    (out : Option (CommandState × List Bool)) :
    readCommands w m (commandMeasure s bs + 1) s bs =
      readCommandsWith w m out (commandMeasure s bs + 1) s bs :=
  readCommandsWith_out w m _ s bs (by omega) none out

theorem readCommands_le (w : Nat) (m : MetaBlockHeader) : ∀ (fuel : Nat) (s s' : CommandState)
    (bs r : List Bool), readCommands w m fuel s bs = some (s', r) → r.length ≤ bs.length
  | 0, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | f + 1, s, s', bs, r, h => by
    simp only [readCommands, readCommandsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_refl _
    obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨bs2, h2, l⟩ := readCommand_spec h1
    have := nextElement_le h2
    have := readCommands_le w m f s1 s' bs1 r h
    omega

theorem readCompressed_le {w mlen : Nat} {st st' : StreamState} {bs r : List Bool}
    (h : readCompressed w st mlen bs = some (st', r)) : r.length ≤ bs.length := by
  unfold readCompressed at h
  obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨s, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have := readMetaBlockHeader_le h1
  have := readCommands_le _ _ _ _ _ _ _ h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · simp at h

theorem readFill_le {bs r : List Bool} (h : readFill bs = some r) : r.length ≤ bs.length := by
  unfold readFill at h
  obtain ⟨⟨v, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact readInt_le h1
  · simp at h

theorem readMetadata_le {bs r : List Bool} (h : readMetadata bs = some r) :
    r.length ≤ bs.length := by
  unfold readMetadata at h
  obtain ⟨⟨res, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  obtain ⟨⟨mb, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨v, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  generalize (if mb = 0 then 0 else v + 1) = mskiplen at h
  obtain ⟨bs4, h4, h⟩ := bind_some h
  have := readInt_le h1
  have := readInt_le h2
  have := readInt_le h3
  have := readFill_le h4
  split at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only [List.length_drop]
    omega

theorem readBytes_le : ∀ (n : Nat) (bs : List Bool) (bytes : List Nat) (r : List Bool),
    readBytes n bs = some (bytes, r) → r.length ≤ bs.length
  | 0, _, _, _, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | n + 1, bs, bytes, r, h => by
    simp only [readBytes] at h
    obtain ⟨⟨b, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rest, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_trans (readBytes_le n bs1 rest _ h2) (readInt_le h1)

theorem readMetaBlockBody_le {w : Nat} {st st' : StreamState} {islast : Bool}
    {bs r : List Bool} (h : readMetaBlockBody w st islast bs = some (st', r)) :
    r.length ≤ bs.length := by
  unfold readMetaBlockBody at h
  obtain ⟨⟨mn, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 : bs1.length ≤ bs.length := by
    unfold readMNIBBLES at h1
    obtain ⟨⟨v, bs0⟩, h0, h1⟩ := bind_some h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, rfl⟩ := h1
    exact readInt_le h0
  split at h
  · obtain ⟨bs2, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_trans (readMetadata_le h2) l1
  obtain ⟨⟨mlen, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have l2 : bs2.length ≤ bs1.length := by
    unfold readMLEN at h2
    obtain ⟨⟨v, bs0⟩, h0, h2⟩ := bind_some h2
    dsimp only at h2
    split at h2
    · simp at h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨-, rfl⟩ := h2
      exact readInt_le h0
  obtain ⟨⟨iu, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  have l3 : bs3.length ≤ bs2.length := by
    unfold readIsUncompressed at h3
    split at h3
    · simp only [Option.some.injEq, Prod.mk.injEq] at h3
      obtain ⟨-, rfl⟩ := h3
      exact Nat.le_refl _
    · exact readInt_le h3
  split at h
  · obtain ⟨bs4, h4, h⟩ := bind_some h
    obtain ⟨⟨bytes, bs5⟩, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readFill_le h4
    have := readBytes_le _ _ _ _ h5
    omega
  · have := readCompressed_le h
    omega

/-- Each meta-block reads at least a bit. -/
theorem readMetaBlock_lt {w : Nat} {st : StreamState} {v : StreamState × Bool} {bs r : List Bool}
    (h : readMetaBlock w st bs = some (v, r)) : r.length < bs.length := by
  unfold readMetaBlock at h
  obtain ⟨⟨islast, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_length _ _ _ _ h1
  split at h
  · obtain ⟨⟨st1, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readMetaBlockBody_le h2
    omega
  obtain ⟨⟨ie, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have l2 := readInt_le h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · obtain ⟨⟨st1, bs3⟩, h3, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readMetaBlockBody_le h3
    omega

/-- While the fuel exceeds the bits left, the loop never reaches its out-of-fuel result: the result is
the same whatever that result is. -/
theorem readMetaBlocksWith_out (w : Nat) : ∀ (fuel : Nat) (st : StreamState) (bs : List Bool),
    bs.length < fuel → ∀ out out',
    readMetaBlocksWith w out fuel st bs = readMetaBlocksWith w out' fuel st bs
  | 0, _, _, hf, _, _ => by omega
  | f + 1, st, bs, hf, out, out' => by
    simp only [readMetaBlocksWith]
    cases hm : readMetaBlock w st bs with
    | none => rfl
    | some p =>
      obtain ⟨⟨st1, islast⟩, bs1⟩ := p
      have := readMetaBlock_lt hm
      dsimp only [bind, Option.bind]
      split
      · rfl
      · exact readMetaBlocksWith_out w f st1 bs1 (by omega) out out'

/-- With the fuel `decode` gives it, `readMetaBlocks` never reaches its out-of-fuel result: any other
value in its place gives the same result. -/
theorem readMetaBlocks_out (w : Nat) (st : StreamState) (bs : List Bool)
    (out : Option (StreamState × List Bool)) :
    readMetaBlocks w (bs.length + 1) st bs = readMetaBlocksWith w out (bs.length + 1) st bs :=
  readMetaBlocksWith_out w _ st bs (by omega) none out

/-! ### Field ranges and widths -/

theorem wbitsCode_fields :
    ∀ e ∈ wbitsCode, 10 ≤ e.1 ∧ e.1 ≤ 24 ∧ (e.2.1 = 1 ∨ e.2.1 = 4 ∨ e.2.1 = 7) := by
  decide +kernel

/-- WBITS is in 10..24 and takes 1 to 7 bits (§9.1). -/
theorem readWBITS_range {bs r : List Bool} {w : Nat} (h : readWBITS bs = some (w, r)) :
    10 ≤ w ∧ w ≤ 24 ∧ r.length + 1 ≤ bs.length ∧ bs.length ≤ r.length + 7 := by
  unfold readWBITS at h
  obtain ⟨⟨wb, n, printed⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only at hf
  split at hf
  · rename_i hr
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hf' := wbitsCode_fields _ hmem
      have := readInt_length _ _ _ _ hr
      simp only at hf'
      omega
    · simp at hf
  · simp at hf

/-- The window size is a power of two minus 16, from 1 KiB - 16 B to 16 MiB - 16 B (§2, §9.1). -/
theorem windowSize_range {w : Nat} (h1 : 10 ≤ w) (h2 : w ≤ 24) :
    windowSize w + 16 = 2 ^ w ∧ 1008 ≤ windowSize w ∧ windowSize w ≤ 16777200 := by
  have key : ∀ w, w < 25 → 10 ≤ w →
      windowSize w + 16 = 2 ^ w ∧ 1008 ≤ windowSize w ∧ windowSize w ≤ 16777200 := by
    decide +kernel
  exact key w (by omega) h1

/-- NBLTYPES and NTREES take 1 to 11 bits (§9.2). -/
theorem readVarLen_width {bs r : List Bool} {v : Nat} (h : readVarLen bs = some (v, r)) :
    r.length + 1 ≤ bs.length ∧ bs.length ≤ r.length + 11 := by
  unfold readVarLen at h
  obtain ⟨⟨first, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_length _ _ _ _ h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  obtain ⟨⟨n, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have l2 := readInt_length _ _ _ _ h2
  have hn : n < 8 := by simpa using readInt_lt 3 _ _ _ h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  obtain ⟨⟨x, bs3⟩, h3, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have := readInt_length _ _ _ _ h3
  omega

/-- RLEMAX takes 1 to 5 bits (§7.3). -/
theorem readRLEMAX_width {bs r : List Bool} {v : Nat} (h : readRLEMAX bs = some (v, r)) :
    r.length + 1 ≤ bs.length ∧ bs.length ≤ r.length + 5 := by
  unfold readRLEMAX at h
  obtain ⟨⟨flag, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have l1 := readInt_length _ _ _ _ h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    omega
  · obtain ⟨⟨x, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have := readInt_length _ _ _ _ h2
    omega

/-- A code length of a code length symbol is 0 to 5 and takes 2 to 4 bits (§3.5). -/
theorem readCodeLengthCodeLength_width {bs r : List Bool} {v : Nat}
    (h : readCodeLengthCodeLength bs = some (v, r)) :
    v ≤ 5 ∧ r.length + 2 ≤ bs.length ∧ bs.length ≤ r.length + 4 := by
  unfold readCodeLengthCodeLength at h
  obtain ⟨⟨sym, n, printed⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only at hf
  split at hf
  · rename_i hr
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have hf' := codeLengthCodeLengthCode_fields _ hmem
      have := readInt_length _ _ _ _ hr
      simp only at hf'
      omega
    · simp at hf
  · simp at hf

/-! ### What a meta-block produces -/

theorem copyBytes_output (d : Nat) : ∀ (n : Nat) (o : List Nat),
    ∃ a, copyBytes d n o = a ++ o ∧ a.length = n
  | 0, _ => ⟨[], rfl, rfl⟩
  | n + 1, o => by
    obtain ⟨a, ha, hl⟩ := copyBytes_output d n (o.getD (d - 1) 0 :: o)
    refine ⟨a ++ [o.getD (d - 1) 0], ?_, by simp [hl]⟩
    simp only [copyBytes]
    rw [ha]
    simp

theorem readLiterals_output (h : MetaBlockHeader) : ∀ (n : Nat) (st : BlockState)
    (output : List Nat) (bs : List Bool) (st' : BlockState) (o : List Nat) (r : List Bool),
    readLiterals h n st output bs = some (st', o, r) → ∃ a, o = a ++ output ∧ a.length = n
  | 0, _, _, _, _, _, _, hr => by
    simp only [readLiterals, Option.some.injEq, Prod.mk.injEq] at hr
    exact ⟨[], by simp [hr.2.1], rfl⟩
  | n + 1, st, output, bs, st', o, r, hr => by
    simp only [readLiterals] at hr
    obtain ⟨⟨st1, bs1⟩, _, hr⟩ := bind_some hr
    dsimp only at hr
    obtain ⟨mode, _, hr⟩ := bind_some hr
    obtain ⟨index, _, hr⟩ := bind_some hr
    obtain ⟨code, _, hr⟩ := bind_some hr
    obtain ⟨⟨byte, bs2⟩, _, hr⟩ := bind_some hr
    dsimp only at hr
    obtain ⟨a, ha, hl⟩ := readLiterals_output h n _ _ bs2 st' o r hr
    exact ⟨a ++ [byte], by simp [ha], by simp [hl]⟩

/-- A copy's distance is at most the window and the bytes produced, and the copy takes the bytes from
there; any other distance is a static dictionary word (§8, §9.1, §10). -/
theorem copyCommand_cases {w clen dcode d : Nat} {s s' : CommandState}
    (h : copyCommand w s clen dcode d = some s') :
    (d ≤ w ∧ d ≤ s.produced ∧ s'.output = copyBytes d clen s.output) ∨
      (maxBackwardDistance w s.produced < d ∧
        ∃ word, dictionaryWord clen d (maxBackwardDistance w s.produced) = some word ∧
          s'.output = word.reverse ++ s.output) := by
  unfold copyCommand at h
  dsimp only at h
  split at h
  · rename_i hd
    obtain ⟨word, h1, h⟩ := bind_some h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      exact Or.inr ⟨by simpa [isDictionaryReference] using hd, word, h1, by rw [← h]⟩
  · rename_i hd
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      have hle := (backwardDistance_iff (w := w) (p := s.produced) (d := d)).mp (by simpa using hd)
      exact Or.inl ⟨hle.1, hle.2, by rw [← h]⟩

theorem copyCommand_output {w clen dcode d : Nat} {s s' : CommandState}
    (h : copyCommand w s clen dcode d = some s') :
    ∃ a, s'.output = a ++ s.output ∧ a.length + s'.remaining = s.remaining ∧
      s'.produced = s.produced + a.length := by
  unfold copyCommand at h
  dsimp only at h
  split at h
  · obtain ⟨word, _, h⟩ := bind_some h
    split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq] at h
      rw [← h]
      refine ⟨word.reverse, rfl, ?_, by simp⟩
      simp only [List.length_reverse]
      omega
  · split at h
    · simp at h
    · rename_i hle
      simp only [Option.some.injEq] at h
      obtain ⟨a, ha, hl⟩ := copyBytes_output d clen s.output
      rw [← h]
      refine ⟨a, ha, ?_, by simp [hl]⟩
      simp only [hl]
      omega

theorem readCommand_output {w : Nat} {m : MetaBlockHeader} {s s' : CommandState}
    {bs r : List Bool} (h : readCommand w m s bs = some (s', r)) :
    ∃ a, s'.output = a ++ s.output ∧ a.length + s'.remaining = s.remaining ∧
      s'.produced = s.produced + a.length := by
  unfold readCommand at h
  obtain ⟨⟨ic, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨code, _, h⟩ := bind_some h
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  rename_i hle
  obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨a1, ha1, hl1⟩ := readLiterals_output _ _ _ _ _ _ _ _ h3
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨a1, ha1, by simp only [hl1]; omega, by simp only [hl1]⟩
  · obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨a2, ha2, hl2, hp2⟩ := copyCommand_output h5
    simp only at ha2 hl2 hp2
    refine ⟨a2 ++ a1, by rw [ha2, ha1, List.append_assoc], ?_, ?_⟩
    · simp only [List.length_append, hl1]
      omega
    · simp only [hp2, List.length_append, hl1]
      omega

/-- A meta-block's commands end at MLEN, having produced exactly the bytes left of it (§9.3). -/
theorem readCommands_output (w : Nat) (m : MetaBlockHeader) : ∀ (fuel : Nat) (s s' : CommandState)
    (bs r : List Bool), readCommands w m fuel s bs = some (s', r) →
    s'.remaining = 0 ∧ s'.produced = s.produced + s.remaining ∧
      ∃ a, s'.output = a ++ s.output ∧ a.length = s.remaining
  | 0, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | f + 1, s, s', bs, r, h => by
    simp only [readCommands, readCommandsWith] at h
    split at h
    · rename_i h0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h0, by omega, [], rfl, by simp [h0]⟩
    obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨a1, ha1, hl1, hp1⟩ := readCommand_output h1
    obtain ⟨h0, hp, a2, ha2, hl2⟩ := readCommands_output w m f s1 s' bs1 r h
    refine ⟨h0, by omega, a2 ++ a1, by rw [ha2, ha1, List.append_assoc], ?_⟩
    simp only [List.length_append]
    omega

/-- A compressed meta-block produces exactly MLEN bytes, added to the output so far (§9.3). -/
theorem readCompressed_output {w mlen : Nat} {st st' : StreamState} {bs r : List Bool}
    (h : readCompressed w st mlen bs = some (st', r)) :
    st'.produced = st.produced + mlen ∧ ∃ a, st'.output = a ++ st.output ∧ a.length = mlen := by
  unfold readCompressed at h
  obtain ⟨⟨m, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨s, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, hp, a, ha, hl⟩ := readCommands_output _ _ _ _ _ _ _ h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hp, a, ha, hl⟩
  · simp at h

theorem readBytes_length : ∀ (n : Nat) (bs : List Bool) (bytes : List Nat) (r : List Bool),
    readBytes n bs = some (bytes, r) → bytes.length = n
  | 0, _, _, _, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | n + 1, bs, bytes, r, h => by
    simp only [readBytes] at h
    obtain ⟨⟨b, bs1⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rest, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp [readBytes_length n bs1 rest bs2 h2]

/-- An empty meta-block leaves the state as it was: it adds nothing to the output, the window or the
context (§2, §9.2). -/
theorem readMetaBlockBody_metadata {w : Nat} {st : StreamState} {islast : Bool} {bs b1 b2 : List Bool}
    (h1 : readMNIBBLES bs = some (0, b1)) (h2 : readMetadata b1 = some b2) :
    readMetaBlockBody w st islast bs = some (st, b2) := by
  unfold readMetaBlockBody
  rw [h1]
  dsimp only [bind, Option.bind]
  simp only [↓reduceIte]
  rw [h2]

/-- ISLAST means no ISUNCOMPRESSED bit is read: a last meta-block that isn't empty is compressed, so an
uncompressed meta-block can't be the last (§2, §9.2). -/
theorem readMetaBlockBody_last {w mnibbles mlen : Nat} {st : StreamState} {bs b1 b2 : List Bool}
    (h1 : readMNIBBLES bs = some (mnibbles, b1)) (h0 : mnibbles ≠ 0)
    (h2 : readMLEN mnibbles b1 = some (mlen, b2)) :
    readMetaBlockBody w st true bs = readCompressed w st mlen b2 := by
  unfold readMetaBlockBody
  rw [h1]
  dsimp only [bind, Option.bind]
  simp only [h0, ↓reduceIte]
  rw [h2]
  dsimp only [bind, Option.bind]
  simp [readIsUncompressed]

/-- A meta-block's returned flag is its ISLAST bit (§9.2). -/
theorem readMetaBlock_flag {w : Nat} {st st' : StreamState} {last : Bool} {bs r : List Bool}
    (h : readMetaBlock w st bs = some ((st', last), r)) :
    ∃ b, readInt 1 bs = some ((if last then 1 else 0), b) := by
  unfold readMetaBlock at h
  obtain ⟨⟨islast, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have hlt : islast < 2 := by simpa using readInt_lt 1 _ _ _ h1
  split at h
  · rename_i h0
    obtain ⟨⟨st1, bs2⟩, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact ⟨bs1, by simpa [h0] using h1⟩
  · rename_i h0
    have h1' : islast = 1 := by omega
    obtain ⟨⟨ie, bs2⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact ⟨bs1, by simpa [h1'] using h1⟩
    · obtain ⟨⟨st1, bs3⟩, _, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact ⟨bs1, by simpa [h1'] using h1⟩

/-- A meta-block with ISLAST set, ISLASTEMPTY clear and a non-zero MNIBBLES is compressed and is the last, so
an uncompressed meta-block can't be the last (§2, §9.2). -/
theorem readMetaBlock_last {w mnibbles mlen : Nat} {st : StreamState} {bs b0 b1 b2 b3 : List Bool}
    (h0 : readInt 1 bs = some (1, b0)) (h1 : readInt 1 b0 = some (0, b1))
    (h2 : readMNIBBLES b1 = some (mnibbles, b2)) (hm : mnibbles ≠ 0)
    (h3 : readMLEN mnibbles b2 = some (mlen, b3)) :
    readMetaBlock w st bs =
      (readCompressed w st mlen b3 >>= fun (st', r) => some ((st', true), r)) := by
  unfold readMetaBlock
  rw [h0]
  dsimp only [bind, Option.bind]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  rw [h1]
  dsimp only
  simp only [Nat.zero_ne_one, ↓reduceIte]
  rw [readMetaBlockBody_last h2 hm h3]

/-- A last meta-block with ISLASTEMPTY set ends the stream with the state unchanged (§2, §9.2). -/
theorem readMetaBlock_lastEmpty {w : Nat} {st : StreamState} {bs b0 b1 : List Bool}
    (h0 : readInt 1 bs = some (1, b0)) (h1 : readInt 1 b0 = some (1, b1)) :
    readMetaBlock w st bs = some ((st, true), b1) := by
  unfold readMetaBlock
  rw [h0]
  dsimp only [bind, Option.bind]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  rw [h1]
  rfl

/-- What a meta-block's result comes from: ISLAST, then ISLASTEMPTY or the meta-block's body (§9.2). -/
theorem readMetaBlock_cases {w : Nat} {st st' : StreamState} {last : Bool} {bs r : List Bool}
    (h : readMetaBlock w st bs = some ((st', last), r)) :
    (∃ b, readInt 1 bs = some (0, b) ∧ last = false ∧ readMetaBlockBody w st false b = some (st', r)) ∨
    (∃ b, readInt 1 bs = some (1, b) ∧ last = true ∧
      ((readInt 1 b = some (1, r) ∧ st' = st) ∨
        ∃ b', readInt 1 b = some (0, b') ∧ readMetaBlockBody w st true b' = some (st', r))) := by
  unfold readMetaBlock at h
  obtain ⟨⟨islast, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have hlt : islast < 2 := by simpa using readInt_lt 1 _ _ _ h1
  split at h
  · rename_i h0
    subst h0
    obtain ⟨⟨st1, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact Or.inl ⟨bs1, h1, rfl, h2⟩
  · rename_i h0
    have h1' : islast = 1 := by omega
    subst h1'
    obtain ⟨⟨ie, bs2⟩, h2, h⟩ := bind_some h
    dsimp only at h
    have hie : ie < 2 := by simpa using readInt_lt 1 _ _ _ h2
    split at h
    · rename_i he
      subst he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact Or.inr ⟨bs1, h1, rfl, Or.inl ⟨h2, rfl⟩⟩
    · rename_i he
      have he' : ie = 0 := by omega
      subst he'
      obtain ⟨⟨st1, bs3⟩, h3, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact Or.inr ⟨bs1, h1, rfl, Or.inr ⟨bs2, h2, h3⟩⟩

/-- What a meta-block's body comes from: metadata, stored bytes, or a compressed meta-block (§9.2). -/
theorem readMetaBlockBody_cases {w : Nat} {st st' : StreamState} {islast : Bool} {bs r : List Bool}
    (h : readMetaBlockBody w st islast bs = some (st', r)) :
    (∃ b1, readMNIBBLES bs = some (0, b1) ∧ readMetadata b1 = some r ∧ st' = st) ∨
    ∃ mn b1 mlen b2 u b3, readMNIBBLES bs = some (mn, b1) ∧ mn ≠ 0 ∧
      readMLEN mn b1 = some (mlen, b2) ∧ readIsUncompressed islast b2 = some (u, b3) ∧
      ((u = 1 ∧ ∃ b4 bytes, readFill b3 = some b4 ∧ readBytes mlen b4 = some (bytes, r) ∧
          st' = ⟨bytes.reverse ++ st.output, st.produced + mlen, st.distances⟩) ∨
        (u ≠ 1 ∧ readCompressed w st mlen b3 = some (st', r))) := by
  unfold readMetaBlockBody at h
  obtain ⟨⟨mn, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · rename_i h0
    subst h0
    obtain ⟨bs2, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨bs1, h1, h2, rfl⟩
  · rename_i h0
    obtain ⟨⟨mlen, bs2⟩, h2, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨iu, bs3⟩, h3, h⟩ := bind_some h
    dsimp only at h
    refine Or.inr ⟨mn, bs1, mlen, bs2, iu, bs3, h1, h0, h2, h3, ?_⟩
    split at h
    · rename_i hu
      obtain ⟨bs4, h4, h⟩ := bind_some h
      obtain ⟨⟨bytes, bs5⟩, h5, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inl ⟨hu, bs4, bytes, h4, by rw [h5, h.2], h.1.symm⟩
    · rename_i hu
      exact Or.inr ⟨hu, h⟩

/-- With bytes left of MLEN, a further step of the commands is one `readCommand`, with the same window (§9.3). -/
theorem readCommands_step {w fuel : Nat} {m : MetaBlockHeader} {s : CommandState} {bs : List Bool}
    (h0 : s.remaining ≠ 0) :
    readCommands w m (fuel + 1) s bs =
      (readCommand w m s bs >>= fun (s1, b) => readCommands w m fuel s1 b) := by
  simp only [readCommands, readCommandsWith, h0, ↓reduceIte]

/-- A command's parts: its literals, and unless they reach MLEN, its distance and `copyCommand` with the
same window (§9.3). -/
theorem readCommand_parts {w : Nat} {m : MetaBlockHeader} {s s' : CommandState} {bs r : List Bool}
    (h : readCommand w m s bs = some (s', r)) :
    ∃ (ic : BlockState) (b1 : List Bool) (code : PrefixCode) (c ilen clen : Nat) (b2 : List Bool)
      (lit : BlockState) (out : List Nat) (b3 : List Bool),
      nextElement m.insertCopy s.insertCopy bs = some (ic, b1) ∧
      m.insertCopyCodes[ic.types.cur]? = some code ∧
      readInsertCopy code b1 = some ((c, ilen, clen), b2) ∧ ilen ≤ s.remaining ∧
      readLiterals m ilen s.literal s.output b2 = some (lit, out, b3) ∧
      ((s.remaining = ilen ∧ r = b3 ∧ s' = { s with
          insertCopy := ic, literal := lit, output := out,
          produced := s.produced + ilen, remaining := s.remaining - ilen }) ∨
        (s.remaining ≠ ilen ∧ ∃ (dst : BlockState) (dcode d : Nat),
          readCommandDistance m s.distance s.distances c clen b3 = some ((dst, dcode, d), r) ∧
          copyCommand w { s with
            insertCopy := ic, literal := lit, output := out,
            produced := s.produced + ilen, remaining := s.remaining - ilen, distance := dst }
            clen dcode d = some s')) := by
  unfold readCommand at h
  obtain ⟨⟨ic, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨code, hc, h⟩ := bind_some h
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  rename_i hle
  obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  refine ⟨ic, bs1, code, c, ilen, clen, bs2, lit, out, bs3, h1, hc, h2, by omega, h3, ?_⟩
  split at h
  · rename_i h0
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨by omega, rfl, rfl⟩
  · rename_i h0
    obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, h4, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inr ⟨by omega, dst, dcode, d, h4, h5⟩

/-- If the literals reach MLEN, the copy length has no effect and no distance is read: the command ends
at the last literal (§2, §9.3, §10). -/
theorem readCommand_literals_reach {w ilen clen c : Nat} {m : MetaBlockHeader} {s : CommandState}
    {ic lit : BlockState} {out : List Nat} {code : PrefixCode} {bs b1 b2 b3 : List Bool}
    (h1 : nextElement m.insertCopy s.insertCopy bs = some (ic, b1))
    (hc : m.insertCopyCodes[ic.types.cur]? = some code)
    (h2 : readInsertCopy code b1 = some ((c, ilen, clen), b2))
    (h3 : readLiterals m ilen s.literal s.output b2 = some (lit, out, b3))
    (hreach : s.remaining = ilen) :
    readCommand w m s bs = some ({ s with
      insertCopy := ic, literal := lit, output := out
      produced := s.produced + ilen, remaining := 0 }, b3) := by
  unfold readCommand
  rw [h1]
  dsimp only [bind, Option.bind]
  rw [hc]
  dsimp only [bind, Option.bind]
  rw [h2]
  dsimp only [bind, Option.bind]
  rw [ite_eq_right (by omega), h3]
  dsimp only [bind, Option.bind]
  rw [ite_eq_left (by omega)]
  simp [hreach]

theorem readMetaBlockBody_output {w : Nat} {st st' : StreamState} {islast : Bool}
    {bs r : List Bool} (h : readMetaBlockBody w st islast bs = some (st', r)) :
    ∃ a, st'.output = a ++ st.output ∧ a.length ≤ 16777216 ∧ st'.produced = st.produced + a.length := by
  unfold readMetaBlockBody at h
  obtain ⟨⟨mn, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨bs2, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨[], rfl, by simp, by simp⟩
  obtain ⟨⟨mlen, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have hr := readMLEN_range (readMNIBBLES_le h1) h2
  obtain ⟨⟨iu, bs3⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨bs4, _, h⟩ := bind_some h
    obtain ⟨⟨bytes, bs5⟩, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hl := readBytes_length _ _ _ _ h5
    exact ⟨bytes.reverse, rfl, by simp only [List.length_reverse]; omega,
      by simp only [List.length_reverse]; omega⟩
  · obtain ⟨hp, a, ha, hl⟩ := readCompressed_output h
    exact ⟨a, ha, by omega, by omega⟩

/-- Each meta-block adds 0 to 16,777,216 bytes to the output (§2). -/
theorem readMetaBlock_output {w : Nat} {st st' : StreamState} {last : Bool} {bs r : List Bool}
    (h : readMetaBlock w st bs = some ((st', last), r)) :
    ∃ a, st'.output = a ++ st.output ∧ a.length ≤ 16777216 ∧ st'.produced = st.produced + a.length := by
  unfold readMetaBlock at h
  obtain ⟨⟨islast, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨⟨st1, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact readMetaBlockBody_output h2
  obtain ⟨⟨ie, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact ⟨[], rfl, by simp, by simp⟩
  · obtain ⟨⟨st1, bs3⟩, h3, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact readMetaBlockBody_output h3

/-- The run of a stream's meta-blocks, each adding one part to the output, most recent byte first, and the
last one the only one flagged last (§2, §9.2). -/
inductive MetaBlockChain (w : Nat) :
    StreamState → List Bool → List (List Nat) → StreamState → List Bool → Prop
  | last {st st' : StreamState} {bs r : List Bool} {a : List Nat} :
    readMetaBlock w st bs = some ((st', true), r) → st'.output = a ++ st.output →
    MetaBlockChain w st bs [a] st' r
  | step {st st1 st' : StreamState} {bs b1 r : List Bool} {a : List Nat} {parts : List (List Nat)} :
    readMetaBlock w st bs = some ((st1, false), b1) → st1.output = a ++ st.output →
    MetaBlockChain w st1 b1 parts st' r → MetaBlockChain w st bs (a :: parts) st' r

/-- The meta-blocks run as a chain ending on the last one, and the output is the concatenation of their
parts, each of at most 16,777,216 bytes (§2). -/
theorem readMetaBlocks_parts (w : Nat) : ∀ (fuel : Nat) (st st' : StreamState) (bs r : List Bool),
    readMetaBlocks w fuel st bs = some (st', r) →
    ∃ parts : List (List Nat), MetaBlockChain w st bs parts st' r ∧
      st'.output.reverse = st.output.reverse ++ (parts.map List.reverse).flatten ∧
      ∀ p ∈ parts, p.length ≤ 16777216
  | 0, _, _, _, _, h => by simp [readMetaBlocks, readMetaBlocksWith] at h
  | f + 1, st, st', bs, r, h => by
    simp only [readMetaBlocks, readMetaBlocksWith] at h
    obtain ⟨⟨⟨st1, last⟩, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨a, ha, hl, _⟩ := readMetaBlock_output h1
    split at h
    · rename_i hlast
      subst hlast
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[a], .last h1 ha, by simp [ha], by simpa using hl⟩
    · rename_i hlast
      have hf : last = false := by simpa using hlast
      subst hf
      obtain ⟨parts, hc, hp, hb⟩ := readMetaBlocks_parts w f st1 st' bs1 r h
      refine ⟨a :: parts, .step h1 ha hc, by simp [hp, ha], ?_⟩
      intro p hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hl
      · exact hb p hm

/-- A valid stream runs its meta-blocks as a chain that ends on the last one, followed by the stream's end,
and `decode`'s output is the concatenation of their parts, each of at most 16,777,216 bytes (§2, §10). -/
theorem decode_parts {input : List UInt8} {y : List UInt8} (h : decode input = some y) :
    ∃ (wbits : Nat) (bs : List Bool) (parts : List (List Nat)) (st : StreamState) (r : List Bool),
      readWBITS (bits input) = some (wbits, bs) ∧
      MetaBlockChain (windowSize wbits) ⟨[], 0, initialDistances⟩ bs parts st r ∧
      readEnd r = some () ∧
      y = (parts.map List.reverse).flatten.map Nat.toUInt8 ∧
      ∀ p ∈ parts, p.length ≤ 16777216 := by
  unfold decode at h
  obtain ⟨⟨wbits, bs⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨st, bs1⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨u, h3, h⟩ := bind_some h
  simp only [Option.some.injEq] at h
  obtain ⟨parts, hc, hp, hb⟩ := readMetaBlocks_parts _ _ _ _ _ _ h2
  refine ⟨wbits, bs, parts, st, bs1, h1, hc, h3, ?_, hb⟩
  rw [← h, hp]
  simp

/-- A chain of meta-blocks is what `readMetaBlocks` reads, given more fuel than bits. -/
theorem readMetaBlocks_of_chain {w : Nat} {st st' : StreamState} {bs r : List Bool}
    {parts : List (List Nat)} (hc : MetaBlockChain w st bs parts st' r) :
    ∀ fuel, bs.length < fuel → readMetaBlocks w fuel st bs = some (st', r) := by
  induction hc with
  | last h1 _ =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ f =>
      simp only [readMetaBlocks, readMetaBlocksWith]
      rw [h1]
      rfl
  | step h1 _ _ ih =>
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ f =>
      have hl := readMetaBlock_lt h1
      simp only [readMetaBlocks, readMetaBlocksWith]
      rw [h1]
      exact ih f (by omega)

/-- The converse of `decode_parts`: a chain of meta-blocks after WBITS, ending on the last one and followed by
the stream's end, is a valid stream, with that chain's output. -/
theorem decode_of_chain {input : List UInt8} {wbits : Nat} {bs r : List Bool} {st : StreamState}
    {parts : List (List Nat)} (h1 : readWBITS (bits input) = some (wbits, bs))
    (hc : MetaBlockChain (windowSize wbits) ⟨[], 0, initialDistances⟩ bs parts st r)
    (he : readEnd r = some ()) : decode input = some (st.output.reverse.map Nat.toUInt8) := by
  unfold decode
  rw [h1]
  dsimp only [bind, Option.bind]
  rw [readMetaBlocks_of_chain hc _ (by omega)]
  dsimp only
  rw [he]

/-- A valid stream has at least one meta-block (§2, §9.2). -/
theorem decode_metaBlock {input : List UInt8} {y : List UInt8} (h : decode input = some y) :
    ∃ wbits bs v r, readWBITS (bits input) = some (wbits, bs) ∧
      readMetaBlock (windowSize wbits) ⟨[], 0, initialDistances⟩ bs = some (v, r) := by
  unfold decode at h
  obtain ⟨⟨wbits, bs⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨st, bs1⟩, h2, h⟩ := bind_some h
  simp only [readMetaBlocks, readMetaBlocksWith] at h2
  obtain ⟨⟨v, r⟩, h3, _⟩ := bind_some h2
  exact ⟨wbits, bs, v, r, h1, h3⟩

/-! ### Block types -/

/-- What a meta-block header gives a category: 1 to 256 block types, and a block type code over its
alphabet if there are at least 2. -/
def BlockCategory.Wf (c : BlockCategory) : Prop :=
  1 ≤ c.n ∧ c.n ≤ 256 ∧ (2 ≤ c.n → c.typeCode.Symbols (blockTypeAlphabetSize c.n))

/-- A category's block types are within its number of block types. -/
def BlockState.Wf (c : BlockCategory) (st : BlockState) : Prop :=
  (2 ≤ c.n → st.types.prev < c.n) ∧ st.types.cur < c.n ∧ ∀ t ∈ st.seen, t < c.n

theorem readBlockCategory_wf {bs r : List Bool} {c : BlockCategory}
    (h : readBlockCategory bs = some (c, r)) : c.Wf := by
  unfold readBlockCategory at h
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have hr := readVarLen_range h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨hr.1, hr.2, by simp only; omega⟩
  obtain ⟨⟨tc, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cc, bs3⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨fc, bs4⟩, _, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨hr.1, hr.2, fun _ => readPrefixCode_symbols h2⟩

theorem readMetaBlockHeader_wf {bs r : List Bool} {m : MetaBlockHeader}
    (h : readMetaBlockHeader bs = some (m, r)) : m.literal.Wf ∧ m.insertCopy.Wf ∧ m.distance.Wf := by
  unfold readMetaBlockHeader at h
  obtain ⟨⟨c1, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c2, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c3, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨np, bs4⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨nd, bs5⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ms, bs6⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨tl, ml⟩, bs7⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨td, md⟩, bs8⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cl, bs9⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ci, bs10⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cd, bs11⟩, _, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨readBlockCategory_wf h1, readBlockCategory_wf h2, readBlockCategory_wf h3⟩

theorem BlockState.initial_wf {c : BlockCategory} (hc : c.Wf) : (BlockState.initial c).Wf c := by
  refine ⟨fun h2 => ?_, ?_, ?_⟩
  · simp only [BlockState.initial, initialBlockTypes]
    omega
  · simp only [BlockState.initial, initialBlockTypes]
    exact hc.1
  · intro t ht
    simp only [BlockState.initial, List.mem_singleton] at ht
    have := hc.1
    omega

theorem nextElement_wf {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
    (hc : c.Wf) (hs : st.Wf c) (h : nextElement c st bs = some (st', r)) : st'.Wf c := by
  unfold nextElement at h
  split at h
  · split at h
    · simp at h
    · rename_i hn
      have h2 : 2 ≤ c.n := by omega
      obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨cnt, bs2⟩, _, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      unfold readBlockType at h1
      obtain ⟨⟨sym, bs3⟩, h3, h1⟩ := bind_some h1
      dsimp only at h1
      split at h1
      · simp at h1
      · simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        have hsym := decodeSymbol_lt (hc.2.2 h2) h3
        have hcur := nextBlockType_lt (hs.1 h2) hs.2.1 hsym
        refine ⟨fun _ => hs.2.1, hcur, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hcur
        · exact hs.2.2 u hu
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hs

theorem readLiterals_wf (m : MetaBlockHeader) (hc : m.literal.Wf) : ∀ (n : Nat) (st : BlockState)
    (output : List Nat) (bs : List Bool) (st' : BlockState) (o : List Nat) (r : List Bool),
    st.Wf m.literal → readLiterals m n st output bs = some (st', o, r) → st'.Wf m.literal
  | 0, _, _, _, _, _, _, hs, hr => by
    simp only [readLiterals, Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    exact hs
  | n + 1, st, output, bs, st', o, r, hs, hr => by
    simp only [readLiterals] at hr
    obtain ⟨⟨st1, bs1⟩, h1, hr⟩ := bind_some hr
    dsimp only at hr
    obtain ⟨mode, _, hr⟩ := bind_some hr
    obtain ⟨index, _, hr⟩ := bind_some hr
    obtain ⟨code, _, hr⟩ := bind_some hr
    obtain ⟨⟨byte, bs2⟩, _, hr⟩ := bind_some hr
    dsimp only at hr
    exact readLiterals_wf m hc n _ _ bs2 st' o r (nextElement_wf hc hs h1) hr

theorem readCommandDistance_wf {m : MetaBlockHeader} {st : BlockState} {d : Distances}
    {c clen : Nat} {bs r : List Bool} {v : BlockState × Nat × Nat} (hc : m.distance.Wf)
    (hs : st.Wf m.distance) (h : readCommandDistance m st d c clen bs = some (v, r)) :
    v.1.Wf m.distance := by
  unfold readCommandDistance at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  · obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨⟨⟨dcode, dist⟩, bs2⟩, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact nextElement_wf hc hs h1

theorem copyCommand_blocks {w clen dcode d : Nat} {s s' : CommandState}
    (h : copyCommand w s clen dcode d = some s') :
    s'.insertCopy = s.insertCopy ∧ s'.literal = s.literal ∧ s'.distance = s.distance := by
  unfold copyCommand at h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_some h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact ⟨rfl, rfl, rfl⟩
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact ⟨rfl, rfl, rfl⟩

theorem readCommand_wf {w : Nat} {m : MetaBlockHeader} {s s' : CommandState} {bs r : List Bool}
    (hm : m.literal.Wf ∧ m.insertCopy.Wf ∧ m.distance.Wf)
    (hs : s.literal.Wf m.literal ∧ s.insertCopy.Wf m.insertCopy ∧ s.distance.Wf m.distance)
    (h : readCommand w m s bs = some (s', r)) :
    s'.literal.Wf m.literal ∧ s'.insertCopy.Wf m.insertCopy ∧ s'.distance.Wf m.distance := by
  unfold readCommand at h
  obtain ⟨⟨ic, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨code, _, h⟩ := bind_some h
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  have wI := nextElement_wf hm.2.1 hs.2.1 h1
  have wL := readLiterals_wf m hm.1 _ _ _ _ _ _ _ hs.1 h3
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨wL, wI, hs.2.2⟩
  · obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, h4, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have wD := readCommandDistance_wf hm.2.2 hs.2.2 h4
    obtain ⟨e1, e2, e3⟩ := copyCommand_blocks h5
    rw [e1, e2, e3]
    exact ⟨wL, wI, wD⟩

theorem readCommands_wf (w : Nat) (m : MetaBlockHeader)
    (hm : m.literal.Wf ∧ m.insertCopy.Wf ∧ m.distance.Wf) : ∀ (fuel : Nat) (s s' : CommandState)
    (bs r : List Bool),
    (s.literal.Wf m.literal ∧ s.insertCopy.Wf m.insertCopy ∧ s.distance.Wf m.distance) →
    readCommands w m fuel s bs = some (s', r) →
    s'.literal.Wf m.literal ∧ s'.insertCopy.Wf m.insertCopy ∧ s'.distance.Wf m.distance
  | 0, _, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | f + 1, s, s', bs, r, hs, h => by
    simp only [readCommands, readCommandsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hs
    obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    exact readCommands_wf w m hm f s1 s' bs1 r (readCommand_wf hm hs h1) h

/-- The types `seen` are the first block's 0 (§6). -/
theorem BlockState.initial_seen (c : BlockCategory) :
    (BlockState.initial c).seen = [0] ∧ (BlockState.initial c).types.cur = 0 :=
  ⟨rfl, rfl⟩

/-- Each block switch adds the block type it read to the types `seen`, and nothing else does (§6). -/
theorem nextElement_seen {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
    (h : nextElement c st bs = some (st', r)) :
    (st'.seen = st.seen ∧ st'.types = st.types) ∨
      ∃ b, readBlockType c.n c.typeCode st.types bs = some (st'.types, b) ∧
        st'.seen = st'.types.cur :: st.seen := by
  unfold nextElement at h
  split at h
  · split at h
    · simp at h
    · obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨cnt, bs2⟩, _, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Or.inr ⟨bs1, h1, rfl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Or.inl ⟨rfl, rfl⟩

/-- If every block type of a category occurred, and all are within its number of block types, the types
are exactly [0..n-1], and that number is the largest plus one (§6). -/
theorem usesEveryType_largest {c : BlockCategory} {st : BlockState}
    (hw : ∀ t ∈ st.seen, t < c.n) (hu : usesEveryType c st = true) :
    (∀ t, t < c.n → t ∈ st.seen) ∧ ∀ t ∈ st.seen, t + 1 ≤ c.n := by
  refine ⟨?_, fun t ht => hw t ht⟩
  intro t ht
  have := List.all_eq_true.mp hu t (List.mem_range.mpr ht)
  simpa using this

/-- In a valid compressed meta-block, each category's block types are exactly [0..n-1], so its number of block
types is the largest plus one, and every block type is at most 255 (§2, §6). -/
theorem readCompressed_blockTypes {w mlen : Nat} {st st' : StreamState} {bs r : List Bool}
    (h : readCompressed w st mlen bs = some (st', r)) :
    ∃ (m : MetaBlockHeader) (b1 : List Bool) (s : CommandState),
      readMetaBlockHeader bs = some (m, b1) ∧
      readCommands w m
        (commandMeasure ⟨st.output, st.produced, st.distances, mlen, .initial m.insertCopy,
          .initial m.literal, .initial m.distance⟩ b1 + 1)
        ⟨st.output, st.produced, st.distances, mlen, .initial m.insertCopy,
          .initial m.literal, .initial m.distance⟩ b1 = some (s, r) ∧
      st' = ⟨s.output, s.produced, s.distances⟩ ∧
      ((∀ t, t < m.literal.n → t ∈ s.literal.seen) ∧
        ∀ t ∈ s.literal.seen, t + 1 ≤ m.literal.n ∧ t < 256) ∧
      ((∀ t, t < m.insertCopy.n → t ∈ s.insertCopy.seen) ∧
        ∀ t ∈ s.insertCopy.seen, t + 1 ≤ m.insertCopy.n ∧ t < 256) ∧
      ((∀ t, t < m.distance.n → t ∈ s.distance.seen) ∧
        ∀ t ∈ s.distance.seen, t + 1 ≤ m.distance.n ∧ t < 256) := by
  unfold readCompressed at h
  obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨s, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have hm := readMetaBlockHeader_wf h1
  have hs := readCommands_wf w m hm _ _ s _ bs2 ⟨BlockState.initial_wf hm.1,
    BlockState.initial_wf hm.2.1, BlockState.initial_wf hm.2.2⟩ h2
  split at h
  · rename_i hall
    simp only [Bool.and_eq_true] at hall
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨m, bs1, s, h1, h2, rfl, ?_, ?_, ?_⟩
    · have hL := usesEveryType_largest hs.1.2.2 hall.1.1
      exact ⟨hL.1, fun t ht => ⟨hL.2 t ht, by have := hs.1.2.2 t ht; have := hm.1.2.1; omega⟩⟩
    · have hI := usesEveryType_largest hs.2.1.2.2 hall.1.2
      exact ⟨hI.1, fun t ht => ⟨hI.2 t ht, by have := hs.2.1.2.2 t ht; have := hm.2.1.2.1; omega⟩⟩
    · have hD := usesEveryType_largest hs.2.2.2.2 hall.2
      exact ⟨hD.1, fun t ht => ⟨hD.2 t ht, by have := hs.2.2.2.2 t ht; have := hm.2.2.2.1; omega⟩⟩
  · simp at h

/-! ### More input changes nothing -/

theorem readInt_ext: ∀ (n : Nat) (p q : List Bool) (v : Nat) (r : List Bool),
    readInt n p = some (v, r) → readInt n (p ++ q) = some (v, r ++ q)
  | 0, p, q, v, r, h => by
    simp only [readInt, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | _ + 1, [], _, _, _, h => by simp [readInt] at h
  | n + 1, b :: p, q, v, r, h => by
    simp only [readInt] at h
    cases hr : readInt n p with
    | none => simp [hr] at h
    | some x =>
      obtain ⟨u, r'⟩ := x
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [List.cons_append, readInt, readInt_ext n p q u r' hr]

theorem readInt_none : ∀ (n : Nat) (p : List Bool), readInt n p = none → p.length < n
  | 0, _, h => by simp [readInt] at h
  | _ + 1, [], _ => by simp
  | n + 1, _ :: p, h => by
    simp only [readInt] at h
    cases hr : readInt n p with
    | none =>
      have := readInt_none n p hr
      simp only [List.length_cons]
      omega
    | some x => simp [hr] at h

theorem mod_step {x P : Nat} (u : Nat) (hx : x < 2) (hP : 0 < P) :
    (x + 2 * u) % (2 * P) = x + 2 * (u % P) := by
  have e : x + 2 * u = (x + 2 * (u % P)) + (2 * P) * (u / P) := by
    have := Nat.div_add_mod u P
    rw [Nat.mul_assoc]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  have := Nat.mod_lt u hP
  omega

theorem readInt_mod : ∀ (m n : Nat) (bs : List Bool) (v u : Nat) (r r' : List Bool), m ≤ n →
    readInt n bs = some (v, r) → readInt m bs = some (u, r') → v % 2 ^ m = u
  | 0, _, _, v, u, _, _, _, _, h2 => by
    simp only [readInt, Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h2.1, Nat.pow_zero, Nat.mod_one]
  | _ + 1, 0, _, _, _, _, _, hle, _, _ => by omega
  | _ + 1, _ + 1, [], _, _, _, _, _, h1, _ => by simp [readInt] at h1
  | m + 1, n + 1, b :: bs, v, u, r, r', hle, h1, h2 => by
    simp only [readInt] at h1 h2
    cases hn : readInt n bs with
    | none => simp [hn] at h1
    | some x =>
      cases hm : readInt m bs with
      | none => simp [hm] at h2
      | some y =>
        obtain ⟨v', r1⟩ := x
        obtain ⟨u', r2⟩ := y
        simp only [hn, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
        simp only [hm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
        obtain ⟨rfl, -⟩ := h1
        obtain ⟨rfl, -⟩ := h2
        have ih := readInt_mod m n bs v' u' r1 r2 (by omega) hn hm
        have hb : b.toNat < 2 := by cases b <;> decide
        rw [Nat.pow_succ', mod_step v' hb (Nat.two_pow_pos m), ih]

/-- One row of a variable-length code's table, tried on the bits. -/
def tableStep (bs : List Bool) : Nat × Nat × Nat → Option (Nat × List Bool) :=
  fun (sym, n, printed) =>
    match readInt n bs with
    | some (v, rest) => if v = printed then some (sym, rest) else none
    | none => none

theorem tableStep_ext{p : List Bool} (q : List Bool) {f : Nat × Nat × Nat} {a : Nat}
    {r : List Bool} (h : tableStep p f = some (a, r)) : tableStep (p ++ q) f = some (a, r ++ q) := by
  obtain ⟨s, n, pr⟩ := f
  simp only [tableStep] at h ⊢
  cases hr : readInt n p with
  | none => simp [hr] at h
  | some x =>
    obtain ⟨v, rest⟩ := x
    simp only [hr] at h
    rw [readInt_ext _ _ _ _ _ hr]
    dsimp only
    split at h
    · rename_i he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [he]
    · simp at h

/-- A table of prefix-free rows gives the same row however much input follows. -/
theorem table_ext: ∀ (T : List (Nat × Nat × Nat)),
    (∀ e ∈ T, ∀ f ∈ T, e ≠ f → e.2.1 ≤ f.2.1 → f.2.2 % 2 ^ e.2.1 ≠ e.2.2) →
    ∀ (p q : List Bool) (a : Nat) (r : List Bool),
    T.findSome? (tableStep p) = some (a, r) → T.findSome? (tableStep (p ++ q)) = some (a, r ++ q)
  | [], _, _, _, _, _, h => by simp at h
  | f :: T, hpf, p, q, a, r, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases hf : tableStep p f with
    | some x =>
      obtain ⟨a', r'⟩ := x
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [tableStep_ext q hf]
    | none =>
      rw [hf] at h
      dsimp only at h
      have hsub : ∀ e ∈ T, ∀ g ∈ T, e ≠ g → e.2.1 ≤ g.2.1 → g.2.2 % 2 ^ e.2.1 ≠ e.2.2 :=
        fun e he g hg => hpf e (List.mem_cons_of_mem _ he) g (List.mem_cons_of_mem _ hg)
      have hnone : tableStep (p ++ q) f = none := by
        obtain ⟨e, he, hes⟩ := List.exists_of_findSome?_eq_some h
        have hne : e ≠ f := by
          intro heq
          rw [heq, hf] at hes
          simp at hes
        have hpf' := hpf e (List.mem_cons_of_mem _ he) f List.mem_cons_self hne
        obtain ⟨es, en, ep⟩ := e
        obtain ⟨fs, fn, fp⟩ := f
        simp only at hpf'
        have hee : readInt en p = some (ep, r) := by
          simp only [tableStep] at hes
          split at hes
          · rename_i v rest hr
            split at hes
            · rename_i hv
              simp only [Option.some.injEq, Prod.mk.injEq] at hes
              rw [hr, hv, hes.2]
            · simp at hes
          · simp at hes
        simp only [tableStep] at hf ⊢
        cases hfr : readInt fn p with
        | some x =>
          obtain ⟨v, rest⟩ := x
          simp only [hfr] at hf
          rw [readInt_ext _ _ _ _ _ hfr]
          dsimp only
          split at hf
          · simp at hf
          · rename_i hv
            simp [hv]
        | none =>
          have hshort := readInt_none _ _ hfr
          have hlen := readInt_length _ _ _ _ hee
          cases hq : readInt fn (p ++ q) with
          | none => rfl
          | some x =>
            obtain ⟨v, rest⟩ := x
            dsimp only
            have hle : en ≤ fn := by omega
            have hmod := readInt_mod en fn (p ++ q) v ep rest (r ++ q) hle hq
              (readInt_ext _ _ _ _ _ hee)
            refine ite_eq_right (fun hv => hpf' hle ?_)
            rw [← hv]
            exact hmod
      rw [hnone]
      exact table_ext T hsub p q a r h

/-- WBITS read from some bits reads the same however much input follows. -/
theorem readWBITS_ext {p : List Bool} (q : List Bool) {w : Nat} {r : List Bool}
    (h : readWBITS p = some (w, r)) : readWBITS (p ++ q) = some (w, r ++ q) :=
  table_ext wbitsCode wbitsCode_prefixFree p q w r h

/-- A code length of a code length symbol reads the same however much input follows. -/
theorem readCodeLengthCodeLength_ext {p : List Bool} (q : List Bool) {v : Nat} {r : List Bool}
    (h : readCodeLengthCodeLength p = some (v, r)) :
    readCodeLengthCodeLength (p ++ q) = some (v, r ++ q) :=
  table_ext codeLengthCodeLengthCode codeLengthCodeLengthCode_prefixFree p q v r h

theorem readCode_ext{n : Nat} {p : List Bool} (q : List Bool) {c : Nat} {r : List Bool}
    (h : readCode n p = some (c, r)) : readCode n (p ++ q) = some (c, r ++ q) := by
  obtain ⟨u, rfl, hu⟩ := readCode_split n p c r h
  rw [List.append_assoc]
  exact readCode_append n u c (r ++ q) hu

theorem decodeLengths_ext(lens : List Nat) : ∀ (k len : Nat) (p q : List Bool) (s : Nat)
    (r : List Bool), decodeLengths lens p len k = some (s, r) →
    decodeLengths lens (p ++ q) len k = some (s, r ++ q)
  | 0, _, _, _, _, _, h => by simp [decodeLengths] at h
  | k + 1, len, p, q, s, r, h => by
    simp only [decodeLengths] at h ⊢
    cases hr : readCode len p with
    | none => rw [hr] at h; simp at h
    | some x =>
      obtain ⟨c, rest⟩ := x
      rw [hr] at h
      rw [readCode_ext q hr]
      dsimp only at h ⊢
      by_cases hle : nextCode lens len ≤ c
      · rw [ite_eq_left hle] at h ⊢
        cases hs : (symbolsOfLength lens len)[c - nextCode lens len]? with
        | none =>
          rw [hs] at h
          dsimp only at h ⊢
          exact decodeLengths_ext lens k (len + 1) p q s r h
        | some sym =>
          rw [hs] at h
          dsimp only at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
          exact ⟨h.1, by rw [h.2]⟩
      · rw [ite_eq_right hle] at h ⊢
        exact decodeLengths_ext lens k (len + 1) p q s r h

theorem decodeSymbol_ext{c : PrefixCode} {p : List Bool} (q : List Bool) {s : Nat}
    {r : List Bool} (h : decodeSymbol c p = some (s, r)) :
    decodeSymbol c (p ++ q) = some (s, r ++ q) := by
  cases c with
  | single sym =>
    simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | canonical lens => exact decodeLengths_ext lens 15 1 p q s r h

theorem readSimpleSymbols_ext(size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (p q : List Bool) (out : List Nat) (r : List Bool),
    readSimpleSymbols size bits n syms p = some (out, r) →
    readSimpleSymbols size bits n syms (p ++ q) = some (out, r ++ q)
  | 0, _, p, q, _, r, h => by
    simp only [readSimpleSymbols, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | n + 1, syms, p, q, out, r, h => by
    simp only [readSimpleSymbols] at h ⊢
    obtain ⟨⟨v, bs1⟩, h1, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h1]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i hc
      rw [ite_eq_right hc]
      exact readSimpleSymbols_ext size bits n _ bs1 q out r h

theorem readSimple_ext{size : Nat} {p : List Bool} (q : List Bool) {c : PrefixCode}
    {r : List Bool} (h : readSimple size p = some (c, r)) :
    readSimple size (p ++ q) = some (c, r ++ q) := by
  unfold readSimple at h ⊢
  obtain ⟨⟨nsym, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨syms, bs2⟩, h2, h⟩ := bind_some h
  rw [readSimpleSymbols_ext _ _ _ _ _ q _ _ h2]
  dsimp only [bind, Option.bind] at h ⊢
  match syms, h with
  | [], h => simp at h
  | [_], h =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | [_, _], h =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | [_, _, _], h =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | [_, _, _, _], h =>
    dsimp only at h ⊢
    obtain ⟨⟨ts, bs3⟩, h3, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h3]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i hts
      rw [ite_eq_left hts]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hts
      rw [ite_eq_right hts]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
  | _ :: _ :: _ :: _ :: _ :: _, h => simp at h

theorem readCodeLengthCodeLengths_ext: ∀ (order : List Nat) (acc : List (Nat × Nat))
    (sum : Nat) (p q : List Bool) (pairs : List (Nat × Nat)) (r : List Bool),
    readCodeLengthCodeLengths order acc sum p = some (pairs, r) →
    readCodeLengthCodeLengths order acc sum (p ++ q) = some (pairs, r ++ q)
  | [], _, _, _, _, _, _, h => by
    simp only [readCodeLengthCodeLengths] at h ⊢
    split at h
    · rename_i hone
      rw [ite_eq_left hone]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · simp at h
  | sym :: order, acc, sum, p, q, pairs, r, h => by
    simp only [readCodeLengthCodeLengths] at h ⊢
    obtain ⟨⟨len, bs1⟩, h1, h⟩ := bind_some h
    have h1' : readCodeLengthCodeLength (p ++ q) = some (len, bs1 ++ q) :=
      table_ext codeLengthCodeLengthCode codeLengthCodeLengthCode_prefixFree p q len bs1 h1
    rw [h1']
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i h0
      rw [ite_eq_left h0]
      exact readCodeLengthCodeLengths_ext order _ _ bs1 q pairs r h
    · rename_i h0
      rw [ite_eq_right h0]
      split at h
      · rename_i hs
        rw [ite_eq_left hs]
        simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
        exact ⟨h.1, by rw [h.2]⟩
      · rename_i hs
        rw [ite_eq_right hs]
        split at h
        · simp at h
        · rename_i hl
          rw [ite_eq_right hl]
          exact readCodeLengthCodeLengths_ext order _ _ bs1 q pairs r h

theorem readSymbolLengths_ext(size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
    (st : LengthState) (p q : List Bool) (lens : List Nat) (r : List Bool),
    readSymbolLengths size clc fuel st p = some (lens, r) →
    readSymbolLengths size clc fuel st (p ++ q) = some (lens, r ++ q)
  | 0, _, _, _, _, _, h => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, p, q, lens, r, h => by
    simp only [readSymbolLengths, readSymbolLengthsWith] at h ⊢
    split at h
    · rename_i hs
      rw [ite_eq_left hs]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hs
      rw [ite_eq_right hs]
      split at h
      · simp at h
      · rename_i hl
        rw [ite_eq_right hl]
        obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
        rw [decodeSymbol_ext q h1]
        dsimp only [bind, Option.bind] at h ⊢
        obtain ⟨⟨e, bs2⟩, h2, h⟩ := bind_some h
        rw [readInt_ext _ _ _ _ _ h2]
        dsimp only [bind, Option.bind] at h ⊢
        split at h
        · simp at h
        · rename_i h3
          rw [ite_eq_right h3]
          split at h
          · simp at h
          · rename_i h4
            rw [ite_eq_right h4]
            exact readSymbolLengths_ext size clc f _ bs2 q lens r h

theorem readPrefixCode_ext{size : Nat} {p : List Bool} (q : List Bool) {c : PrefixCode}
    {r : List Bool} (h : readPrefixCode size p = some (c, r)) :
    readPrefixCode size (p ++ q) = some (c, r ++ q) := by
  unfold readPrefixCode at h ⊢
  obtain ⟨⟨hskip, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hs
    rw [ite_eq_left hs]
    exact readSimple_ext q h
  · rename_i hs
    rw [ite_eq_right hs]
    unfold readComplex at h ⊢
    obtain ⟨⟨pairs, bs2⟩, h2, h⟩ := bind_some h
    rw [readCodeLengthCodeLengths_ext _ _ _ _ q _ _ h2]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨lens, bs3⟩, h3, h⟩ := bind_some h
    rw [readSymbolLengths_ext _ _ _ _ _ q _ _ h3]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readContextModes_ext: ∀ (n : Nat) (p q : List Bool) (modes : List Nat) (r : List Bool),
    readContextModes n p = some (modes, r) → readContextModes n (p ++ q) = some (modes, r ++ q)
  | 0, _, _, _, _, h => by
    simp only [readContextModes, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | n + 1, p, q, modes, r, h => by
    simp only [readContextModes] at h ⊢
    obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h1]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨ms, bs2⟩, h2, h⟩ := bind_some h
    rw [readContextModes_ext n bs1 q ms bs2 h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readContextMapValues_ext(rlemax : Nat) (code : PrefixCode) : ∀ (fuel left : Nat)
    (p q : List Bool) (vals : List Nat) (r : List Bool),
    readContextMapValues rlemax code fuel left p = some (vals, r) →
    readContextMapValues rlemax code fuel left (p ++ q) = some (vals, r ++ q)
  | 0, _, _, _, _, _, h => by simp [readContextMapValues, readContextMapValuesWith] at h
  | f + 1, left, p, q, vals, r, h => by
    simp only [readContextMapValues, readContextMapValuesWith] at h ⊢
    split at h
    · rename_i hl
      rw [ite_eq_left hl]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hl
      rw [ite_eq_right hl]
      obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
      rw [decodeSymbol_ext q h1]
      dsimp only [bind, Option.bind] at h ⊢
      cases hv : contextMapValue rlemax sym with
      | some v =>
        rw [hv] at h
        dsimp only at h ⊢
        obtain ⟨⟨vs, bs2⟩, h2, h⟩ := bind_some h
        have h2' := readContextMapValues_ext rlemax code f _ bs1 q vs bs2 h2
        simp only [readContextMapValues] at h2'
        rw [h2']
        dsimp only [bind, Option.bind]
        simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
        exact ⟨h.1, by rw [h.2]⟩
      | none =>
        rw [hv] at h
        dsimp only at h ⊢
        obtain ⟨⟨e, bs2⟩, h2, h⟩ := bind_some h
        rw [readInt_ext _ _ _ _ _ h2]
        dsimp only [bind, Option.bind] at h ⊢
        split at h
        · simp at h
        · rename_i hrun
          rw [ite_eq_right hrun]
          obtain ⟨⟨vs, bs3⟩, h3, h⟩ := bind_some h
          have h3' := readContextMapValues_ext rlemax code f _ bs2 q vs bs3 h3
          simp only [readContextMapValues] at h3'
          rw [h3']
          dsimp only [bind, Option.bind]
          simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
          exact ⟨h.1, by rw [h.2]⟩

theorem readRLEMAX_ext{p : List Bool} (q : List Bool) {v : Nat} {r : List Bool}
    (h : readRLEMAX p = some (v, r)) : readRLEMAX (p ++ q) = some (v, r ++ q) := by
  unfold readRLEMAX at h ⊢
  obtain ⟨⟨flag, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hf
    rw [ite_eq_left hf]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hf
    rw [ite_eq_right hf]
    obtain ⟨⟨x, bs2⟩, h2, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readContextMap_ext{size ntrees : Nat} {p : List Bool} (q : List Bool)
    {cmap : List Nat} {r : List Bool} (h : readContextMap size ntrees p = some (cmap, r)) :
    readContextMap size ntrees (p ++ q) = some (cmap, r ++ q) := by
  unfold readContextMap at h ⊢
  obtain ⟨⟨rlemax, bs1⟩, h1, h⟩ := bind_some h
  rw [readRLEMAX_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨code, bs2⟩, h2, h⟩ := bind_some h
  rw [readPrefixCode_ext q h2]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨vals, bs3⟩, h3, h⟩ := bind_some h
  rw [readContextMapValues_ext _ _ _ _ _ q _ _ h3]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨imtf, bs4⟩, h4, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h4]
  dsimp only [bind, Option.bind] at h ⊢
  generalize (if imtf = 0 then vals else inverseMoveToFront vals) = final at h ⊢
  split at h
  · rename_i hall
    rw [ite_eq_left hall]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · simp at h

theorem readVarLen_ext{p : List Bool} (q : List Bool) {v : Nat} {r : List Bool}
    (h : readVarLen p = some (v, r)) : readVarLen (p ++ q) = some (v, r ++ q) := by
  unfold readVarLen at h ⊢
  obtain ⟨⟨first, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hf
    rw [ite_eq_left hf]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hf
    rw [ite_eq_right hf]
    obtain ⟨⟨n, bs2⟩, h2, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h2]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i hn
      rw [ite_eq_left hn]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hn
      rw [ite_eq_right hn]
      obtain ⟨⟨x, bs3⟩, h3, h⟩ := bind_some h
      rw [readInt_ext _ _ _ _ _ h3]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩

theorem readBlockCount_ext{code : PrefixCode} {p : List Bool} (q : List Bool) {v : Nat}
    {r : List Bool} (h : readBlockCount code p = some (v, r)) :
    readBlockCount code (p ++ q) = some (v, r ++ q) := by
  unfold readBlockCount at h ⊢
  obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
  rw [decodeSymbol_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨bits, lowest, highest⟩, h2, h⟩ := bind_some h
  rw [h2]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨extra, bs2⟩, h3, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h3]
  dsimp only [bind, Option.bind]
  simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by rw [h.2]⟩

theorem readBlockType_ext{n : Nat} {code : PrefixCode} {bt bt' : BlockTypes} {p : List Bool}
    (q : List Bool) {r : List Bool} (h : readBlockType n code bt p = some (bt', r)) :
    readBlockType n code bt (p ++ q) = some (bt', r ++ q) := by
  unfold readBlockType at h ⊢
  obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
  rw [decodeSymbol_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · simp at h
  · rename_i hc
    rw [ite_eq_right hc]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readBlockCategory_ext{p : List Bool} (q : List Bool) {c : BlockCategory}
    {r : List Bool} (h : readBlockCategory p = some (c, r)) :
    readBlockCategory (p ++ q) = some (c, r ++ q) := by
  unfold readBlockCategory at h ⊢
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  rw [readVarLen_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hn
    rw [ite_eq_right hn]
    obtain ⟨⟨tc, bs2⟩, h2, h⟩ := bind_some h
    rw [readPrefixCode_ext q h2]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨cc, bs3⟩, h3, h⟩ := bind_some h
    rw [readPrefixCode_ext q h3]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨fc, bs4⟩, h4, h⟩ := bind_some h
    rw [readBlockCount_ext q h4]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readTreesAndMap_ext{size : Nat} {p : List Bool} (q : List Bool) {v : Nat × List Nat}
    {r : List Bool} (h : readTreesAndMap size p = some (v, r)) :
    readTreesAndMap size (p ++ q) = some (v, r ++ q) := by
  unfold readTreesAndMap at h ⊢
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  rw [readVarLen_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hn
    rw [ite_eq_left hn]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hn
    rw [ite_eq_right hn]
    obtain ⟨⟨m, bs2⟩, h2, h⟩ := bind_some h
    rw [readContextMap_ext q h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readPrefixCodes_ext(size : Nat) : ∀ (n : Nat) (p q : List Bool)
    (codes : List PrefixCode) (r : List Bool),
    readPrefixCodes size n p = some (codes, r) → readPrefixCodes size n (p ++ q) = some (codes, r ++ q)
  | 0, _, _, _, _, h => by
    simp only [readPrefixCodes, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | n + 1, p, q, codes, r, h => by
    simp only [readPrefixCodes] at h ⊢
    obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
    rw [readPrefixCode_ext q h1]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨cs, bs2⟩, h2, h⟩ := bind_some h
    rw [readPrefixCodes_ext size n bs1 q cs bs2 h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readMetaBlockHeader_ext{p : List Bool} (q : List Bool) {m : MetaBlockHeader}
    {r : List Bool} (h : readMetaBlockHeader p = some (m, r)) :
    readMetaBlockHeader (p ++ q) = some (m, r ++ q) := by
  unfold readMetaBlockHeader at h ⊢
  obtain ⟨⟨c1, bs1⟩, h1, h⟩ := bind_some h
  rw [readBlockCategory_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨c2, bs2⟩, h2, h⟩ := bind_some h
  rw [readBlockCategory_ext q h2]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨c3, bs3⟩, h3, h⟩ := bind_some h
  rw [readBlockCategory_ext q h3]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨np, bs4⟩, h4, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h4]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨nd, bs5⟩, h5, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h5]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ms, bs6⟩, h6, h⟩ := bind_some h
  rw [readContextModes_ext _ _ q _ _ h6]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨⟨tl, ml⟩, bs7⟩, h7, h⟩ := bind_some h
  rw [readTreesAndMap_ext q h7]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨⟨td, md⟩, bs8⟩, h8, h⟩ := bind_some h
  rw [readTreesAndMap_ext q h8]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨cl, bs9⟩, h9, h⟩ := bind_some h
  rw [readPrefixCodes_ext _ _ _ q _ _ h9]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ci, bs10⟩, h10, h⟩ := bind_some h
  rw [readPrefixCodes_ext _ _ _ q _ _ h10]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨cd, bs11⟩, h11, h⟩ := bind_some h
  rw [readPrefixCodes_ext _ _ _ q _ _ h11]
  dsimp only [bind, Option.bind]
  simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by rw [h.2]⟩

theorem nextElement_ext{c : BlockCategory} {st st' : BlockState} {p : List Bool}
    (q : List Bool) {r : List Bool} (h : nextElement c st p = some (st', r)) :
    nextElement c st (p ++ q) = some (st', r ++ q) := by
  unfold nextElement at h ⊢
  split at h
  · rename_i h0
    rw [ite_eq_left h0]
    split at h
    · simp at h
    · rename_i hn
      rw [ite_eq_right hn]
      obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
      rw [readBlockType_ext q h1]
      dsimp only [bind, Option.bind] at h ⊢
      obtain ⟨⟨cnt, bs2⟩, h2, h⟩ := bind_some h
      rw [readBlockCount_ext q h2]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
  · rename_i h0
    rw [ite_eq_right h0]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readLiterals_ext(m : MetaBlockHeader) : ∀ (n : Nat) (st : BlockState)
    (output : List Nat) (p q : List Bool) (st' : BlockState) (o : List Nat) (r : List Bool),
    readLiterals m n st output p = some (st', o, r) →
    readLiterals m n st output (p ++ q) = some (st', o, r ++ q)
  | 0, _, _, _, _, _, _, _, h => by
    simp only [readLiterals, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, h.2.1, by rw [h.2.2]⟩
  | n + 1, st, output, p, q, st', o, r, h => by
    simp only [readLiterals] at h ⊢
    obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    rw [nextElement_ext q h1]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨mode, hm, h⟩ := bind_some h
    rw [hm]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨index, hi, h⟩ := bind_some h
    rw [hi]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨code, hc, h⟩ := bind_some h
    rw [hc]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨byte, bs2⟩, h2, h⟩ := bind_some h
    rw [decodeSymbol_ext q h2]
    dsimp only [bind, Option.bind] at h ⊢
    exact readLiterals_ext m n _ _ bs2 q st' o r h

theorem readInsertCopy_ext{code : PrefixCode} {p : List Bool} (q : List Bool)
    {v : Nat × Nat × Nat} {r : List Bool} (h : readInsertCopy code p = some (v, r)) :
    readInsertCopy code (p ++ q) = some (v, r ++ q) := by
  unfold readInsertCopy at h ⊢
  obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
  rw [decodeSymbol_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ic, cc⟩, hc, h⟩ := bind_some h
  rw [hc]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ib, ibase, ihi⟩, hi, h⟩ := bind_some h
  rw [hi]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨cb, cbase, chi⟩, hj, h⟩ := bind_some h
  rw [hj]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ie, bs2⟩, h2, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h2]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨ce, bs3⟩, h3, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h3]
  dsimp only [bind, Option.bind]
  simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
  exact ⟨h.1, by rw [h.2]⟩

theorem readCommandDistance_ext{m : MetaBlockHeader} {st : BlockState} {d : Distances}
    {c clen : Nat} {p : List Bool} (q : List Bool) {v : BlockState × Nat × Nat} {r : List Bool}
    (h : readCommandDistance m st d c clen p = some (v, r)) :
    readCommandDistance m st d c clen (p ++ q) = some (v, r ++ q) := by
  unfold readCommandDistance at h ⊢
  split at h
  · rename_i hi
    rw [ite_eq_left hi]
    obtain ⟨dv, hd, h⟩ := bind_some h
    rw [hd]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hi
    rw [ite_eq_right hi]
    obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    rw [nextElement_ext q h1]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨index, hx, h⟩ := bind_some h
    rw [hx]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨code, hc, h⟩ := bind_some h
    rw [hc]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨⟨dcode, dist⟩, bs2⟩, h2, h⟩ := bind_some h
    have h2' : readDistance m.npostfix m.ndirect code d (bs1 ++ q) = some ((dcode, dist), bs2 ++ q) := by
      unfold readDistance at h2 ⊢
      obtain ⟨⟨sym, bs3⟩, h3, h2⟩ := bind_some h2
      rw [decodeSymbol_ext q h3]
      dsimp only [bind, Option.bind] at h2 ⊢
      obtain ⟨⟨e, bs4⟩, h4, h2⟩ := bind_some h2
      rw [readInt_ext _ _ _ _ _ h4]
      dsimp only [bind, Option.bind] at h2 ⊢
      obtain ⟨dv, hd, h2⟩ := bind_some h2
      rw [hd]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h2 ⊢
      exact ⟨h2.1, by rw [h2.2]⟩
    rw [h2']
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readCommand_ext{w : Nat} {m : MetaBlockHeader} {s s' : CommandState} {p : List Bool}
    (q : List Bool) {r : List Bool} (h : readCommand w m s p = some (s', r)) :
    readCommand w m s (p ++ q) = some (s', r ++ q) := by
  unfold readCommand at h ⊢
  obtain ⟨⟨ic, bs1⟩, h1, h⟩ := bind_some h
  rw [nextElement_ext q h1]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨code, hc, h⟩ := bind_some h
  rw [hc]
  dsimp only [bind, Option.bind] at h ⊢
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, h2, h⟩ := bind_some h
  rw [readInsertCopy_ext q h2]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · simp at h
  · rename_i hle
    rw [ite_eq_right hle]
    obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
    rw [readLiterals_ext _ _ _ _ _ q _ _ _ h3]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i h0
      rw [ite_eq_left h0]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i h0
      rw [ite_eq_right h0]
      obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, h4, h⟩ := bind_some h
      rw [readCommandDistance_ext q h4]
      dsimp only [bind, Option.bind] at h ⊢
      obtain ⟨s2, h5, h⟩ := bind_some h
      rw [h5]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩

theorem readCommands_ext(w : Nat) (m : MetaBlockHeader) : ∀ (fuel : Nat) (s s' : CommandState)
    (p q r : List Bool), readCommands w m fuel s p = some (s', r) →
    readCommands w m fuel s (p ++ q) = some (s', r ++ q)
  | 0, _, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | f + 1, s, s', p, q, r, h => by
    simp only [readCommands, readCommandsWith] at h ⊢
    split at h
    · rename_i h0
      rw [ite_eq_left h0]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i h0
      rw [ite_eq_right h0]
      obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
      rw [readCommand_ext q h1]
      dsimp only [bind, Option.bind] at h ⊢
      exact readCommands_ext w m f s1 s' bs1 q r h

theorem readCommands_mono (w : Nat) (m : MetaBlockHeader) : ∀ (f f' : Nat) (s s' : CommandState)
    (bs r : List Bool), f ≤ f' → readCommands w m f s bs = some (s', r) →
    readCommands w m f' s bs = some (s', r)
  | 0, _, _, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | _ + 1, 0, _, _, _, _, hle, _ => by omega
  | f + 1, f' + 1, s, s', bs, r, hle, h => by
    simp only [readCommands, readCommandsWith] at h ⊢
    split at h
    · rename_i h0
      rw [ite_eq_left h0]
      exact h
    · rename_i h0
      rw [ite_eq_right h0]
      obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
      rw [h1]
      dsimp only [bind, Option.bind] at h ⊢
      exact readCommands_mono w m f f' s1 s' bs1 r (by omega) h

private theorem bind_eq {α β : Type} {x : Option α} {f : α → Option β} {a : α} {y : β}
    (h : x = some a) (hf : f a = some y) : (x >>= f) = some y := by
  rw [h]
  exact hf

theorem commandMeasure_append (s : CommandState) (p q : List Bool) :
    commandMeasure s p ≤ commandMeasure s (p ++ q) := by
  unfold commandMeasure
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  simp

theorem readCompressed_ext{w mlen : Nat} {st st' : StreamState} {p : List Bool} (q : List Bool)
    {r : List Bool} (h : readCompressed w st mlen p = some (st', r)) :
    readCompressed w st mlen (p ++ q) = some (st', r ++ q) := by
  unfold readCompressed at h ⊢
  obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨s, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  refine bind_eq (readMetaBlockHeader_ext q h1) ?_
  dsimp only
  refine bind_eq (readCommands_mono _ _ _ _ _ _ _ _
    (Nat.add_le_add_right (commandMeasure_append _ bs1 q) 1)
    (readCommands_ext _ _ _ _ _ _ q _ h2)) ?_
  dsimp only
  split at h
  · rename_i hall
    rw [ite_eq_left hall]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · simp at h

theorem readFill_ext{p q r : List Bool} (hq : q.length % 8 = 0) (h : readFill p = some r) :
    readFill (p ++ q) = some (r ++ q) := by
  unfold readFill at h ⊢
  have hl : (p ++ q).length % 8 = p.length % 8 := by
    simp only [List.length_append]
    omega
  rw [hl]
  obtain ⟨⟨v, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hv
    rw [ite_eq_left hv]
    simp only [Option.some.injEq] at h ⊢
    rw [h]
  · simp at h

theorem readMetadata_ext{p q r : List Bool} (hq : q.length % 8 = 0)
    (h : readMetadata p = some r) : readMetadata (p ++ q) = some (r ++ q) := by
  unfold readMetadata at h ⊢
  obtain ⟨⟨res, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · simp at h
  · rename_i hres
    rw [ite_eq_right hres]
    obtain ⟨⟨mb, bs2⟩, h2, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h2]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨v, bs3⟩, h3, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h3]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · simp at h
    · rename_i hz
      rw [ite_eq_right hz]
      generalize (if mb = 0 then 0 else v + 1) = ml at h ⊢
      obtain ⟨bs4, h4, h⟩ := bind_some h
      rw [readFill_ext hq h4]
      dsimp only [bind, Option.bind] at h ⊢
      split at h
      · simp at h
      · rename_i hlen
        have hlen' : ¬ (bs4 ++ q).length < ml * 8 := by
          simp only [List.length_append]
          omega
        rw [ite_eq_right hlen']
        simp only [Option.some.injEq] at h ⊢
        rw [← h]
        exact List.drop_append_of_le_length (by omega)

theorem readBytes_ext: ∀ (n : Nat) (p q : List Bool) (bytes : List Nat) (r : List Bool),
    readBytes n p = some (bytes, r) → readBytes n (p ++ q) = some (bytes, r ++ q)
  | 0, _, _, _, _, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  | n + 1, p, q, bytes, r, h => by
    simp only [readBytes] at h ⊢
    obtain ⟨⟨b, bs1⟩, h1, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h1]
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨rest, bs2⟩, h2, h⟩ := bind_some h
    rw [readBytes_ext n bs1 q rest bs2 h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩

theorem readMetaBlockBody_ext{w : Nat} {st st' : StreamState} {islast : Bool}
    {p q r : List Bool} (hq : q.length % 8 = 0) (h : readMetaBlockBody w st islast p = some (st', r)) :
    readMetaBlockBody w st islast (p ++ q) = some (st', r ++ q) := by
  unfold readMetaBlockBody at h ⊢
  obtain ⟨⟨mn, bs1⟩, h1, h⟩ := bind_some h
  have h1' : readMNIBBLES (p ++ q) = some (mn, bs1 ++ q) := by
    unfold readMNIBBLES at h1 ⊢
    obtain ⟨⟨v, bs0⟩, h0, h1⟩ := bind_some h1
    rw [readInt_ext _ _ _ _ _ h0]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h1 ⊢
    exact ⟨h1.1, by rw [h1.2]⟩
  rw [h1']
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i h0
    rw [ite_eq_left h0]
    obtain ⟨bs2, h2, h⟩ := bind_some h
    rw [readMetadata_ext hq h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i h0
    rw [ite_eq_right h0]
    obtain ⟨⟨mlen, bs2⟩, h2, h⟩ := bind_some h
    have h2' : readMLEN mn (bs1 ++ q) = some (mlen, bs2 ++ q) := by
      unfold readMLEN at h2 ⊢
      obtain ⟨⟨v, bs0⟩, h3, h2⟩ := bind_some h2
      rw [readInt_ext _ _ _ _ _ h3]
      dsimp only [bind, Option.bind] at h2 ⊢
      split at h2
      · simp at h2
      · rename_i hz
        rw [ite_eq_right hz]
        simp only [Option.some.injEq, Prod.mk.injEq] at h2 ⊢
        exact ⟨h2.1, by rw [h2.2]⟩
    rw [h2']
    dsimp only [bind, Option.bind] at h ⊢
    obtain ⟨⟨iu, bs3⟩, h3, h⟩ := bind_some h
    have h3' : readIsUncompressed islast (bs2 ++ q) = some (iu, bs3 ++ q) := by
      unfold readIsUncompressed at h3 ⊢
      split at h3
      · rename_i hl
        rw [ite_eq_left hl]
        simp only [Option.some.injEq, Prod.mk.injEq] at h3 ⊢
        exact ⟨h3.1, by rw [h3.2]⟩
      · rename_i hl
        rw [ite_eq_right hl]
        exact readInt_ext _ _ _ _ _ h3
    rw [h3']
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i hu
      rw [ite_eq_left hu]
      obtain ⟨bs4, h4, h⟩ := bind_some h
      rw [readFill_ext hq h4]
      dsimp only [bind, Option.bind] at h ⊢
      obtain ⟨⟨bytes, bs5⟩, h5, h⟩ := bind_some h
      rw [readBytes_ext _ _ q _ _ h5]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hu
      rw [ite_eq_right hu]
      exact readCompressed_ext q h

theorem readMetaBlock_ext{w : Nat} {st : StreamState} {v : StreamState × Bool}
    {p q r : List Bool} (hq : q.length % 8 = 0) (h : readMetaBlock w st p = some (v, r)) :
    readMetaBlock w st (p ++ q) = some (v, r ++ q) := by
  unfold readMetaBlock at h ⊢
  obtain ⟨⟨islast, bs1⟩, h1, h⟩ := bind_some h
  rw [readInt_ext _ _ _ _ _ h1]
  dsimp only [bind, Option.bind] at h ⊢
  split at h
  · rename_i hl
    rw [ite_eq_left hl]
    obtain ⟨⟨st1, bs2⟩, h2, h⟩ := bind_some h
    rw [readMetaBlockBody_ext hq h2]
    dsimp only [bind, Option.bind]
    simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨h.1, by rw [h.2]⟩
  · rename_i hl
    rw [ite_eq_right hl]
    obtain ⟨⟨ie, bs2⟩, h2, h⟩ := bind_some h
    rw [readInt_ext _ _ _ _ _ h2]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i he
      rw [ite_eq_left he]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i he
      rw [ite_eq_right he]
      obtain ⟨⟨st1, bs3⟩, h3, h⟩ := bind_some h
      rw [readMetaBlockBody_ext hq h3]
      dsimp only [bind, Option.bind]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩

theorem readMetaBlocks_ext(w : Nat) : ∀ (fuel : Nat) (st st' : StreamState)
    (p q r : List Bool), q.length % 8 = 0 → readMetaBlocks w fuel st p = some (st', r) →
    readMetaBlocks w fuel st (p ++ q) = some (st', r ++ q)
  | 0, _, _, _, _, _, _, h => by simp [readMetaBlocks, readMetaBlocksWith] at h
  | f + 1, st, st', p, q, r, hq, h => by
    simp only [readMetaBlocks, readMetaBlocksWith] at h ⊢
    obtain ⟨⟨⟨st1, last⟩, bs1⟩, h1, h⟩ := bind_some h
    rw [readMetaBlock_ext hq h1]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i hl
      rw [ite_eq_left hl]
      simp only [Option.some.injEq, Prod.mk.injEq] at h ⊢
      exact ⟨h.1, by rw [h.2]⟩
    · rename_i hl
      rw [ite_eq_right hl]
      exact readMetaBlocks_ext w f st1 st' bs1 q r hq h

theorem readMetaBlocks_mono (w : Nat) : ∀ (f f' : Nat) (st st' : StreamState) (bs r : List Bool),
    f ≤ f' → readMetaBlocks w f st bs = some (st', r) → readMetaBlocks w f' st bs = some (st', r)
  | 0, _, _, _, _, _, _, h => by simp [readMetaBlocks, readMetaBlocksWith] at h
  | _ + 1, 0, _, _, _, _, hle, _ => by omega
  | f + 1, f' + 1, st, st', bs, r, hle, h => by
    simp only [readMetaBlocks, readMetaBlocksWith] at h ⊢
    obtain ⟨⟨⟨st1, last⟩, bs1⟩, h1, h⟩ := bind_some h
    rw [h1]
    dsimp only [bind, Option.bind] at h ⊢
    split at h
    · rename_i hl
      rw [ite_eq_left hl]
      exact h
    · rename_i hl
      rw [ite_eq_right hl]
      exact readMetaBlocks_mono w f f' st1 st' bs1 r (by omega) h

theorem bits_append (x t : List UInt8) : bits (x ++ t) = bits x ++ bits t := by
  simp [bits, List.flatMap_append]

theorem bits_length : ∀ t : List UInt8, (bits t).length = t.length * 8
  | [] => by simp [bits]
  | b :: t => by
    have ih := bits_length t
    simp only [bits, List.flatMap_cons, List.length_append, List.length_map, List.length_range,
      List.length_cons] at ih ⊢
    omega

/-- A stream that ends before its last meta-block completes is invalid: whatever is cut from the end of a
valid stream, what remains is rejected (§10). -/
theorem decode_truncated {x t : List UInt8} {y : List UInt8} (ht : t ≠ [])
    (h : decode (x ++ t) = some y) : decode x = none := by
  cases hx : decode x with
  | none => rfl
  | some y' =>
    exfalso
    have hlen := bits_length t
    have hq : (bits t).length % 8 = 0 := by omega
    have hpos : bits t ≠ [] := by
      intro he
      rw [he] at hlen
      cases t with
      | nil => exact ht rfl
      | cons _ _ =>
        simp only [List.length_nil, List.length_cons] at hlen
        omega
    unfold decode at hx h
    obtain ⟨⟨wbits, bs⟩, h1, hx⟩ := bind_some hx
    dsimp only at hx
    obtain ⟨⟨st, bs1⟩, h2, hx⟩ := bind_some hx
    dsimp only at hx
    obtain ⟨u, h3, _⟩ := bind_some hx
    rw [bits_append, readWBITS_ext _ h1] at h
    dsimp only [bind, Option.bind] at h
    have h2' := readMetaBlocks_mono _ _ ((bs ++ bits t).length + 1) _ _ _ _
      (by simp only [List.length_append]; omega) (readMetaBlocks_ext _ _ _ _ _ _ _ hq h2)
    rw [h2'] at h
    dsimp only [bind, Option.bind] at h
    obtain ⟨u', h4, _⟩ := bind_some h
    unfold readEnd at h3 h4
    obtain ⟨b2, h5, h3⟩ := bind_some h3
    split at h3
    · rename_i he
      have hb2 : b2 = [] := by simpa using he
      rw [readFill_ext hq h5] at h4
      dsimp only [bind, Option.bind] at h4
      rw [hb2, List.nil_append] at h4
      split at h4
      · rename_i he'
        exact hpos (by simpa using he')
      · simp at h4
    · simp at h3

end Brotli.Spec
