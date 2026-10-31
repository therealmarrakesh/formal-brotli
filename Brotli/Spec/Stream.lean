import Brotli.Spec.PrefixCode
import Brotli.Spec.Distance
import Brotli.Spec.InsertCopy
import Brotli.Spec.BlockSwitch
import Brotli.Spec.Context
import Brotli.Spec.Dictionary

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
private theorem readInt_length : ∀ (n : Nat) (bs : List Bool) (v : Nat) (r : List Bool),
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

private theorem readInt_le {n : Nat} {bs r : List Bool} {v : Nat} (h : readInt n bs = some (v, r)) :
    r.length ≤ bs.length := by
  have := readInt_length n bs v r h
  omega

private theorem decodeSymbol_le {c : PrefixCode} {bs r : List Bool} {s : Nat}
    (h : decodeSymbol c bs = some (s, r)) : r.length ≤ bs.length := by
  cases c with
  | single sym =>
    simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact Nat.le_refl _
  | canonical lens =>
    obtain ⟨_, _, w, _, _, _, _, rfl⟩ := decodeLengths_sound lens 15 1 bs s r (by decide) h
    simp

private theorem readSimpleSymbols_le (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
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

private theorem readSimple_le {size : Nat} {bs r : List Bool} {c : PrefixCode}
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

private theorem readCodeLengthCodeLength_le' {bs r : List Bool} {v : Nat}
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

private theorem readCodeLengthCodeLengths_le : ∀ (order : List Nat) (acc : List (Nat × Nat))
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

private theorem readSymbolLengths_le (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
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

private theorem readPrefixCode_le {size : Nat} {bs r : List Bool} {c : PrefixCode}
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

private theorem readContextModes_le : ∀ (n : Nat) (bs : List Bool) (modes : List Nat) (r : List Bool),
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

private theorem readContextMapValues_le (rlemax : Nat) (code : PrefixCode) : ∀ (fuel left : Nat)
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

private theorem readRLEMAX_le {bs r : List Bool} {v : Nat} (h : readRLEMAX bs = some (v, r)) :
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

private theorem readContextMap_le {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
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

private theorem readVarLen_le {bs r : List Bool} {v : Nat} (h : readVarLen bs = some (v, r)) :
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
private theorem readBlockCount_bound {code : PrefixCode} {bs r : List Bool} {v : Nat}
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

private theorem readBlockType_le {n : Nat} {code : PrefixCode} {bt bt' : BlockTypes}
    {bs r : List Bool} (h : readBlockType n code bt bs = some (bt', r)) : r.length ≤ bs.length := by
  unfold readBlockType at h
  obtain ⟨⟨sym, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact decodeSymbol_le h1

private theorem readBlockCategory_le {bs r : List Bool} {c : BlockCategory}
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

private theorem readTreesAndMap_le {size : Nat} {bs r : List Bool} {p : Nat × List Nat}
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

private theorem readPrefixCodes_le (size : Nat) : ∀ (n : Nat) (bs : List Bool)
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

private theorem readMetaBlockHeader_le {bs r : List Bool} {m : MetaBlockHeader}
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

private theorem nextElement_le {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
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
private theorem nextElement_measure {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
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

private theorem readLiterals_le (h : MetaBlockHeader) : ∀ (n : Nat) (st : BlockState)
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

private theorem readInsertCopy_le {code : PrefixCode} {bs r : List Bool} {v : Nat × Nat × Nat}
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

private theorem readCommandDistance_le {m : MetaBlockHeader} {st : BlockState} {d : Distances}
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

private theorem copyCommand_insertCopy {w clen dcode d : Nat} {s s' : CommandState}
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
private theorem readCommand_spec {w : Nat} {m : MetaBlockHeader} {s s' : CommandState}
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

private theorem readCommands_le (w : Nat) (m : MetaBlockHeader) : ∀ (fuel : Nat) (s s' : CommandState)
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

private theorem readCompressed_le {w mlen : Nat} {st st' : StreamState} {bs r : List Bool}
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

private theorem readFill_le {bs r : List Bool} (h : readFill bs = some r) : r.length ≤ bs.length := by
  unfold readFill at h
  obtain ⟨⟨v, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact readInt_le h1
  · simp at h

private theorem readMetadata_le {bs r : List Bool} (h : readMetadata bs = some r) :
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

private theorem readBytes_le : ∀ (n : Nat) (bs : List Bool) (bytes : List Nat) (r : List Bool),
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

private theorem readMetaBlockBody_le {w : Nat} {st st' : StreamState} {islast : Bool}
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

end Brotli.Spec
