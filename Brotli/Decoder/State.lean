import Brotli.Decoder.Literals
import Brotli.Decoder.Block
import Brotli.Decoder.Fixed

/-!
# The command loop's state

`Hdr` is a meta-block's fast header, with the checks made once when it is built. `Cmd` is the loop's state: plain
scalars and byte arrays, between steps. `Rel` ties a state to the place in `rest` it stands for, which is the bridge
for the command loop. Everything about the spec here is ghost: it appears only in propositions.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Which place in the command loop a state is at. -/
inductive Tag where
  | command
  | insertCopy
  | copyLength
  | literals
  | distance
  | distanceSymbol
  | copy
  | word
  deriving DecidableEq

/-- How a step ended. -/
inductive StepStatus where
  /-- It moved on, to another place or further through the same one. -/
  | next
  /-- It needs more input: the chunk is used up and the bits held can't finish the next read. -/
  | needsInput
  /-- The window is full of bytes not yet handed over. -/
  | needsOutput
  /-- The meta-block's commands are finished. -/
  | done
  /-- The spec rejects, whatever bits follow. -/
  | bad
  deriving DecidableEq

/-- The block types that occurred, four words per category: type `t`'s flag is bit `t % 64` of word `t / 64`. They are
held apart from the loop's state, which a block switch alone changes, so that every other step's state stays small. -/
structure Flags where
  fL0 : UInt64
  fL1 : UInt64
  fL2 : UInt64
  fL3 : UInt64
  fI0 : UInt64
  fI1 : UInt64
  fI2 : UInt64
  fI3 : UInt64
  fD0 : UInt64
  fD1 : UInt64
  fD2 : UInt64
  fD3 : UInt64

/-- The loop's state between steps. A step returns it with the input position and how the step ended, so that a step
updates it in place and returns nothing else. -/
structure Cmd where
  word : UInt64
  count : UInt64
  ring : ByteArray
  wpos : USize
  /-- Output bytes not yet handed over. -/
  pend : USize
  /-- How many bytes may wait before the loop stops for output space: one more than the call's space left, so that a call
  decodes little more than it can hand out. -/
  cap : USize
  /-- The smaller of the window and the bytes produced. -/
  written : USize
  p1 : UInt8
  p2 : UInt8
  d0 : UInt64
  d1 : UInt64
  d2 : UInt64
  d3 : UInt64
  remaining : UInt64
  iCur : UInt64
  iPrev : UInt64
  iCount : UInt64
  lCur : UInt64
  lPrev : UInt64
  lCount : UInt64
  dCur : UInt64
  dPrev : UInt64
  dCount : UInt64
  /-- The block types that occurred. -/
  flags : Flags
  tag : Tag
  code : UInt64
  ilen : UInt64
  clen : UInt64
  left : UInt64
  copyBits : UInt64
  copyBase : UInt64
  dist : UInt64
  wordBuf : ByteArray
  wordPos : USize
  pos : USize
  status : StepStatus

/-- A meta-block's fast header. -/
structure Hdr where
  arena : ByteArray
  /-- What the arena has reserved. -/
  arenaCap : UInt64
  litBase : ByteArray
  lMap : ByteArray
  icBase : ByteArray
  dBase : ByteArray
  dMap : ByteArray
  modes : ByteArray
  nL : UInt64
  nI : UInt64
  nD : UInt64
  treesL : UInt64
  treesD : UInt64
  baseTL : USize
  baseCL : USize
  baseTI : USize
  baseCI : USize
  baseTD : USize
  baseCD : USize
  npostfix : UInt64
  ndirect : UInt64
  npLe : npostfix.toNat ≤ 3
  ndLe : ndirect.toNat ≤ 120
  lit : LitChecked arena litBase lMap treesL.toNat
  lMapSize : lMap.size = 64 * nL.toNat
  modesSize : modes.size = nL.toNat
  modesLt : ∀ p : USize, ∀ h : p.toNat < modes.size, (modes.uget p h).toNat < 4
  icSize : icBase.size = 4 * nI.toNat
  ic32 : icBase.size < 2 ^ 32
  icFits : ∀ t, t < nI.toNat → TableFits arena (u32At icBase t)
  dSize : dBase.size = 4 * treesD.toNat
  d32 : dBase.size < 2 ^ 32
  dMapSize : dMap.size = 4 * nD.toNat
  dMap32 : dMap.size < 2 ^ 32
  dMapLt : ∀ p : USize, ∀ h : p.toNat < dMap.size, (dMap.uget p h).toNat < treesD.toNat
  dFits : ∀ tree, tree < treesD.toNat → TableFits arena (u32At dBase tree)
  swL : 2 ≤ nL.toNat → TableFits arena baseTL.toNat ∧ TableFits arena baseCL.toNat
  swI : 2 ≤ nI.toNat → TableFits arena baseTI.toNat ∧ TableFits arena baseCI.toNat
  swD : 2 ≤ nD.toNat → TableFits arena baseTD.toNat ∧ TableFits arena baseCD.toNat

/-- What a meta-block header gives the lookups that follow it. -/
structure HeaderOk (m : MetaBlockHeader) : Prop where
  literal : m.literal.Wf
  insertCopy : m.insertCopy.Wf
  distance : m.distance.Wf
  literalCount : 2 ≤ m.literal.n → m.literal.countCode.Symbols blockCountAlphabetSize
  insertCopyCount : 2 ≤ m.insertCopy.n → m.insertCopy.countCode.Symbols blockCountAlphabetSize
  distanceCount : 2 ≤ m.distance.n → m.distance.countCode.Symbols blockCountAlphabetSize
  modes_length : m.contextModes.length = m.literal.n
  literalMap_length : m.literalMap.length = literalContextMapSize m.literal.n
  literalMap_lt : ∀ v ∈ m.literalMap, v < m.literalCodes.length
  literalCodes : ∀ c ∈ m.literalCodes, c.Symbols literalAlphabetSize ∧ Complete c
  insertCopyCodes_length : m.insertCopyCodes.length = m.insertCopy.n
  insertCopyCodes : ∀ c ∈ m.insertCopyCodes, c.Symbols insertCopyAlphabetSize ∧ Complete c
  distanceMap_length : m.distanceMap.length = distanceContextMapSize m.distance.n
  distanceMap_lt : ∀ v ∈ m.distanceMap, v < m.distanceCodes.length
  distanceCodes : ∀ c ∈ m.distanceCodes,
    c.Symbols (distanceAlphabetSize m.npostfix m.ndirect) ∧ Complete c
  literalSwitch : Complete m.literal.typeCode ∧ Complete m.literal.countCode
  insertCopySwitch : Complete m.insertCopy.typeCode ∧ Complete m.insertCopy.countCode
  distanceSwitch : Complete m.distance.typeCode ∧ Complete m.distance.countCode

/-- A category's switch tables match the spec's. -/
structure CatRel (arena : ByteArray) (baseT baseC : USize) (c : BlockCategory) : Prop where
  type : 2 ≤ c.n → TableOk arena baseT.toNat c.typeCode ∧ Complete c.typeCode ∧
    c.typeCode.Symbols (blockTypeAlphabetSize c.n)
  count : 2 ≤ c.n → TableOk arena baseC.toNat c.countCode ∧ Complete c.countCode ∧
    c.countCode.Symbols blockCountAlphabetSize

/-- The fast header matches the spec's. -/
structure HdrRel (H : Hdr) (m : MetaBlockHeader) : Prop where
  ok : HeaderOk m
  nL : H.nL.toNat = m.literal.n
  nI : H.nI.toNat = m.insertCopy.n
  nD : H.nD.toNat = m.distance.n
  npostfix : H.npostfix.toNat = m.npostfix
  ndirect : H.ndirect.toNat = m.ndirect
  lit : LitRel H.arena H.litBase H.lMap H.treesL.toNat m
  modes : ∀ p : USize, ∀ h : p.toNat < H.modes.size, m.contextModes[p.toNat]? = some (H.modes.uget p h).toNat
  ic : ∀ t, t < H.nI.toNat → ∃ code, m.insertCopyCodes[t]? = some code ∧ TableOk H.arena (u32At H.icBase t) code ∧
    Complete code ∧ code.Symbols insertCopyAlphabetSize
  dMap : ∀ p : USize, ∀ h : p.toNat < H.dMap.size, m.distanceMap[p.toNat]? = some (H.dMap.uget p h).toNat
  d : ∀ tree, tree < H.treesD.toNat → ∃ code, m.distanceCodes[tree]? = some code ∧ TableOk H.arena (u32At H.dBase tree) code ∧
    Complete code ∧ code.Symbols (distanceAlphabetSize m.npostfix m.ndirect)
  catL : CatRel H.arena H.baseTL H.baseCL m.literal
  catI : CatRel H.arena H.baseTI H.baseCI m.insertCopy
  catD : CatRel H.arena H.baseTD H.baseCD m.distance

/-! ### Block type flags -/

/-- Word `j` of a category's flags, with type `t` marked: the bit `t % 64` goes to the word `t / 64` only. -/
@[inline] def markWord (w t j : UInt64) : UInt64 := w ||| (((1 : UInt64) >>> (t / 64 ^^^ j)) <<< (t % 64))

private theorem xor_small : ∀ a, a < 4 → ∀ b, b < 4 → a ^^^ b < 4 ∧ (1 >>> (a ^^^ b) = if a = b then 1 else 0) := by
  decide

theorem markWord_bit {w t j : UInt64} (ht : t.toNat < 256) (hj : j.toNat < 4) {i : Nat} (hi : i < 64) :
    (markWord w t j).toNat.testBit i =
      (w.toNat.testBit i || (decide (t.toNat / 64 = j.toNat) && decide (i = t.toNat % 64))) := by
  have ha : t.toNat / 64 < 4 := by omega
  obtain ⟨hx, hs⟩ := xor_small _ ha _ hj
  have hm : t.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
  unfold markWord
  rw [UInt64.toNat_or, Nat.testBit_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.toNat_xor, UInt64.toNat_div,
    UInt64.toNat_mod]
  rw [show (1 : UInt64).toNat = 1 from rfl, show (64 : UInt64).toNat = 64 from rfl,
    Nat.mod_eq_of_lt (show t.toNat / 64 ^^^ j.toNat < 64 by omega), Nat.mod_mod, hs]
  congr 1
  rw [Nat.testBit_mod_two_pow, decide_eq_true (show i < 64 by omega), Bool.true_and, Nat.testBit_shiftLeft]
  by_cases he : t.toNat / 64 = j.toNat
  · rw [ite_eq_left he, decide_eq_true he, Bool.true_and]
    by_cases hq : i = t.toNat % 64
    · subst hq
      simp
    · rw [decide_eq_false hq]
      by_cases hge : i ≥ t.toNat % 64
      · rw [decide_eq_true hge, Bool.true_and]
        rw [show i - t.toNat % 64 = (i - t.toNat % 64 - 1) + 1 by omega]
        simp [Nat.testBit_succ]
      · rw [decide_eq_false hge, Bool.false_and]
  · rw [ite_eq_right he, decide_eq_false he, Bool.false_and]
    simp

/-- A category's flag for type `t`: bit `t % 64` of word `t / 64`. -/
def flagOf (w0 w1 w2 w3 : UInt64) (t : Nat) : Bool :=
  (if t / 64 = 0 then w0 else if t / 64 = 1 then w1 else if t / 64 = 2 then w2 else w3).toNat.testBit (t % 64)

/-- Marking type `c` sets its flag and no other. -/
theorem flagOf_mark {w0 w1 w2 w3 c : UInt64} (hc : c.toNat < 256) {t : Nat} (ht : t < 256) :
    flagOf (markWord w0 c 0) (markWord w1 c 1) (markWord w2 c 2) (markWord w3 c 3) t =
      (flagOf w0 w1 w2 w3 t || decide (t = c.toNat)) := by
  have hi : t % 64 < 64 := Nat.mod_lt _ (by decide)
  have key : ∀ k : Nat, k < 4 → t / 64 = k →
      (decide (c.toNat / 64 = k) && decide (t % 64 = c.toNat % 64)) = decide (t = c.toNat) := by
    intro k _ hk
    by_cases h : t = c.toNat
    · subst h
      simp [hk]
    · rw [decide_eq_false h]
      by_cases h1 : c.toNat / 64 = k
      · rw [decide_eq_true h1, Bool.true_and, decide_eq_false (fun e => h (by omega))]
      · rw [decide_eq_false h1, Bool.false_and]
  unfold flagOf
  have : t / 64 = 0 ∨ t / 64 = 1 ∨ t / 64 = 2 ∨ t / 64 = 3 := by omega
  rcases this with h | h | h | h <;> simp only [h, ↓reduceIte, Nat.reduceEqDiff] <;>
    rw [markWord_bit hc (by decide) hi] <;>
    simp only [show UInt64.toNat 0 = 0 from rfl, show UInt64.toNat 1 = 1 from rfl, show UInt64.toNat 2 = 2 from rfl,
      show UInt64.toNat 3 = 3 from rfl] <;> rw [key _ (by decide) h]

/-- A block state is held by these fields, and its `seen` list by those flags. -/
structure BlockRel (w0 w1 w2 w3 : UInt64) (cur prev count : UInt64) (st : BlockState) (c : BlockCategory) : Prop where
  cur : st.types.cur = cur.toNat
  prev : st.types.prev = prev.toNat
  count : st.count = count.toNat
  wf : st.Wf c
  flags : ∀ t, t < 256 → (flagOf w0 w1 w2 w3 t = true ↔ t ∈ st.seen)

/-- The parts of a state that every place has in common, with the ghost values they stand for. -/
structure Core (w k : Nat) (m : MetaBlockHeader) (st : Cmd) (out : List Nat) (rem : Nat) (ds : Distances)
    (ic lit dist : BlockState) : Prop where
  wf : (BitBuffer.mk st.word st.count).Wf
  win : w + 16 = 2 ^ k
  k24 : k ≤ 24
  ring : RingOk st.ring k st.wpos.toNat out
  bytes : ∀ b ∈ out, b < 256
  ctx : contextBytes out = (st.p1.toNat, st.p2.toNat)
  pendLe : st.pend.toNat ≤ 2 ^ k
  pendOut : st.pend.toNat ≤ out.length
  written : st.written.toNat = min w out.length
  rem : st.remaining.toNat = rem
  d0 : ds.last = st.d0.toNat
  d1 : ds.secondToLast = st.d1.toNat
  d2 : ds.thirdToLast = st.d2.toNat
  d3 : ds.fourthToLast = st.d3.toNat
  dsLt : ds.last < 2 ^ 32 ∧ ds.secondToLast < 2 ^ 32 ∧ ds.thirdToLast < 2 ^ 32 ∧ ds.fourthToLast < 2 ^ 32
  iRel : BlockRel st.flags.fI0 st.flags.fI1 st.flags.fI2 st.flags.fI3 st.iCur st.iPrev st.iCount ic m.insertCopy
  lRel : BlockRel st.flags.fL0 st.flags.fL1 st.flags.fL2 st.flags.fL3 st.lCur st.lPrev st.lCount lit m.literal
  dRel : BlockRel st.flags.fD0 st.flags.fD1 st.flags.fD2 st.flags.fD3 st.dCur st.dPrev st.dCount dist m.distance
  wordLe : st.wordBuf.size ≤ 38

/-- A state stands for a place in `rest`. -/
def Rel (w k : Nat) (m : MetaBlockHeader) (st : Cmd) : Phase → Prop
  | .command s =>
    Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance ∧ st.tag = .command ∧
      s.produced = s.output.length
  | .insertCopy s ic =>
    Core w k m st s.output s.remaining s.distances ic s.literal s.distance ∧ st.tag = .insertCopy ∧
      s.produced = s.output.length
  | .copyLength s ic c ilen copyBits copyBase =>
    Core w k m st s.output s.remaining s.distances ic s.literal s.distance ∧ st.tag = .copyLength ∧
      s.produced = s.output.length ∧ st.code.toNat = c ∧ st.ilen.toNat = ilen ∧ st.copyBits.toNat = copyBits ∧
      st.copyBase.toNat = copyBase ∧ copyBits ≤ 24 ∧ copyBase ≤ 2118
  | .literals s ic c ilen clen n lit out =>
    Core w k m st out (s.remaining - (ilen - n)) s.distances ic lit s.distance ∧ st.tag = .literals ∧
      s.produced = s.output.length ∧ st.code.toNat = c ∧ st.ilen.toNat = ilen ∧ st.clen.toNat = clen ∧
      st.left.toNat = n ∧ n ≤ ilen ∧ ilen ≤ s.remaining ∧ out.length + n = s.output.length + ilen
  | .literalSymbol .. => False
  | .distance s c clen =>
    Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance ∧ st.tag = .distance ∧
      s.produced = s.output.length ∧ st.code.toNat = c ∧ st.clen.toNat = clen
  | .distanceSymbol s clen dist =>
    Core w k m st s.output s.remaining s.distances s.insertCopy s.literal dist ∧ st.tag = .distanceSymbol ∧
      s.produced = s.output.length ∧ st.clen.toNat = clen
  | .copy s d n =>
    Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance ∧ st.tag = .copy ∧
      s.produced = s.output.length + n ∧ st.dist.toNat = d ∧ st.left.toNat = n ∧ 1 ≤ d ∧ d ≤ w ∧ d ≤ s.output.length
  | .word s pending =>
    Core w k m st s.output s.remaining s.distances s.insertCopy s.literal s.distance ∧ st.tag = .word ∧
      s.produced = s.output.length + pending.length ∧
      (st.wordBuf.data.toList.drop st.wordPos.toNat).map UInt8.toNat = pending ∧ st.wordBuf.size ≤ 38 ∧
      st.wordPos.toNat ≤ st.wordBuf.size

/-- A state as a step leaves it. -/
@[inline] def markStep (st : Cmd) (pos : USize) (s : StepStatus) : Cmd := { st with pos := pos, status := s }

/-- A step's position and status don't matter to `Rel`. -/
theorem Rel.mark {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {p : Phase} (h : Rel w k m st p) (pos : USize) (s : StepStatus) :
    Rel w k m (markStep st pos s) p := by
  cases p with
  | literalSymbol => exact h.elim
  | command =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | insertCopy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | copyLength =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | literals =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | distance =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | distanceSymbol =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | copy =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩
  | word =>
    obtain ⟨hC, hr⟩ := h
    exact ⟨{ hC with }, hr⟩

/-- The bits a state and position stand for, then any future. -/
def stateBits (st : Cmd) (a : ByteArray) (pos stop : USize) (F : List Bool) : List Bool :=
  availBits st.word st.count a pos stop F

/-- Empties a state's window. Its caller reads the window first, then holds it alone, so writes to it don't copy it. It
is not inlined, because inlined the state would stay live and share the window. -/
@[noinline] def clearRing (st : Cmd) : Cmd := { st with ring := ByteArray.empty }

end Brotli.Decoder
