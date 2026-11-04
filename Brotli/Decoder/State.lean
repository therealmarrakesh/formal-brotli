import Brotli.Decoder.Literals
import Brotli.Decoder.Block
import Brotli.Decoder.Fixed
import Brotli.Properties.Lookups

/-!
# The command loop's state

`Hdr` is a meta-block's fast header, with the checks made once when it is built. `Cmd` is the loop's state: plain
scalars and byte arrays, between steps. `Rel` ties a state to the place in `rest` it stands for, which is the bridge
for the command loop. Everything about the spec here is ghost: it appears only in propositions.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

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
  /-- 256 flags per category, the block types that occurred. -/
  seen : ByteArray
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

/-- A block state is held by these fields, and its `seen` list by those flags. -/
structure BlockRel (seen : ByteArray) (off : Nat) (cur prev count : UInt64) (st : BlockState) (c : BlockCategory) : Prop where
  cur : st.types.cur = cur.toNat
  prev : st.types.prev = prev.toNat
  count : st.count = count.toNat
  wf : st.Wf c
  flags : ∀ t, t < 256 → ((seen.data[off + t]?.getD 0) ≠ 0 ↔ t ∈ st.seen)

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
  iRel : BlockRel st.seen 256 st.iCur st.iPrev st.iCount ic m.insertCopy
  lRel : BlockRel st.seen 0 st.lCur st.lPrev st.lCount lit m.literal
  dRel : BlockRel st.seen 512 st.dCur st.dPrev st.dCount dist m.distance
  seenSize : st.seen.size = 768
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

/-- Empties a state's block type flags, as `clearRing` does its window. -/
@[noinline] def clearSeen (st : Cmd) : Cmd := { st with seen := ByteArray.empty }

end Brotli.Decoder
