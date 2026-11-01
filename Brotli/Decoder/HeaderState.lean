import Brotli.Decoder.HeaderRest
import Brotli.Decoder.Builder
import Brotli.Decoder.State

/-!
# The header machine's state

While a meta-block's header is read, the decoder's state is plain scalars and byte arrays, so it can pause at any bit.
`HRel` ties a state to a place in `hrest`, as `Rel` does for the commands. Everything about the spec here is ghost.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A small table held only while the header is read: it has been checked once, so its lookups need no check. -/
structure Tab where
  t : ByteArray
  h32 : t.size < 2 ^ 32
  fits : TableFits t (USize.ofNat 0).toNat

theorem usize_zero' : (USize.ofNat 0).toNat = 0 := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  exact Nat.zero_mod _

/-- A table of zeros, before a real one is read. -/
def Tab.none : Tab where
  t := zeroBytes 1024
  h32 := by rw [zeroBytes_size (by decide)]; decide
  fits := by
    rw [usize_zero']
    refine ⟨by rw [zeroBytes_size (by decide)]; omega, fun r _ hb => ?_⟩
    have : (slotAt (zeroBytes 1024) (0 + r)).1 = 0 := by
      simp only [slotAt]
      rw [zeroBytes_get (by decide)]
      rfl
    omega

/-- Who the prefix code being read is for. -/
inductive Role where
  | type
  | count
  | map
  | codes
  deriving DecidableEq

/-- Which place in the header a state is at. -/
inductive HTag where
  | cat
  | code
  | clens
  | syms
  | first
  | np
  | modes
  | trees
  | rlemax
  | vals
  | imtf
  | codes
  | ready
  deriving DecidableEq

/-- How a header step ended. -/
inductive HStatus where
  | next
  | needsInput
  | bad
  /-- The next table would pass the arena's limit. -/
  | memory
  | ready
  deriving DecidableEq

/-- What the header has settled so far. -/
structure Done where
  arena : ByteArray
  arenaMax : UInt64
  nL : UInt64
  nI : UInt64
  nD : UInt64
  countL : UInt64
  countI : UInt64
  countD : UInt64
  baseTL : USize
  baseCL : USize
  baseTI : USize
  baseCI : USize
  baseTD : USize
  baseCD : USize
  npostfix : UInt64
  ndirect : UInt64
  treesL : UInt64
  treesD : UInt64
  modes : ByteArray
  lMap : ByteArray
  dMap : ByteArray
  litBase : ByteArray
  icBase : ByteArray
  dBase : ByteArray

/-- A category's number of block types. -/
def Done.nOf (d : Done) : Cat → UInt64
  | .L => d.nL
  | .I => d.nI
  | .D => d.nD

/-- A category's first block count. -/
def Done.countOf (d : Done) : Cat → UInt64
  | .L => d.countL
  | .I => d.countI
  | .D => d.countD

/-- A category's block type table. -/
def Done.baseTOf (d : Done) : Cat → USize
  | .L => d.baseTL
  | .I => d.baseTI
  | .D => d.baseTD

/-- A category's block count table. -/
def Done.baseCOf (d : Done) : Cat → USize
  | .L => d.baseCL
  | .I => d.baseCI
  | .D => d.baseCD

/-- A group of codes' tables. -/
def Done.basesOf (d : Done) : CK → ByteArray
  | .L => d.litBase
  | .I => d.icBase
  | .D => d.dBase

/-- Sets a category's number of block types. -/
@[inline] def Done.setN (d : Done) (i : Cat) (n : UInt64) : Done :=
  match i with
  | .L => { d with nL := n }
  | .I => { d with nI := n }
  | .D => { d with nD := n }

/-- Sets a category's first block count. -/
@[inline] def Done.setCount (d : Done) (i : Cat) (n : UInt64) : Done :=
  match i with
  | .L => { d with countL := n }
  | .I => { d with countI := n }
  | .D => { d with countD := n }

/-- Sets a category's block type table. -/
@[inline] def Done.setBaseT (d : Done) (i : Cat) (b : USize) : Done :=
  match i with
  | .L => { d with baseTL := b }
  | .I => { d with baseTI := b }
  | .D => { d with baseTD := b }

/-- Sets a category's block count table. -/
@[inline] def Done.setBaseC (d : Done) (i : Cat) (b : USize) : Done :=
  match i with
  | .L => { d with baseCL := b }
  | .I => { d with baseCI := b }
  | .D => { d with baseCD := b }

/-- Sets a group of codes' tables. -/
@[inline] def Done.setBases (d : Done) (k : CK) (b : ByteArray) : Done :=
  match k with
  | .L => { d with litBase := b }
  | .I => { d with icBase := b }
  | .D => { d with dBase := b }

/-- The header machine's state between steps. -/
structure Hd where
  word : UInt64
  count : UInt64
  pos : USize
  status : HStatus
  tag : HTag
  d : Done
  cat : Cat
  role : Role
  isL : Bool
  ck : CK
  left : UInt64
  idx : UInt64
  size : UInt64
  ntrees : UInt64
  rlemax : UInt64
  /-- The array being filled for the modes, a context map or a group of codes' tables. -/
  fill : ByteArray
  lens : ByteArray
  ln : UInt64
  prevLen : UInt64
  repSym : UInt64
  repCount : UInt64
  symSum : UInt64
  clLens : ByteArray
  clIdx : UInt64
  clSum : UInt64
  clNz : UInt64
  clSym : UInt64
  clt : Tab
  mapT : Tab

/-- A state as a step leaves it. -/
@[inline] def markH (st : Hd) (pos : USize) (s : HStatus) : Hd := { st with pos := pos, status := s }

/-- A state's position and status don't matter to what it holds. -/
@[noinline] def clearFill (st : Hd) : Hd := { st with fill := ByteArray.empty }

/-- Empties a state's code lengths, as `clearRing` does its window. -/
@[noinline] def clearLens (st : Hd) : Hd := { st with lens := ByteArray.empty }

/-- Empties a state's code length code lengths. -/
@[noinline] def clearClLens (st : Hd) : Hd := { st with clLens := ByteArray.empty }

/-- Empties a state's settled part, so the arena inside it is held once. -/
@[noinline] def clearDone (st : Hd) (d : Done) : Hd := { st with d := d }

/-! ### The ghost record's parts -/

/-- A category of the ghost record. -/
def Gh.catOf (g : Gh) : Cat → BlockCategory
  | .L => g.m.literal
  | .I => g.m.insertCopy
  | .D => g.m.distance

/-- A group of codes of the ghost record. -/
def Gh.codesOf (g : Gh) : CK → List PrefixCode
  | .L => g.m.literalCodes
  | .I => g.m.insertCopyCodes
  | .D => g.m.distanceCodes

/-- A category's place. -/
def catIdx : Cat → Nat
  | .L => 0
  | .I => 1
  | .D => 2

/-- A group of codes' place, after the first seven. -/
def ckIdx : CK → Nat
  | .L => 0
  | .I => 1
  | .D => 2

/-- A map's place. -/
def mapIdx (isL : Bool) : Nat := if isL then 5 else 6

/-- How many codes a group has. -/
def Gh.ckCount (g : Gh) : CK → Nat
  | .L => g.treesL
  | .I => g.m.insertCopy.n
  | .D => g.treesD

/-! ### What's settled -/

/-- A category is settled. -/
structure CatOk (d : Done) (i : Cat) (c : BlockCategory) : Prop where
  n : (d.nOf i).toNat = c.n
  count : (d.countOf i).toNat = c.firstCount
  rel : CatRel d.arena (d.baseTOf i) (d.baseCOf i) c
  wf : c.Wf
  tc : Complete c.typeCode
  cc : Complete c.countCode

/-- A group of codes so far: the first ones have tables. -/
structure CodesPart (t bases : ByteArray) (cs : List PrefixCode) (total size : Nat) : Prop where
  basesSize : bases.size = 4 * total
  le : cs.length ≤ total
  code : ∀ i, i < cs.length → ∃ c, cs[i]? = some c ∧ TableOk t (u32At bases i) c ∧ Complete c ∧ c.Symbols size

/-- A context map, with its bytes. -/
structure MapOk (b : ByteArray) (l : List Nat) (size ntrees : Nat) : Prop where
  sz : b.size = size
  length : l.length = size
  at_ : ∀ i, i < size → l[i]? = some (b.data[i]?.getD 0).toNat
  lt : ∀ v ∈ l, v < ntrees

/-- What's settled at stage `n`. -/
structure Upto (d : Done) (g : Gh) (n : Nat) : Prop where
  four : d.arena.size % 4 = 0
  le : d.arena.size ≤ d.arenaMax.toNat
  max : d.arenaMax.toNat + 132096 < 2 ^ 32
  cat : ∀ i, catIdx i < n → CatOk d i (g.catOf i)
  np : 3 < n → d.npostfix.toNat = g.m.npostfix ∧ d.ndirect.toNat = g.m.ndirect ∧ g.m.npostfix ≤ 3 ∧ g.m.ndirect ≤ 120
  modes : 4 < n → MapOk d.modes g.m.contextModes g.m.literal.n 4
  lmap : 5 < n → d.treesL.toNat = g.treesL ∧ 1 ≤ g.treesL ∧ g.treesL ≤ 256 ∧
    MapOk d.lMap g.m.literalMap (literalContextMapSize g.m.literal.n) g.treesL
  dmap : 6 < n → d.treesD.toNat = g.treesD ∧ 1 ≤ g.treesD ∧ g.treesD ≤ 256 ∧
    MapOk d.dMap g.m.distanceMap (distanceContextMapSize g.m.distance.n) g.treesD
  codes : ∀ k, ckIdx k + 7 < n → g.ckCount k = (g.codesOf k).length ∧
    CodesPart d.arena (d.basesOf k) (g.codesOf k) (g.ckCount k) (ckSize k g)

/-- The array grew at its end only. -/
structure Keep (t t' : ByteArray) : Prop where
  four : t.size % 4 = 0
  le : t.size ≤ t'.size
  frame : ∀ q, q < t.size / 4 → slotAt t' q = slotAt t q

theorem CatRel.frame {t t' : ByteArray} {a b : USize} {c : BlockCategory} (h : CatRel t a b c) (hk : Keep t t') : CatRel t' a b c where
  type hn := by
    obtain ⟨h1, h2⟩ := h.type hn
    exact ⟨h1.frame hk.four hk.le hk.frame, h2⟩
  count hn := by
    obtain ⟨h1, h2⟩ := h.count hn
    exact ⟨h1.frame hk.four hk.le hk.frame, h2⟩

theorem CodesPart.frame {t t' bases : ByteArray} {cs : List PrefixCode} {total size : Nat} (h : CodesPart t bases cs total size)
    (hk : Keep t t') : CodesPart t' bases cs total size where
  basesSize := h.basesSize
  le := h.le
  code i hi := by
    obtain ⟨c, h1, h2, h3⟩ := h.code i hi
    exact ⟨c, h1, h2.frame hk.four hk.le hk.frame, h3⟩

/-- A longer arena keeps everything settled. -/
theorem Upto.frame {d : Done} {g : Gh} {n : Nat} (h : Upto d g n) {a : ByteArray} (hk : Keep d.arena a) (h4 : a.size % 4 = 0)
    (hle : a.size ≤ d.arenaMax.toNat) : Upto { d with arena := a } g n where
  four := h4
  le := hle
  max := h.max
  cat i hi := by
    have hc := h.cat i hi
    cases i <;> exact ⟨hc.n, hc.count, hc.rel.frame hk, hc.wf, hc.tc, hc.cc⟩
  np := h.np
  modes := h.modes
  lmap := h.lmap
  dmap := h.dmap
  codes k hk' := by
    obtain ⟨h1, h2⟩ := h.codes k hk'
    cases k <;> exact ⟨h1, h2.frame hk⟩

/-! ### The places -/

/-- Which stage a code's owner is at. -/
def ownerStage : Owner → Nat
  | .type i _ => catIdx i
  | .count i _ _ => catIdx i
  | .map isL _ _ => mapIdx isL
  | .codes k _ _ => ckIdx k + 7

/-- Which stage a place is at. -/
def stageOf : HPhase → Nat
  | .cat i => catIdx i
  | .code o _ => ownerStage o
  | .clens o _ _ _ _ => ownerStage o
  | .syms o _ _ _ => ownerStage o
  | .first i _ _ _ => catIdx i
  | .np => 3
  | .modes _ _ => 4
  | .trees isL => mapIdx isL
  | .rlemax isL _ => mapIdx isL
  | .vals isL _ _ _ _ _ => mapIdx isL
  | .imtf isL _ _ => mapIdx isL
  | .codes k _ _ => ckIdx k + 7

/-- The fields for who a code is for. -/
def OwnerRel (st : Hd) (g : Gh) (size : Nat) : Owner → Prop
  | .type i n => st.role = .type ∧ st.cat = i ∧ (st.d.nOf i).toNat = n ∧ 2 ≤ n ∧ n ≤ 256 ∧ size = blockTypeAlphabetSize n
  | .count i n tc => st.role = .count ∧ st.cat = i ∧ (st.d.nOf i).toNat = n ∧ 2 ≤ n ∧ n ≤ 256 ∧ size = blockCountAlphabetSize ∧
    TableOk st.d.arena (st.d.baseTOf i).toNat tc ∧ Complete tc ∧ tc.Symbols (blockTypeAlphabetSize n)
  | .map isL ntrees rlemax => st.role = .map ∧ st.isL = isL ∧ st.ntrees.toNat = ntrees ∧ st.rlemax.toNat = rlemax ∧
    2 ≤ ntrees ∧ ntrees ≤ 256 ∧ rlemax ≤ 16 ∧ size = contextMapAlphabetSize ntrees rlemax
  | .codes k done left => st.role = .codes ∧ st.ck = k ∧ st.idx.toNat = done.length ∧ st.left.toNat = left ∧
    size = ckSize k g ∧ done.length + 1 + left = g.ckCount k ∧ g.ckCount k ≤ 256 ∧
    CodesPart st.d.arena st.fill done (g.ckCount k) size

/-- A prefix code's alphabet is within a slot's symbols and `lens`'s room. -/
def SizeOk (st : Hd) (size : Nat) : Prop := st.size.toNat = size ∧ 2 ≤ size ∧ size ≤ 704

/-- The code lengths of the code length alphabet so far. -/
structure ClRel (st : Hd) (order : List Nat) (acc : List (Nat × Nat)) (sum : Nat) : Prop where
  orderOk : order = codeLengthOrder.drop st.clIdx.toNat
  le : st.clIdx.toNat ≤ 18
  sumOk : st.clSum.toNat = sum
  sumLt : sum < 32
  sumEq : lengthSum (acc.map (·.2)) = 1024 * sum
  size : st.clLens.size = 18
  /-- The lengths so far, as `lengthsOf` will take them. -/
  lens : ∀ i, i < 18 → (st.clLens.data[i]?.getD 0).toNat = ((acc.find? (·.1 == i)).map (·.2)).getD 0
  keys : (acc.map (·.1)).Nodup
  apart : ∀ p ∈ acc, p.1 < 18 ∧ p.1 ∉ order ∧ p.2 ≤ 5
  nz : st.clNz.toNat = (acc.filter (·.2 != 0)).length
  nzOne : (acc.filter (·.2 != 0)).length = 1 → ∃ l, acc.filter (·.2 != 0) = [(st.clSym.toNat, l)]
  symLt : st.clSym.toNat < 18

/-- The code lengths so far. -/
structure SymRel (st : Hd) (size : Nat) (clc : PrefixCode) (ls : LengthState) : Prop where
  table : TableOk st.clt.t (USize.ofNat 0).toNat clc
  complete : Complete clc
  symbols : clc.Symbols 18
  sz : st.lens.size = size
  ln : st.ln.toNat = ls.lens.length
  le : ls.lens.length ≤ size
  /-- The lengths so far, with zeros after them. -/
  lens : lensOf st.lens size = ls.lens ++ List.replicate (size - ls.lens.length) 0
  small : ∀ l ∈ ls.lens, l ≤ 15
  prev : st.prevLen.toNat = ls.prev
  prevOk : 1 ≤ ls.prev ∧ ls.prev ≤ 15
  rep : match ls.rep with
    | some (s, c) => st.repSym.toNat = s ∧ st.repCount.toNat = c ∧ 3 ≤ c ∧ c ≤ ls.lens.length
    | none => st.repCount.toNat = 0
  sumOk : st.symSum.toNat = lengthSum ls.lens
  sumLe : lengthSum ls.lens ≤ 32768

/-- A state stands for a place in a header. -/
def HRel (st : Hd) (g : Gh) (p : HPhase) : Prop :=
  (BitBuffer.mk st.word st.count).Wf ∧ Upto st.d g (stageOf p) ∧
    match p with
    | .cat i => st.tag = .cat ∧ st.cat = i
    | .code o size => st.tag = .code ∧ SizeOk st size ∧ OwnerRel st g size o
    | .clens o size order acc sum => st.tag = .clens ∧ SizeOk st size ∧ OwnerRel st g size o ∧ ClRel st order acc sum
    | .syms o size clc ls => st.tag = .syms ∧ SizeOk st size ∧ OwnerRel st g size o ∧ SymRel st size clc ls
    | .first i n tc cc => st.tag = .first ∧ st.cat = i ∧ (st.d.nOf i).toNat = n ∧ 2 ≤ n ∧ n ≤ 256 ∧
      TableOk st.d.arena (st.d.baseTOf i).toNat tc ∧ Complete tc ∧ tc.Symbols (blockTypeAlphabetSize n) ∧
      TableOk st.d.arena (st.d.baseCOf i).toNat cc ∧ Complete cc ∧ cc.Symbols blockCountAlphabetSize
    | .np => st.tag = .np
    | .modes done left => st.tag = .modes ∧ st.idx.toNat = done.length ∧ st.left.toNat = left ∧
      done.length + left = g.m.literal.n ∧ st.fill.size = g.m.literal.n ∧ (∀ v ∈ done, v < 4) ∧
      ∀ i, i < done.length → done[i]? = some (st.fill.data[i]?.getD 0).toNat
    | .trees isL => st.tag = .trees ∧ st.isL = isL
    | .rlemax isL ntrees => st.tag = .rlemax ∧ st.isL = isL ∧ st.ntrees.toNat = ntrees ∧ 2 ≤ ntrees ∧ ntrees ≤ 256
    | .vals isL ntrees rlemax code done left => st.tag = .vals ∧ st.isL = isL ∧ st.ntrees.toNat = ntrees ∧
      st.rlemax.toNat = rlemax ∧ 2 ≤ ntrees ∧ ntrees ≤ 256 ∧ rlemax ≤ 16 ∧
      TableOk st.mapT.t (USize.ofNat 0).toNat code ∧ Complete code ∧ code.Symbols (contextMapAlphabetSize ntrees rlemax) ∧
      st.idx.toNat = done.length ∧ st.left.toNat = left ∧ done.length + left = mapSize g isL ∧
      st.fill.size = mapSize g isL ∧ (∀ v ∈ done, v < ntrees) ∧
      (∀ i, i < done.length → done[i]? = some (st.fill.data[i]?.getD 0).toNat) ∧
      ∀ i, done.length ≤ i → st.fill.data[i]?.getD 0 = 0
    | .imtf isL ntrees vals => st.tag = .imtf ∧ st.isL = isL ∧ st.ntrees.toNat = ntrees ∧ 2 ≤ ntrees ∧ ntrees ≤ 256 ∧
      MapOk st.fill vals (mapSize g isL) ntrees
    | .codes k done left => st.tag = .codes ∧ st.ck = k ∧ st.idx.toNat = done.length ∧ st.left.toNat = left ∧
      done.length + left = g.ckCount k ∧ g.ckCount k ≤ 256 ∧ CodesPart st.d.arena st.fill done (g.ckCount k) (ckSize k g)

theorem HRel.wf {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) : (BitBuffer.mk st.word st.count).Wf := h.1

theorem HRel.mark {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) (pos : USize) (s : HStatus) :
    HRel (markH st pos s) g p := by
  cases p
  case clens =>
    obtain ⟨hw, hu, ht, hs, ho, hc⟩ := h
    exact ⟨hw, hu, ht, hs, ho, { hc with }⟩
  case syms =>
    obtain ⟨hw, hu, ht, hs, ho, hc⟩ := h
    exact ⟨hw, hu, ht, hs, ho, { hc with }⟩
  all_goals exact h

theorem HRel.withBits {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) {word count : UInt64}
    (hw : (BitBuffer.mk word count).Wf) : HRel { st with word := word, count := count } g p := by
  cases p
  case clens =>
    obtain ⟨_, hu, ht, hs, ho, hc⟩ := h
    exact ⟨hw, hu, ht, hs, ho, { hc with }⟩
  case syms =>
    obtain ⟨_, hu, ht, hs, ho, hc⟩ := h
    exact ⟨hw, hu, ht, hs, ho, { hc with }⟩
  all_goals exact ⟨hw, h.2⟩

/-! ### What a step must do -/

/-- What a header step must do. It is `StepOk` for a header's places, and a header is finished when all of it is read. -/
structure HStepOk {α : Type} (K : MetaBlockHeader → List Bool → Option α) (a : ByteArray) (stop : USize) (g : Gh) (p : HPhase)
    (st : Hd) (pos : USize) (r : Hd) : Prop where
  next : r.status = .next → ∃ g' p', HRel r g' p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = hrest K g' p' (availBits r.word r.count a r.pos stop F)
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ HRel r g p ∧
    (∀ F, hrest K g p (availBits st.word st.count a pos stop F) = hrest K g p (availBits r.word r.count a r.pos stop F)) ∧
    hrest K g p (BitBuffer.mk r.word r.count).held = none
  bad : r.status = .bad → ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = none
  memory : r.status = .memory → r.d.arenaMax = st.d.arenaMax
  ready : r.status = .ready → ∃ g', Upto r.d g' 10 ∧ (BitBuffer.mk r.word r.count).Wf ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = K g'.m (availBits r.word r.count a r.pos stop F)

section
variable {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray} {stop : USize} {g : Gh} {p : HPhase}
  {st : Hd} {pos : USize} {r : Hd}

/-- A step that moved on. -/
theorem HStepOk.ofNext (hs : r.status = .next) {g' : Gh} {p' : HPhase} (hrel : HRel r g' p') (h1 : pos.toNat ≤ r.pos.toNat)
    (h2 : r.pos.toNat ≤ stop.toNat)
    (h : ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = hrest K g' p' (availBits r.word r.count a r.pos stop F)) :
    HStepOk K a stop g p st pos r :=
  ⟨fun _ => ⟨g', p', hrel, h1, h2, h⟩, fun e => HStatus.noConfusion (hs.symm.trans e),
    fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e),
    fun e => HStatus.noConfusion (hs.symm.trans e)⟩

/-- A step that rejected. -/
theorem HStepOk.ofBad (hs : r.status = .bad) (h : ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = none) :
    HStepOk K a stop g p st pos r :=
  ⟨fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e), fun _ => h,
    fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e)⟩

/-- A read that fell short and changed nothing. -/
theorem HStepOk.ofShort (hrel : HRel st g p) (hstop : pos = stop) (hn : hrest K g p (BitBuffer.mk st.word st.count).held = none) :
    HStepOk K a stop g p st pos (markH st pos .needsInput) :=
  ⟨fun e => HStatus.noConfusion e,
    fun _ => ⟨hstop, by rw [hstop]; exact Nat.le_refl _, hrel.mark _ _, fun _ => rfl, hn⟩,
    fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e⟩

/-- A step that's past the arena's limit. -/
theorem HStepOk.ofMemory (hs : r.status = .memory) (h : r.d.arenaMax = st.d.arenaMax) : HStepOk K a stop g p st pos r :=
  ⟨fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e),
    fun e => HStatus.noConfusion (hs.symm.trans e), fun _ => h, fun e => HStatus.noConfusion (hs.symm.trans e)⟩

/-- A step taken after a refill is a step from before it. -/
theorem HStepOk.refilled {st1 : Hd} {pos1 : USize} (h : HStepOk K a stop g p st1 pos1 r)
    (hb : ∀ F, availBits st.word st.count a pos stop F = availBits st1.word st1.count a pos1 stop F) (h1 : pos.toNat ≤ pos1.toNat)
    (h2 : pos1.toNat ≤ stop.toNat) (hd : st1.d.arenaMax = st.d.arenaMax) : HStepOk K a stop g p st pos r where
  next e := by
    obtain ⟨g', p', hrel, h3, h4, h5⟩ := h.next e
    exact ⟨g', p', hrel, Nat.le_trans h1 h3, h4, fun F => by rw [hb]; exact h5 F⟩
  needsInput e := by
    obtain ⟨h3, _, hrel, h5, h6⟩ := h.needsInput e
    exact ⟨h3, Nat.le_trans h1 h2, hrel, fun F => by rw [hb]; exact h5 F, h6⟩
  bad e := fun F => by rw [hb]; exact h.bad e F
  memory e := by rw [h.memory e, hd]
  ready e := by
    obtain ⟨g', h3, h4, h5, h6, h7⟩ := h.ready e
    exact ⟨g', h3, h4, Nat.le_trans h1 h5, h6, fun F => by rw [hb]; exact h7 F⟩

end

end Brotli.Decoder
