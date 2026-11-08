module

public import Brotli.Decoder.HeaderOrder
public import Brotli.Decoder.Builder
public import Brotli.Decoder.FastTab
public import Brotli.Decoder.TableSize
public import Brotli.Decoder.State
public import Brotli.Decoder.Step
public import Brotli.Decoder.FastEq

@[expose] public section

/-!
# The header machine's state

While a meta-block's header is read, the decoder's state is plain scalars and byte arrays, so it can pause at any bit.
`HRel` ties a state to a place in `hrest`, as `Rel` does for the commands. Everything about the spec here is ghost.
-/

namespace Brotli.Decoder

open Brotli.Spec

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
  t := zeroBytes 512
  h32 := by rw [zeroBytes_size (by decide)]; decide
  fits := by
    rw [usize_zero']
    refine ⟨by rw [zeroBytes_size (by decide)]; omega, fun r _ hb => ?_⟩
    have : (slotAt (zeroBytes 512) (0 + r)).1 = 0 := by
      simp only [slotAt, slotNum]
      rw [zeroBytes_get (by decide), zeroBytes_get (by decide)]
      rfl
    omega

/-- Who the prefix code being read is for. -/
inductive Role where
  | type
  | count
  | map
  | codes
  deriving DecidableEq

fast_deceq Role [type, count, map, codes]

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

fast_deceq HTag [cat, code, clens, syms, first, np, modes, trees, rlemax, vals, imtf, codes, ready]

/-- How a header step ended. -/
inductive HStatus where
  | next
  | needsInput
  | bad
  /-- The groups' tables would pass the arena's limit. -/
  | memory
  | ready
  deriving DecidableEq

fast_deceq HStatus [next, needsInput, bad, memory, ready]

/-- What the header has settled so far. -/
structure Done where
  /-- The tables, one after another. -/
  arena : ByteArray
  /-- What the arena may reserve. -/
  arenaMax : UInt64
  /-- What the arena has reserved. -/
  arenaCap : UInt64
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
  /-- The 16-bit link to each length's last symbol so far, 0 for none (`ListsIs`). -/
  head : ByteArray
  /-- Each symbol's 16-bit link to the one before it of its length. -/
  next : ByteArray
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
  /-- A context map's values with the inverse move-to-front transform applied, as they are read. -/
  xf : ByteArray
  /-- The transform's move-to-front list. -/
  mtf : ByteArray
  /-- The values a context map has so far, as read. -/
  seenR : ByteArray
  /-- The values a context map has so far, transformed. -/
  seenX : ByteArray
  headSz : head.size = 32
  nextSz : next.size = 1408

/-- A state as a step leaves it. -/
@[inline] def markH (st : Hd) (pos : USize) (s : HStatus) : Hd := { st with pos := pos, status := s }

/-- A state's position and status don't matter to what it holds. -/
@[noinline] def clearFill (st : Hd) : Hd := { st with fill := ByteArray.empty }

/-- Empties a state's context map arrays, so that each is held once while a step writes it. -/
@[noinline] def clearMap (st : Hd) : Hd :=
  { st with fill := ByteArray.empty, xf := ByteArray.empty, mtf := ByteArray.empty, seenR := ByteArray.empty, seenX := ByteArray.empty }

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

/-- The prefix a header's arena starts with, before any table: the fast command loop's masks `2 ^ n - 1` for `n < 32`,
8 bytes each (`writeMasks`), then room for the shared distance table (4160 bytes), written at the header's end, so that
the arena itself is the loop's one table array and that table is at a fixed place. -/
def arenaPre : Nat := 4416

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
  /-- Every table is after the arena's prefix. -/
  lo : ∀ i, i < cs.length → arenaPre ≤ 2 * u32At bases i

/-- A context map, with its bytes. -/
structure MapOk (b : ByteArray) (l : List Nat) (size ntrees : Nat) : Prop where
  sz : b.size = size
  length : l.length = size
  at_ : ∀ i, i < size → l[i]? = some (b.data[i]?.getD 0).toNat
  lt : ∀ v ∈ l, v < ntrees

/-- The bytes a table of a code over `size` symbols can take (`tableBytes_le`). -/
def treeMax (size : Nat) : Nat := 2 * (size + 376)

/-- The bytes a category's block type and block count codes' tables can take. -/
def catMax : Nat := treeMax 258 + treeMax 26

/-- What the arena reserves at a header's start: the prefix and the three categories' codes. -/
def smallMax : Nat := 3 * catMax + arenaPre

/-- The bytes the fast command loop's derived tables can take at the header's end (`tabMax`), for at most 256 block types
in each category. -/
def tabMaxOf (g : Gh) : Nat := tabMax (min g.m.literal.n 256) (min g.m.insertCopy.n 256) (min g.m.distance.n 256)

/-- What's settled at stage `n`. Until both context maps are read, the arena has reserved room for the categories' codes;
after, also for the groups'. -/
structure Upto (d : Done) (g : Gh) (n : Nat) : Prop where
  four : d.arena.size % 2 = 0
  pre : arenaPre ≤ d.arena.size
  masks : ∀ n, n < 32 → leAt d.arena (8 * n) 8 = 2 ^ n - 1
  /-- The categories' switch tables are after the arena's prefix (or not yet built, and their bases still the first
  past it). -/
  lo : ∀ i, arenaPre ≤ 2 * (d.baseTOf i).toNat ∧ arenaPre ≤ 2 * (d.baseCOf i).toNat
  le : d.arena.size ≤ d.arenaCap.toNat
  max : d.arenaCap.toNat + 2672 < 2 ^ 32
  capLe : d.arenaCap.toNat ≤ smallMax + d.arenaMax.toNat
  room : d.arenaMax.toNat + smallMax + 2672 < 2 ^ 32
  small : n ≤ 6 → d.arenaCap.toNat = smallMax
  cat : ∀ i, catIdx i < n → CatOk d i (g.catOf i)
  np : 3 < n → d.npostfix.toNat = g.m.npostfix ∧ d.ndirect.toNat = g.m.ndirect ∧ g.m.npostfix ≤ 3 ∧ g.m.ndirect ≤ 120
  modes : 4 < n → MapOk d.modes g.m.contextModes g.m.literal.n 4
  lmap : 5 < n → d.treesL.toNat = g.treesL ∧ 1 ≤ g.treesL ∧ g.treesL ≤ 256 ∧
    MapOk d.lMap g.m.literalMap (literalContextMapSize g.m.literal.n) g.treesL
  dmap : 6 < n → d.treesD.toNat = g.treesD ∧ 1 ≤ g.treesD ∧ g.treesD ≤ 256 ∧
    MapOk d.dMap g.m.distanceMap (distanceContextMapSize g.m.distance.n) g.treesD
  codes : ∀ k, ckIdx k + 7 < n → g.ckCount k = (g.codesOf k).length ∧
    CodesPart d.arena (d.basesOf k) (g.codesOf k) (g.ckCount k) (ckSize k g)
  /-- Once every code is read, the arena has room for the derived tables. -/
  fin : n = 10 → d.arena.size + tabMaxOf g ≤ d.arenaCap.toNat

/-- The array grew at its end only. -/
structure Keep (t t' : ByteArray) : Prop where
  four : t.size % 2 = 0
  le : t.size ≤ t'.size
  frame : ∀ q, q < t.size / 2 → slotAt t' q = slotAt t q

/-- A longer arena keeps every byte there was. -/
theorem Keep.byteN {t t' : ByteArray} (hk : Keep t t') {q : Nat} (hq : q < t.size) :
    _root_.Brotli.Decoder.byteN t' q = _root_.Brotli.Decoder.byteN t q := by
  have hs := hk.frame (q / 2) (by have := hk.four; omega)
  simp only [slotAt, slotNum, Prod.mk.injEq] at hs
  have e : ∀ a b : Nat, a = 16 * (a / 16) + a % 16 ∧ b = 16 * (b / 16) + b % 16 → a % 16 = b % 16 → a / 16 = b / 16 →
      a = b := fun a b h h1 h2 => by omega
  have hv := e _ _ ⟨(Nat.div_add_mod _ 16).symm, (Nat.div_add_mod _ 16).symm⟩ hs.1 hs.2
  have a0 := Brotli.Decoder.byteN_lt t' (2 * (q / 2))
  have a1 := Brotli.Decoder.byteN_lt t' (2 * (q / 2) + 1)
  have b0 := Brotli.Decoder.byteN_lt t (2 * (q / 2))
  have b1 := Brotli.Decoder.byteN_lt t (2 * (q / 2) + 1)
  unfold Brotli.Decoder.byteN at a0 a1 b0 b1 ⊢
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · rw [show q = 2 * (q / 2) by omega]
    omega
  · rw [show q = 2 * (q / 2) + 1 by omega]
    omega

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
  lo := h.lo

/-- The array changed only in its prefix, after the masks. -/
structure KeepAbove (t t' : ByteArray) : Prop where
  size : t'.size = t.size
  masks : ∀ q, q < 256 → t'.data[q]? = t.data[q]?
  above : ∀ q, arenaPre ≤ q → t'.data[q]? = t.data[q]?

theorem KeepAbove.slotAt {t t' : ByteArray} (hk : KeepAbove t t') {q : Nat} (hq : arenaPre ≤ 2 * q) :
    _root_.Brotli.Decoder.slotAt t' q = _root_.Brotli.Decoder.slotAt t q := by
  simp only [_root_.Brotli.Decoder.slotAt, slotNum]
  rw [hk.above _ hq, hk.above _ (by omega)]

theorem CatRel.frameAbove {t t' : ByteArray} {a b : USize} {c : BlockCategory} (h : CatRel t a b c) (hk : KeepAbove t t')
    (ha : arenaPre ≤ 2 * a.toNat) (hb : arenaPre ≤ 2 * b.toNat) : CatRel t' a b c where
  type hn := by
    obtain ⟨h1, h2⟩ := h.type hn
    exact ⟨h1.frameAbove hk.size fun q hq => hk.slotAt (by omega), h2⟩
  count hn := by
    obtain ⟨h1, h2⟩ := h.count hn
    exact ⟨h1.frameAbove hk.size fun q hq => hk.slotAt (by omega), h2⟩

theorem CodesPart.frameAbove {t t' bases : ByteArray} {cs : List PrefixCode} {total size : Nat}
    (h : CodesPart t bases cs total size) (hk : KeepAbove t t') : CodesPart t' bases cs total size where
  basesSize := h.basesSize
  le := h.le
  code i hi := by
    obtain ⟨c, h1, h2, h3⟩ := h.code i hi
    have hl := h.lo i hi
    exact ⟨c, h1, h2.frameAbove hk.size fun q hq => hk.slotAt (by omega), h3⟩
  lo := h.lo

/-- An arena changed only in its prefix, after the masks, keeps everything settled. -/
theorem Upto.frameAbove {d : Done} {g : Gh} {n : Nat} (h : Upto d g n) {a : ByteArray} (hk : KeepAbove d.arena a) :
    Upto { d with arena := a } g n where
  four := by rw [hk.size]; exact h.four
  pre := by rw [hk.size]; exact h.pre
  masks n hn := (leAt_congr fun q _ h2 => hk.masks q (by omega)).trans (h.masks n hn)
  lo := h.lo
  le := by rw [hk.size]; exact h.le
  max := h.max
  capLe := h.capLe
  room := h.room
  small := h.small
  cat i hi := by
    have hc := h.cat i hi
    have hl := h.lo i
    cases i <;> exact ⟨hc.n, hc.count, hc.rel.frameAbove hk hl.1 hl.2, hc.wf, hc.tc, hc.cc⟩
  np := h.np
  modes := h.modes
  lmap := h.lmap
  dmap := h.dmap
  codes k hk' := by
    obtain ⟨h1, h2⟩ := h.codes k hk'
    cases k <;> exact ⟨h1, h2.frameAbove hk⟩
  fin h' := by rw [hk.size]; exact h.fin h'

/-- A longer arena keeps everything settled. -/
theorem Upto.frame {d : Done} {g : Gh} {n : Nat} (h : Upto d g n) {a : ByteArray} (hk : Keep d.arena a) (h4 : a.size % 2 = 0)
    (hle : a.size ≤ d.arenaCap.toNat) (hn : n < 10) : Upto { d with arena := a } g n where
  fin h := absurd h (by omega)
  four := h4
  pre := Nat.le_trans h.pre hk.le
  masks n hn := by
    have hp := h.pre
    unfold arenaPre at hp
    exact (leAt_congrB fun q _ h2 => hk.byteN (by omega)).trans (h.masks n hn)
  lo := h.lo
  le := hle
  max := h.max
  capLe := h.capLe
  room := h.room
  small := h.small
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

/-- An owner's code is read before the header's last stage. -/
theorem ownerStage_lt (o : Owner) : ownerStage o < 10 := by
  cases o with
  | type i _ => cases i <;> simp [ownerStage, catIdx]
  | count i _ _ => cases i <;> simp [ownerStage, catIdx]
  | map isL _ _ => cases isL <;> simp [ownerStage, mapIdx]
  | codes k _ _ => cases k <;> simp [ownerStage, ckIdx]

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
  nzLe : st.clNz.toNat ≤ st.clIdx.toNat
  nzOne : (acc.filter (·.2 != 0)).length = 1 → ∃ l, acc.filter (·.2 != 0) = [(st.clSym.toNat, l)]
  symLt : st.clSym.toNat < 18

/-- The code lengths so far. -/
structure SymRel (st : Hd) (size : Nat) (clc : PrefixCode) (ls : LengthState) : Prop where
  table : TableOk st.clt.t (USize.ofNat 0).toNat clc
  complete : Complete clc
  symbols : clc.Symbols 18
  ln : st.ln.toNat = ls.lens.length
  le : ls.lens.length ≤ size
  /-- The lengths so far, as lists of each length's symbols. -/
  lists : ListsIs st.head st.next ls.lens
  small : ∀ l ∈ ls.lens, l ≤ 15
  prev : st.prevLen.toNat = ls.prev
  prevOk : 1 ≤ ls.prev ∧ ls.prev ≤ 15
  rep : match ls.rep with
    | some (s, c) => st.repSym.toNat = s ∧ st.repCount.toNat = c ∧ 3 ≤ c ∧ c ≤ ls.lens.length
    | none => st.repCount.toNat = 0
  sumOk : st.symSum.toNat = lengthSum ls.lens
  sumLe : lengthSum ls.lens ≤ 32768

/-- The move-to-front list after some indices. -/
def mtfAfter : List Nat → List Nat → List Nat
  | L, [] => L
  | L, idx :: v => mtfAfter (L.getD idx 0 :: L.eraseIdx idx) v

/-- A move-to-front list in an array. -/
structure MtfIs (m : ByteArray) (L : List Nat) : Prop where
  sz : m.size = 256
  length : L.length = 256
  at_ : ∀ k, k < 256 → L.getD k 0 = (m.data[k]?.getD 0).toNat

/-- Flags for the values below 256 that a list has. -/
structure SeenIs (flags : ByteArray) (l : List Nat) : Prop where
  sz : flags.size = 256
  at_ : ∀ t, t < 256 → (flags.data[t]?.getD 0 ≠ 0 ↔ t ∈ l)

/-- What a context map's values read so far hold for its last bit: the values transformed, with zeros after them, the
transform's list after them, and which values occur, as read and transformed. -/
structure XfRel (xf mtf seenR seenX : ByteArray) (done : List Nat) (size : Nat) : Prop where
  sz : xf.size = size
  at_ : ∀ i, i < done.length → (inverseMoveToFront done)[i]? = some (xf.data[i]?.getD 0).toNat
  zero : ∀ i, done.length ≤ i → xf.data[i]?.getD 0 = 0
  mtf : MtfIs mtf (mtfAfter (List.range 256) done)
  seenR : SeenIs seenR done
  seenX : SeenIs seenX (inverseMoveToFront done)

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
      (∀ i, done.length ≤ i → st.fill.data[i]?.getD 0 = 0) ∧ XfRel st.xf st.mtf st.seenR st.seenX done (mapSize g isL)
    | .imtf isL ntrees vals => st.tag = .imtf ∧ st.isL = isL ∧ st.ntrees.toNat = ntrees ∧ 2 ≤ ntrees ∧ ntrees ≤ 256 ∧
      MapOk st.fill vals (mapSize g isL) ntrees ∧ MapOk st.xf (inverseMoveToFront vals) (mapSize g isL) ntrees ∧
      SeenIs st.seenR vals ∧ SeenIs st.seenX (inverseMoveToFront vals)
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

/-- A category's place among the three. -/
def catN : Cat → Nat
  | .L => 2
  | .I => 1
  | .D => 0

/-- A group of codes' place among the three. -/
def ckN : CK → Nat
  | .L => 2
  | .I => 1
  | .D => 0

/-- A context map's place among the two. -/
def mapN : Bool → Nat
  | true => 5
  | false => 0

/-- How far from the header's end a prefix code's owner is. -/
def rankO : Owner → Nat × Nat
  | .type i _ => (17 + 4 * catN i, 0)
  | .count i _ _ => (16 + 4 * catN i, 0)
  | .map isL _ _ => (5 + mapN isL, 0)
  | .codes k _ left => (ckN k, 2 * left + 1)

/-- How far from the header's end a place is: where it is in the header, then where it is in a prefix code. -/
def rankH : HPhase → (Nat × Nat) × (Nat × Nat)
  | .cat i => ((18 + 4 * catN i, 0), (0, 0))
  | .code o _ => (rankO o, (3, 0))
  | .clens o _ order _ _ => (rankO o, (2, order.length))
  | .syms o size _ st => (rankO o, (1, size + 1 - st.lens.length))
  | .first i .. => ((15 + 4 * catN i, 0), (0, 0))
  | .np => ((14, 0), (0, 0))
  | .modes _ left => ((13, left), (0, 0))
  | .trees isL => ((7 + mapN isL, 0), (0, 0))
  | .rlemax isL _ => ((6 + mapN isL, 0), (0, 0))
  | .vals isL _ _ _ _ left => ((4 + mapN isL, left), (0, 0))
  | .imtf isL _ _ => ((3 + mapN isL, 0), (0, 0))
  | .codes k _ left => ((ckN k, 2 * left), (0, 0))

/-- A move nearer to the header's end. -/
def HDown (p p' : HPhase) : Prop :=
  LexLt (rankH p').1 (rankH p).1 ∨ ((rankH p').1 = (rankH p).1 ∧ LexLt (rankH p').2 (rankH p).2)

/-- Settles `HDown` for a move whose places are spelled out. -/
macro "hstep_down" : tactic =>
  `(tactic| (simp only [HDown, rankH, rankO, catN, ckN, mapN, LexLt, Prod.mk.injEq, List.length_cons, true_and]; omega))

/-- The places of the groups of codes are those nearest the header's end. -/
theorem stage_post (p : HPhase) : 7 ≤ stageOf p ↔ (rankH p).1.1 ≤ 2 := by
  have ho : ∀ o : Owner, 7 ≤ ownerStage o ↔ (rankO o).1 ≤ 2 := by
    intro o
    cases o with
    | type i n => cases i <;> simp [ownerStage, rankO, catIdx, catN]
    | count i n tc => cases i <;> simp [ownerStage, rankO, catIdx, catN]
    | map isL a b => cases isL <;> simp [ownerStage, rankO, mapIdx, mapN]
    | codes k d l => cases k <;> simp [ownerStage, rankO, ckIdx, ckN]
  cases p with
  | cat i => cases i <;> simp [stageOf, rankH, catIdx, catN]
  | code o _ => exact ho o
  | clens o _ _ _ _ => exact ho o
  | syms o _ _ _ => exact ho o
  | first i _ _ _ => cases i <;> simp [stageOf, rankH, catIdx, catN]
  | np => simp [stageOf, rankH]
  | modes _ _ => simp [stageOf, rankH]
  | trees isL => cases isL <;> simp [stageOf, rankH, mapIdx, mapN]
  | rlemax isL _ => cases isL <;> simp [stageOf, rankH, mapIdx, mapN]
  | vals isL _ _ _ _ _ => cases isL <;> simp [stageOf, rankH, mapIdx, mapN]
  | imtf isL _ _ => cases isL <;> simp [stageOf, rankH, mapIdx, mapN]
  | codes k _ _ => cases k <;> simp [stageOf, rankH, ckIdx, ckN]

/-- A move nearer to the header's end doesn't leave the groups of codes. -/
theorem stage_down {p p' : HPhase} (h : HDown p p') (hp : 7 ≤ stageOf p) : 7 ≤ stageOf p' := by
  rw [stage_post] at hp ⊢
  rcases h with h | ⟨h, _⟩
  · unfold LexLt at h
    omega
  · rw [h]
    exact hp

/-- After a category, nearer to the header's end. -/
theorem catNext_down (i : Cat) : HDown (.cat i) (catNextPhase i) := by
  cases i <;> simp only [catNextPhase] <;> hstep_down

/-- After a category's first count, nearer to the header's end. -/
theorem firstNext_down (i : Cat) (n : Nat) (tc cc : PrefixCode) : HDown (.first i n tc cc) (catNextPhase i) := by
  cases i <;> simp only [catNextPhase] <;> hstep_down

/-- After a context map's number of trees, nearer to the header's end. -/
theorem treesNext_down (g : Gh) (isL : Bool) : HDown (.trees isL) (mapNextPhase g isL) := by
  cases isL <;> simp only [mapNextPhase] <;> hstep_down

/-- After a context map's last bit, nearer to the header's end. -/
theorem imtfNext_down (g : Gh) (isL : Bool) (ntrees : Nat) (vals : List Nat) : HDown (.imtf isL ntrees vals) (mapNextPhase g isL) := by
  cases isL <;> simp only [mapNextPhase] <;> hstep_down

/-- How many bytes a prefix code's table takes. -/
def tableBytes : PrefixCode → Nat
  | .single _ => 512
  | .canonical l => 2 * (256 + offSum (depths l) 256)

/-- What a header's move does to its reading besides moving: builds a prefix code's table, or reserves the groups'
tables once every group's number of trees is known. -/
inductive Hook where
  | table (c : PrefixCode)
  | res (g : Gh)

/-- How many bytes a move's table takes, if it builds one. -/
def tableOf : Option Hook → Nat
  | some (.table c) => tableBytes c
  | _ => 0

/-- What a move does to a header's reading: the groups' reservation is hooked. -/
def Wr {α : Type} (K : HK α) : Option Hook → Option α → Option α
  | some (.res g), x => K.r g x
  | _, x => x

/-- For the spec's own reading, a move does nothing besides moving. -/
theorem Wr_id {α : Type} {K : HK α} (hr : ∀ g x, K.r g x = x) (oc : Option Hook) (x : Option α) : Wr K oc x = x := by
  match oc with
  | none => rfl
  | some (.table _) => rfl
  | some (.res g) => exact hr g x

/-- A complete code's table takes at most `treeMax` of its alphabet's size. -/
theorem tableBytes_le {c : PrefixCode} {size : Nat} (hC : Complete c) (hs : c.Symbols size) : tableBytes c ≤ treeMax size := by
  cases c with
  | single _ => show 512 ≤ 2 * (size + 376); omega
  | canonical lens =>
    have h1 := offSum_le hC
    have h2 := longCount_le lens
    have h3 : lens.length = size := hs
    show 2 * (256 + offSum (depths lens) 256) ≤ 2 * (size + 376)
    omega

/-- The bytes a header's reading holds outside the arena, with bounds set by the format. -/
structure HSize (st : Hd) : Prop where
  fill : st.fill.size ≤ 16384
  /-- The lists of each length's symbols. -/
  lens : st.head.size ≤ 32 ∧ st.next.size ≤ 1408
  clLens : st.clLens.size ≤ 18
  /-- `treeMax 18`. -/
  clt : st.clt.t.size ≤ 788
  /-- `treeMax 272`: a context map's alphabet has at most 256 trees and 16 run lengths. -/
  mapT : st.mapT.t.size ≤ 1296
  modes : st.d.modes.size ≤ 256
  lMap : st.d.lMap.size ≤ 16384
  dMap : st.d.dMap.size ≤ 1024
  litBase : st.d.litBase.size ≤ 1024
  icBase : st.d.icBase.size ≤ 1024
  dBase : st.d.dBase.size ≤ 1024
  /-- A context map's transformed values, the transform's list and the values' flags. -/
  work : st.xf.size ≤ 16384 ∧ st.mtf.size ≤ 256 ∧ st.seenR.size ≤ 256 ∧ st.seenX.size ≤ 256

/-- The bytes the groups' tables can take from a group on, with `left` of its codes to go, and then the derived
tables. -/
def groupsFrom (g : Gh) : CK → Nat → Nat
  | .L, left => left * treeMax (ckSize .L g) + g.m.insertCopy.n * treeMax (ckSize .I g) + g.treesD * treeMax (ckSize .D g) +
      tabMaxOf g
  | .I, left => left * treeMax (ckSize .I g) + g.treesD * treeMax (ckSize .D g) + tabMaxOf g
  | .D, left => left * treeMax (ckSize .D g) + tabMaxOf g

/-- What the decoder reserves for the groups' tables once both context maps are read. -/
def resBytes (g : Gh) : Nat := groupsFrom g .L g.treesL

/-- The bytes an owner's code and the codes after it in the arena can take, until the next reservation. -/
def budO (g : Gh) : Owner → Nat
  | .type i _ => catMax * (catN i + 1)
  | .count i _ _ => catMax * catN i + treeMax 26
  | .map .. => 0
  | .codes k _ left => groupsFrom g k (left + 1)

/-- The bytes the arena's tables from a place on can take, until the next reservation. -/
def budH (g : Gh) : HPhase → Nat
  | .cat i => catMax * (catN i + 1)
  | .code o _ => budO g o
  | .clens o .. => budO g o
  | .syms o .. => budO g o
  | .first i .. => catMax * catN i
  | .codes k _ left => groupsFrom g k left
  | _ => 0

/-- The most the groups' tables can take, 256 codes in each group over at most 520 distance symbols, with the derived
tables. -/
def resMax : Nat := 256 * (treeMax 256 + treeMax 704 + treeMax 520) + tabMax 256 256 256

theorem tabMaxOf_le (g : Gh) : tabMaxOf g ≤ tabMax 256 256 256 := by
  unfold tabMaxOf tabMax
  omega

/-- What the groups' tables can take, with each group's number of codes at most 256 and NPOSTFIX and NDIRECT in range. -/
theorem resBytes_bound {g : Gh} (hT : g.treesL ≤ 256) (hI : g.m.insertCopy.n ≤ 256) (hD : g.treesD ≤ 256)
    (hp : g.m.npostfix ≤ 3) (hn : g.m.ndirect ≤ 120) : resBytes g ≤ resMax := by
  have key : ∀ x, x < 4 → 48 <<< x ≤ 384 := by decide
  have hk := key _ (show g.m.npostfix < 4 by omega)
  have hs : ckSize .D g ≤ 520 := by
    show 16 + g.m.ndirect + (48 <<< g.m.npostfix) ≤ 520
    omega
  have a1 := Nat.mul_le_mul_right (treeMax 256) hT
  have a2 := Nat.mul_le_mul_right (treeMax 704) hI
  have a3 : g.treesD * treeMax (ckSize .D g) ≤ 256 * treeMax 520 := Nat.mul_le_mul hD (by unfold treeMax; omega)
  have a4 := tabMaxOf_le g
  show g.treesL * treeMax 256 + g.m.insertCopy.n * treeMax 704 + g.treesD * treeMax (ckSize .D g) + tabMaxOf g ≤
    256 * (treeMax 256 + treeMax 704 + treeMax 520) + tabMax 256 256 256
  rw [Nat.mul_add, Nat.mul_add]
  omega

/-- What a move does to the arena's reservation: the groups' reservation, made while the arena holds the categories'
reservation, makes it the categories' tables and what the groups' tables can take, and any other move keeps it, with what
the tables still to come can take lowered by the table added. -/
def CapMove (st r : Hd) (g : Gh) (p : HPhase) (g' : Gh) (p' : HPhase) : Option Hook → Prop
  | some (.res g0) => r.d.arenaCap.toNat = r.d.arena.size + resBytes g0 ∧ budH g' p' = resBytes g0 ∧
    st.d.arenaCap.toNat = smallMax ∧ resBytes g0 ≤ st.d.arenaMax.toNat ∧ stageOf p ≤ 6 ∧ 7 ≤ stageOf p'
  | oc => r.d.arenaCap = st.d.arenaCap ∧ budH g' p' + tableOf oc ≤ budH g p

theorem CapMove.same {st1 st r : Hd} {g g' : Gh} {p p' : HPhase} {oc : Option Hook} (hd : st1.d = st.d)
    (h : CapMove st1 r g p g' p' oc) : CapMove st r g p g' p' oc := by
  match oc with
  | some (.res _) => exact ⟨h.1, h.2.1, by rw [← hd]; exact h.2.2.1, by rw [← hd]; exact h.2.2.2.1, h.2.2.2.2⟩
  | none => exact ⟨by rw [h.1, hd], h.2⟩
  | some (.table _) => exact ⟨by rw [h.1, hd], h.2⟩

/-- What a move does to what a header's reading holds. -/
structure HMove (st r : Hd) (g : Gh) (p : HPhase) (g' : Gh) (p' : HPhase) (oc : Option Hook) : Prop where
  max : r.d.arenaMax = st.d.arenaMax
  grow : r.d.arena.size = st.d.arena.size + tableOf oc
  size : HSize st → HSize r
  cap : CapMove st r g p g' p' oc

/-- Settles `HMove` for a move that adds no table and leaves the arrays alone. -/
macro "hstep_move" : tactic =>
  `(tactic| exact ⟨rfl, rfl, fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩,
    ⟨rfl, by simp only [budH, budO, groupsFrom, catN, ckN, tableOf]; omega⟩⟩)

/-- Two settled records with the same arrays. -/
structure SameArrays (d' d : Done) : Prop where
  arena : d'.arena = d.arena
  max : d'.arenaMax = d.arenaMax
  cap : d'.arenaCap = d.arenaCap
  modes : d'.modes = d.modes
  lMap : d'.lMap = d.lMap
  dMap : d'.dMap = d.dMap
  litBase : d'.litBase = d.litBase
  icBase : d'.icBase = d.icBase
  dBase : d'.dBase = d.dBase

theorem SameArrays.rfl' {d : Done} : SameArrays d d := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setN_arrays (d : Done) (i : Cat) (v : UInt64) : SameArrays (d.setN i v) d := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setCount_arrays (d : Done) (i : Cat) (v : UInt64) : SameArrays (d.setCount i v) d := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setBaseT_arrays (d : Done) (i : Cat) (v : USize) : SameArrays (d.setBaseT i v) d := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem setBaseC_arrays (d : Done) (i : Cat) (v : USize) : SameArrays (d.setBaseC i v) d := by
  cases i <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Two states holding the same arrays. -/
structure Arr (r st : Hd) : Prop where
  d : SameArrays r.d st.d
  fill : r.fill = st.fill
  lens : (r.head, r.next) = (st.head, st.next)
  clLens : r.clLens = st.clLens
  clt : r.clt = st.clt
  mapT : r.mapT = st.mapT
  work : r.xf = st.xf ∧ r.mtf = st.mtf ∧ r.seenR = st.seenR ∧ r.seenX = st.seenX

theorem Arr.trans {a b c : Hd} (h1 : Arr a b) (h2 : Arr b c) : Arr a c where
  d := ⟨h1.d.arena.trans h2.d.arena, h1.d.max.trans h2.d.max, h1.d.cap.trans h2.d.cap, h1.d.modes.trans h2.d.modes, h1.d.lMap.trans h2.d.lMap, h1.d.dMap.trans h2.d.dMap,
    h1.d.litBase.trans h2.d.litBase, h1.d.icBase.trans h2.d.icBase, h1.d.dBase.trans h2.d.dBase⟩
  fill := h1.fill.trans h2.fill
  lens := h1.lens.trans h2.lens
  clLens := h1.clLens.trans h2.clLens
  clt := h1.clt.trans h2.clt
  mapT := h1.mapT.trans h2.mapT
  work := ⟨h1.work.1.trans h2.work.1, h1.work.2.1.trans h2.work.2.1, h1.work.2.2.1.trans h2.work.2.2.1,
    h1.work.2.2.2.trans h2.work.2.2.2⟩

/-- A move that adds no table and keeps the arrays. -/
theorem HMove.ofArr {st r : Hd} {g g' : Gh} {p p' : HPhase} (h : Arr r st) (hc : budH g' p' ≤ budH g p) : HMove st r g p g' p' none where
  max := h.d.max
  grow := by rw [h.d.arena]; rfl
  size hs := {
    fill := by rw [h.fill]; exact hs.fill
    lens := by obtain ⟨e1, e2⟩ := Prod.mk.inj h.lens; rw [e1, e2]; exact hs.lens
    clLens := by rw [h.clLens]; exact hs.clLens
    clt := by rw [h.clt]; exact hs.clt
    mapT := by rw [h.mapT]; exact hs.mapT
    modes := by rw [h.d.modes]; exact hs.modes
    lMap := by rw [h.d.lMap]; exact hs.lMap
    dMap := by rw [h.d.dMap]; exact hs.dMap
    litBase := by rw [h.d.litBase]; exact hs.litBase
    icBase := by rw [h.d.icBase]; exact hs.icBase
    dBase := by rw [h.d.dBase]; exact hs.dBase
    work := by rw [h.work.1, h.work.2.1, h.work.2.2.1, h.work.2.2.2]; exact hs.work }
  cap := ⟨h.d.cap, by simpa [tableOf] using hc⟩

/-- A move that adds no table and leaves the settled part alone. -/
theorem HMove.ofD {st r : Hd} {g g' : Gh} {p p' : HPhase} (hd : r.d = st.d) (hs : HSize st → HSize r) (hc : budH g' p' ≤ budH g p) :
    HMove st r g p g' p' none where
  max := by rw [hd]
  grow := by rw [hd]; rfl
  size := hs
  cap := ⟨by rw [hd], by simpa [tableOf] using hc⟩

/-- A move keeps room in the arena's reservation for the tables still to come. -/
theorem HMove.bud {st r : Hd} {g g' : Gh} {p p' : HPhase} {oc : Option Hook} (hm : HMove st r g p g' p' oc)
    (h : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) : r.d.arena.size + budH g' p' ≤ r.d.arenaCap.toNat := by
  have hg := hm.grow
  have hc := hm.cap
  match oc with
  | some (.res g0) =>
    obtain ⟨c1, c2, _⟩ := hc
    have e1 : tableOf (some (.res g0)) = 0 := rfl
    rw [e1] at hg
    omega
  | none =>
    obtain ⟨c1, c2⟩ := hc
    have e1 : tableOf none = 0 := rfl
    rw [e1] at hg c2
    rw [c1]
    omega
  | some (.table c) =>
    obtain ⟨c1, c2⟩ := hc
    have e1 : tableOf (some (.table c)) = tableBytes c := rfl
    rw [e1] at hg c2
    rw [c1]
    omega

/-- After a category, the categories' codes still to come. -/
theorem catNext_bud (i : Cat) (g g' : Gh) : budH g' (catNextPhase i) ≤ budH g (.cat i) := by
  cases i <;> simp only [catNextPhase, budH, catN] <;> omega

/-- After a category's first count, the categories' codes still to come. -/
theorem firstNext_bud (i : Cat) (n : Nat) (tc cc : PrefixCode) (g g' : Gh) : budH g' (catNextPhase i) ≤ budH g (.first i n tc cc) := by
  cases i <;> simp only [catNextPhase, budH, catN] <;> omega

/-- What a header step must do. It is `StepOk` for a header's places, and a header is finished when all of it is read.
Moving on goes where the header's reading in order goes, needing input means the reading in order has too few bits at
the place, and finishing is where it ends. -/
structure HStepOk {α : Type} (K : HK α) (a : ByteArray) (stop : USize) (g : Gh) (p : HPhase)
    (st : Hd) (pos : USize) (r : Hd) : Prop where
  next : r.status = .next → ∃ g' p' oc, HRel r g' p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, hrest K g p (availBits st.word st.count a pos stop F) = Wr K oc (hrest K g' p' (availBits r.word r.count a r.pos stop F))) ∧ HDown p p' ∧ HMove st r g p g' p' oc ∧
    ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) = .next (g', p') (availBits r.word r.count a r.pos stop F)
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ HRel r g p ∧
    (∀ F, hrest K g p (availBits st.word st.count a pos stop F) = hrest K g p (availBits r.word r.count a r.pos stop F)) ∧
    hrest K g p (BitBuffer.mk r.word r.count).held = none ∧ HMove st r g p g p none ∧
    (∀ F, availBits r.word r.count a r.pos stop F = availBits st.word st.count a pos stop F) ∧
    hStepP (g, p) (BitBuffer.mk r.word r.count).held = .short
  bad : r.status = .bad → ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = none
  /-- The groups' tables would pass the arena's limit. -/
  memory : r.status = .memory → ∃ g', st.d.arenaMax.toNat < resBytes g' ∧ resBytes g' ≤ resMax ∧ st.d.arenaCap.toNat = smallMax ∧
    ∀ F, ∃ x, hrest K g p (availBits st.word st.count a pos stop F) = K.r g' x
  ready : r.status = .ready → ∃ g', Upto r.d g' 10 ∧ (BitBuffer.mk r.word r.count).Wf ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ F, hrest K g p (availBits st.word st.count a pos stop F) = K.k g'.m (availBits r.word r.count a r.pos stop F)) ∧ r.d.arenaMax = st.d.arenaMax ∧
    r.d.arena.size = st.d.arena.size ∧ r.d.arenaCap = st.d.arenaCap ∧ (HSize st → HSize r) ∧
    ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) = .exit g'.m (availBits r.word r.count a r.pos stop F)

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize} {g : Gh} {p : HPhase}
  {st : Hd} {pos : USize} {r : Hd}

/-- A step that moved on. -/
theorem HStepOk.ofNext (hs : r.status = .next) {g' : Gh} {p' : HPhase} (hrel : HRel r g' p') (h1 : pos.toNat ≤ r.pos.toNat)
    (h2 : r.pos.toNat ≤ stop.toNat)
    (h : ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = hrest K g' p' (availBits r.word r.count a r.pos stop F))
    (hj : ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) = .next (g', p') (availBits r.word r.count a r.pos stop F))
    (hd : HDown p p' := by hstep_down) (hm : HMove st r g p g' p' none := by hstep_move) :
    HStepOk K a stop g p st pos r :=
  ⟨fun _ => ⟨g', p', none, hrel, h1, h2, h, hd, hm, hj⟩, fun e => HStatus.noConfusion (hs.symm.trans e),
    fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e),
    fun e => HStatus.noConfusion (hs.symm.trans e)⟩

/-- A step that rejected. -/
theorem HStepOk.ofBad (hs : r.status = .bad) (h : ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = none) :
    HStepOk K a stop g p st pos r :=
  ⟨fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e), fun _ => h,
    fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e)⟩

/-- A read that fell short and changed nothing. -/
theorem HStepOk.ofShort (hrel : HRel st g p) (hstop : pos = stop) (hn : hrest K g p (BitBuffer.mk st.word st.count).held = none)
    (hsh : hStepP (g, p) (BitBuffer.mk st.word st.count).held = .short) :
    HStepOk K a stop g p st pos (markH st pos .needsInput) :=
  ⟨fun e => HStatus.noConfusion e,
    fun _ => ⟨hstop, by rw [hstop]; exact Nat.le_refl _, hrel.mark _ _, (fun _ => rfl), hn, by hstep_move, (fun _ => rfl), hsh⟩,
    fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e⟩

/-- What a refill leaves alone. -/
structure SameHeld (st1 st : Hd) : Prop where
  d : st1.d = st.d
  fill : st1.fill = st.fill
  lens : (st1.head, st1.next) = (st.head, st.next)
  clLens : st1.clLens = st.clLens
  clt : st1.clt = st.clt
  mapT : st1.mapT = st.mapT
  work : st1.xf = st.xf ∧ st1.mtf = st.mtf ∧ st1.seenR = st.seenR ∧ st1.seenX = st.seenX

theorem HSize.same {st1 st : Hd} (h : HSize st) (he : SameHeld st1 st) : HSize st1 where
  fill := by rw [he.fill]; exact h.fill
  lens := by obtain ⟨e1, e2⟩ := Prod.mk.inj he.lens; rw [e1, e2]; exact h.lens
  clLens := by rw [he.clLens]; exact h.clLens
  clt := by rw [he.clt]; exact h.clt
  mapT := by rw [he.mapT]; exact h.mapT
  modes := by rw [he.d]; exact h.modes
  lMap := by rw [he.d]; exact h.lMap
  dMap := by rw [he.d]; exact h.dMap
  litBase := by rw [he.d]; exact h.litBase
  icBase := by rw [he.d]; exact h.icBase
  dBase := by rw [he.d]; exact h.dBase
  work := by rw [he.work.1, he.work.2.1, he.work.2.2.1, he.work.2.2.2]; exact h.work

theorem HMove.same {st1 : Hd} {g1 g2 : Gh} {p1 p2 : HPhase} {oc : Option Hook} (h : HMove st1 r g1 p1 g2 p2 oc) (he : SameHeld st1 st) :
    HMove st r g1 p1 g2 p2 oc where
  max := by rw [h.max, he.d]
  grow := by rw [h.grow, he.d]
  size := fun hs => h.size (hs.same he)
  cap := h.cap.same he.d

/-- A step taken after a refill is a step from before it. -/
theorem HStepOk.refilled {st1 : Hd} {pos1 : USize} (h : HStepOk K a stop g p st1 pos1 r)
    (hb : ∀ F, availBits st.word st.count a pos stop F = availBits st1.word st1.count a pos1 stop F) (h1 : pos.toNat ≤ pos1.toNat)
    (h2 : pos1.toNat ≤ stop.toNat) (he : SameHeld st1 st) : HStepOk K a stop g p st pos r where
  next e := by
    obtain ⟨g', p', oc, hrel, h3, h4, h5, h6, h7, h8⟩ := h.next e
    exact ⟨g', p', oc, hrel, Nat.le_trans h1 h3, h4, (fun F => by rw [hb]; exact h5 F), h6, h7.same he, fun F => by rw [hb]; exact h8 F⟩
  needsInput e := by
    obtain ⟨h3, _, hrel, h5, h6, h7, h8, h9⟩ := h.needsInput e
    exact ⟨h3, Nat.le_trans h1 h2, hrel, (fun F => by rw [hb]; exact h5 F), h6, h7.same he, (fun F => by rw [hb]; exact h8 F), h9⟩
  bad e := fun F => by rw [hb]; exact h.bad e F
  memory e := by
    obtain ⟨g', h3, h4, h5, h6⟩ := h.memory e
    rw [he.d] at h3 h5
    exact ⟨g', h3, h4, h5, fun F => by rw [hb]; exact h6 F⟩
  ready e := by
    obtain ⟨g', h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h.ready e
    exact ⟨g', h3, h4, Nat.le_trans h1 h5, h6, (fun F => by rw [hb]; exact h7 F), by rw [h8, he.d], by rw [h9, he.d], by rw [h10, he.d],
      fun hs => h11 (hs.same he), fun F => by rw [hb]; exact h12 F⟩

end

end Brotli.Decoder
