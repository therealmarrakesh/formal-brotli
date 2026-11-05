import Brotli.Decoder.HeaderStep3

/-!
# A prefix code finished

When a prefix code has been read, its table is built: into the arena if it stays for the meta-block, into a table of its own
if it's a context map's. `tableDone` does that and moves on to what the code was for.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### What a built table gives -/

/-- A table appended to an array. -/
structure Built (t t' : ByteArray) (c : PrefixCode) : Prop where
  ok : TableOk t' (t.size / 2) c
  keep : Keep t t'
  four : t'.size % 2 = 0

theorem built_canonical {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h : LensArgs t lens n) :
    Built t (buildLens t lens n hn h) (.canonical (lensOf lens n.toNat)) ∧
      (buildLens t lens n hn h).size = t.size + tableBytes (.canonical (lensOf lens n.toNat)) := by
  rw [buildLens_eq h]
  obtain ⟨hC, h704, ht, _⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := buildDown_spec (t := t) hC ht (by rw [length_lensOf hn]; exact h704)
  refine ⟨⟨h1, ⟨ht, by omega, h3⟩, h2⟩, ?_⟩
  rw [h4]
  simp only [tableSlots, tableBytes]

theorem built_single {t : ByteArray} {sym : UInt64} (hsym : sym.toNat < 4096) (h : t.size + 2672 < 2 ^ 32 ∧ t.size % 2 = 0) :
    Built t (buildSingleFast t sym h) (.single sym.toNat) ∧ (buildSingleFast t sym h).size = t.size + 512 := by
  rw [buildSingleFast_eq h hsym]
  obtain ⟨h1, h2, h3, h4⟩ := buildSingle_spec (t := t) (sym := sym.toNat) h.2 hsym
  exact ⟨⟨h1, ⟨h.2, by omega, h3⟩, h2⟩, h4⟩

/-- What is settled has an arena of whole slots with room for a table. -/
theorem Upto.arenaOk {d : Done} {g : Gh} {n : Nat} (hu : Upto d g n) : d.arena.size % 2 = 0 ∧ d.arena.size + 2672 < 2 ^ 32 := by
  have := hu.le
  have := hu.max
  exact ⟨hu.four, by omega⟩

/-- The arena a header's reading holds has whole slots and room for a table. -/
theorem HRel.arenaOk {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) :
    st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32 :=
  h.2.1.arenaOk

theorem hrel_arena {st : Hd} (h : ∃ g p, HRel st g p) : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32 := by
  obtain ⟨_, _, hr⟩ := h
  exact hr.arenaOk

/-! ### 32-bit values in an array -/

/-- Writes a 32-bit value, the `i`th of an array. -/
@[inline] def u32Set (b : ByteArray) (i v : UInt64) : ByteArray :=
  setU (setU (setU (setU b (i * 4 + 0).toUSize v.toUInt8) (i * 4 + 1).toUSize (v >>> 8).toUInt8) (i * 4 + 2).toUSize (v >>> 16).toUInt8)
    (i * 4 + 3).toUSize (v >>> 24).toUInt8

private theorem p4 {i j : UInt64} (hi : i.toNat < 2 ^ 16) (hj : j.toNat ≤ 3) : (i * 4 + j).toUSize.toNat = 4 * i.toNat + j.toNat := by
  have h4 : (i * 4).toNat = 4 * i.toNat := by
    rw [UInt64.toNat_mul, show (4 : UInt64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  have e : (i * 4 + j).toNat = 4 * i.toNat + j.toNat := by
    rw [UInt64.toNat_add, h4]
    exact Nat.mod_eq_of_lt (by omega)
  rw [word_toUSize (by rw [e]; omega), e]

theorem size_u32Set (b : ByteArray) (i v : UInt64) : (u32Set b i v).size = b.size := by
  simp only [u32Set, size_setU]

/-- Writes a 32-bit value, the `i`th of an array, that is in the array. -/
@[inline] def u32SetU (b : ByteArray) (i v : UInt64) (h : 4 * i.toNat + 3 < b.size ∧ i.toNat < 2 ^ 16) : ByteArray :=
  (((b.uset (i * 4 + 0).toUSize v.toUInt8 (by rw [p4 h.2 (by decide)]; show 4 * i.toNat + 0 < _; omega)).uset (i * 4 + 1).toUSize (v >>> 8).toUInt8
    (by rw [size_uset', p4 h.2 (by decide)]; show 4 * i.toNat + 1 < _; omega)).uset (i * 4 + 2).toUSize (v >>> 16).toUInt8
    (by rw [size_uset', size_uset', p4 h.2 (by decide)]; show 4 * i.toNat + 2 < _; omega)).uset (i * 4 + 3).toUSize (v >>> 24).toUInt8
    (by rw [size_uset', size_uset', size_uset', p4 h.2 (by decide)]; show 4 * i.toNat + 3 < _; omega)

theorem u32SetU_eq (b : ByteArray) (i v : UInt64) (h : 4 * i.toNat + 3 < b.size ∧ i.toNat < 2 ^ 16) :
    u32SetU b i v h = u32Set b i v := by
  simp only [u32SetU, u32Set, uset_setU]

/-- The other values stay. -/
theorem u32At_set_ne {b : ByteArray} {i v : UInt64} {j : Nat} (hi : i.toNat < 2 ^ 16) (hj : j ≠ i.toNat) :
    u32At (u32Set b i v) j = u32At b j := by
  have h0 := p4 (i := i) (j := 0) hi (by decide)
  have h1 := p4 (i := i) (j := 1) hi (by decide)
  have h2 := p4 (i := i) (j := 2) hi (by decide)
  have h3 := p4 (i := i) (j := 3) hi (by decide)
  have e0 : (0 : UInt64).toNat = 0 := rfl
  have e1 : (1 : UInt64).toNat = 1 := rfl
  have e2 : (2 : UInt64).toNat = 2 := rfl
  have e3 : (3 : UInt64).toNat = 3 := rfl
  unfold u32At u32Set
  have key : ∀ k, k ≤ 3 → ∀ x, (setU (setU (setU (setU b (i * 4 + 0).toUSize v.toUInt8) (i * 4 + 1).toUSize (v >>> 8).toUInt8)
      (i * 4 + 2).toUSize (v >>> 16).toUInt8) (i * 4 + 3).toUSize (v >>> 24).toUInt8).data[4 * j + k]?.getD x = b.data[4 * j + k]?.getD x := by
    intro k hk x
    rw [setU_get_ne (by rw [h3, e3]; omega), setU_get_ne (by rw [h2, e2]; omega), setU_get_ne (by rw [h1, e1]; omega),
      setU_get_ne (by rw [h0, e0]; omega)]
  have k0 := key 0 (by omega) 0
  have k1 := key 1 (by omega) 0
  have k2 := key 2 (by omega) 0
  have k3 := key 3 (by omega) 0
  simp only [Nat.add_zero] at k0
  rw [k0, k1, k2, k3]

private theorem shift_byte (v k : UInt64) (hk : k.toNat < 64) : (v >>> k).toUInt8.toNat = v.toNat / 2 ^ k.toNat % 256 := by
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]

/-- The value written reads back. -/
theorem u32At_set_same {b : ByteArray} {i v : UInt64} (hi : i.toNat < 2 ^ 16) (hs : 4 * i.toNat + 3 < b.size) (hv : v.toNat < 2 ^ 32) :
    u32At (u32Set b i v) i.toNat = v.toNat := by
  have h0 := p4 (i := i) (j := 0) hi (by decide)
  have h1 := p4 (i := i) (j := 1) hi (by decide)
  have h2 := p4 (i := i) (j := 2) hi (by decide)
  have h3 := p4 (i := i) (j := 3) hi (by decide)
  have e0 : (0 : UInt64).toNat = 0 := rfl
  have e1 : (1 : UInt64).toNat = 1 := rfl
  have e2 : (2 : UInt64).toNat = 2 := rfl
  have e3 : (3 : UInt64).toNat = 3 := rfl
  rw [e0, Nat.add_zero] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  generalize hb1 : setU b (i * 4 + 0).toUSize v.toUInt8 = b1
  have s1 : b1.size = b.size := by rw [← hb1, size_setU]
  generalize hb2 : setU b1 (i * 4 + 1).toUSize (v >>> 8).toUInt8 = b2
  have s2 : b2.size = b.size := by rw [← hb2, size_setU, s1]
  generalize hb3 : setU b2 (i * 4 + 2).toUSize (v >>> 16).toUInt8 = b3
  have s3 : b3.size = b.size := by rw [← hb3, size_setU, s2]
  have g3 : (setU b3 (i * 4 + 3).toUSize (v >>> 24).toUInt8).data[4 * i.toNat + 3]?.getD 0 = (v >>> 24).toUInt8 := by
    have := setU_get_same (t := b3) (i := (i * 4 + 3).toUSize) (v := (v >>> 24).toUInt8) (by rw [h3, s3]; exact hs)
    rwa [h3] at this
  have g2 : (setU b3 (i * 4 + 3).toUSize (v >>> 24).toUInt8).data[4 * i.toNat + 2]?.getD 0 = (v >>> 16).toUInt8 := by
    rw [setU_get_ne (by rw [h3]; omega), ← hb3]
    have := setU_get_same (t := b2) (i := (i * 4 + 2).toUSize) (v := (v >>> 16).toUInt8) (by rw [h2, s2]; omega)
    rwa [h2] at this
  have g1 : (setU b3 (i * 4 + 3).toUSize (v >>> 24).toUInt8).data[4 * i.toNat + 1]?.getD 0 = (v >>> 8).toUInt8 := by
    rw [setU_get_ne (by rw [h3]; omega), ← hb3, setU_get_ne (by rw [h2]; omega), ← hb2]
    have := setU_get_same (t := b1) (i := (i * 4 + 1).toUSize) (v := (v >>> 8).toUInt8) (by rw [h1, s1]; omega)
    rwa [h1] at this
  have g0 : (setU b3 (i * 4 + 3).toUSize (v >>> 24).toUInt8).data[4 * i.toNat]?.getD 0 = v.toUInt8 := by
    rw [setU_get_ne (by rw [h3]; omega), ← hb3, setU_get_ne (by rw [h2]; omega), ← hb2, setU_get_ne (by rw [h1]; omega), ← hb1]
    have := setU_get_same (t := b) (i := (i * 4 + 0).toUSize) (v := v.toUInt8) (by rw [h0]; omega)
    rwa [h0] at this
  unfold u32At u32Set
  rw [hb1, hb2, hb3, g0, g1, g2, g3, shift_byte v 8 (by decide), shift_byte v 16 (by decide), shift_byte v 24 (by decide),
    UInt64.toNat_toUInt8]
  show v.toNat % 256 + 256 * (v.toNat / 256 % 256) + 65536 * (v.toNat / 65536 % 256) + 16777216 * (v.toNat / 16777216 % 256) = _
  omega

/-! ### Going on after a table -/

/-- What `installTable` needs of a state's role, index and bases: a group's code has room for its base. -/
def InstallOk (role : Role) (idx : UInt64) (fill : ByteArray) : Prop :=
  role = .codes → 4 * idx.toNat + 3 < fill.size ∧ idx.toNat < 2 ^ 16

/-- Records a table in the arena for what it was for. A context map's table is not in the arena (`tableDone`). -/
def installTable (st : Hd) (base : UInt64) (hi : InstallOk st.role st.idx st.fill) : Hd :=
  match hr : st.role with
  | .type => { st with d := st.d.setBaseT st.cat base.toUSize, tag := .code, role := .count, size := 26 }
  | .count => { st with d := st.d.setBaseC st.cat base.toUSize, tag := .first }
  | .codes =>
    let fill := st.fill
    let idx := st.idx
    let st0 := clearFill st
    { st0 with fill := u32SetU fill idx base (hi hr), idx := idx + 1, tag := .codes }
  | .map => st

theorem installTable_spec (st : Hd) (base : UInt64) (hi : InstallOk st.role st.idx st.fill) : (installTable st base hi).word = st.word ∧
    (installTable st base hi).count = st.count ∧ (installTable st base hi).pos = st.pos ∧ (installTable st base hi).status = st.status ∧
    (installTable st base hi).d.arenaMax = st.d.arenaMax ∧ (installTable st base hi).d.arenaCap = st.d.arenaCap := by
  unfold installTable
  split
  · cases st.cat <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases st.cat <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {st : Hd} {base : UInt64} {hi : InstallOk st.role st.idx st.fill}

/-- Settles `installTable`'s role, given its equation. -/
macro "install_tac" h:ident : tactic =>
  `(tactic| (unfold installTable; split <;> rename_i e <;>
    first | exact absurd (Eq.trans (Eq.symm $h) e) (fun x => Role.noConfusion x) | rfl | (simp only [u32SetU_eq]; done)))

theorem installTable_type (h : st.role = .type) :
    installTable st base hi = { st with d := st.d.setBaseT st.cat base.toUSize, tag := .code, role := .count, size := 26 } := by
  install_tac h

theorem installTable_count (h : st.role = .count) :
    installTable st base hi = { st with d := st.d.setBaseC st.cat base.toUSize, tag := .first } := by
  install_tac h

theorem installTable_codes (h : st.role = .codes) :
    installTable st base hi = { clearFill st with fill := u32Set st.fill st.idx base, idx := st.idx + 1, tag := .codes } := by
  install_tac h

theorem installTable_map (h : st.role = .map) : installTable st base hi = st := by
  install_tac h

end

/-- Empties a settled record's arena, as `clearRing` does a state's window. -/
@[noinline] def clearArena (d : Done) : Done := { d with arena := ByteArray.empty }

/-- A settled record with nothing in it, to hold a state's place while the real one is written. -/
def Done.none : Done := ⟨ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ByteArray.empty, ByteArray.empty,
  ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Appends a canonical table to the arena, from the state's lists of each length's symbols. -/
@[inline] def growLens (st : Hd) (h : ∃ L, BuildArgs st.d.arena st.head st.next L) : Hd :=
  let d := st.d
  let st0 := clearDone st Done.none
  let arena := d.arena
  let d0 := clearArena d
  { st0 with d := { d0 with arena := buildFast arena st0.head st0.next h } }

/-- Appends a single symbol's table to the arena. -/
@[inline] def growSingle (st : Hd) (sym : UInt64) (h : st.d.arena.size + 2672 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0) : Hd :=
  let d := st.d
  let st0 := clearDone st Done.none
  let arena := d.arena
  let d0 := clearArena d
  { st0 with d := { d0 with arena := buildSingleFast arena sym h } }

/-- Growing the arena keeps what `installTable` needs. Stated apart, so that no check compares the grown state with the old
one, which would compute the table. -/
theorem growSingle_ok {st : Hd} {sym : UInt64} {h : st.d.arena.size + 2672 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0}
    (hi : InstallOk st.role st.idx st.fill) :
    InstallOk (growSingle st sym h).role (growSingle st sym h).idx (growSingle st sym h).fill := by
  unfold growSingle clearDone
  exact hi

theorem growLens_ok {st : Hd} {h : ∃ L, BuildArgs st.d.arena st.head st.next L} (hi : InstallOk st.role st.idx st.fill) :
    InstallOk (growLens st h).role (growLens st h).idx (growLens st h).fill := by
  unfold growLens clearDone
  exact hi

theorem growLens_eq (st : Hd) (h : ∃ L, BuildArgs st.d.arena st.head st.next L) :
    growLens st h = { st with d := { st.d with arena := buildFast st.d.arena st.head st.next h } } := rfl

theorem growSingle_eq (st : Hd) (sym : UInt64) (h : st.d.arena.size + 2672 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0) :
    growSingle st sym h = { st with d := { st.d with arena := buildSingleFast st.d.arena sym h } } := rfl

/-- The transform's first list. -/
def mtfInitLut : ByteArray := ((List.range 256).map Nat.toUInt8).toByteArray

private theorem mtfInit_values : ∀ k, k < 256 → (List.range 256).getD k 0 = (((List.range 256).map Nat.toUInt8)[k]?.getD 0).toNat := by
  decide +kernel

theorem mtfInit_is : MtfIs mtfInitLut (List.range 256) := by
  refine ⟨by simp [mtfInitLut, List.size_toByteArray], by simp, fun k hk => ?_⟩
  rw [mtfInit_values k hk]
  simp only [mtfInitLut, List.data_toByteArray, List.getElem?_toArray]

theorem SeenIs.zero : SeenIs (zeroBytes 256) [] :=
  ⟨zeroBytes_size (by decide), fun t ht => by rw [zeroBytes_get (by decide)]; simp⟩

/-- Before a context map's values: zeros, the transform's first list, and no value seen. -/
theorem XfRel.start {n size : Nat} {m : ByteArray} (hn : n = size) (h : n < 2 ^ 32) (hm : MtfIs m (List.range 256)) :
    XfRel (zeroBytes n) m (zeroBytes 256) (zeroBytes 256) [] size :=
  ⟨by rw [zeroBytes_size h, hn], fun i hi => absurd hi (by simp), fun i _ => zeroBytes_get h, hm, SeenIs.zero, SeenIs.zero⟩

/-- Builds a map's table on its own and goes on to the map's values: the values as read and transformed start as zeros,
with the transform's first list and no value seen. -/
@[inline] def mapTableDone (st : Hd) (t : ByteArray) (hf : t.size < 2 ^ 32 ∧ TableFits t (USize.ofNat 0).toNat) : Hd :=
  let size := mapSizeFast st
  { st with
    tag := .vals, idx := 0, left := UInt64.ofNat size, fill := zeroBytes size, xf := zeroBytes size, mtf := mtfInitLut
    seenR := zeroBytes 256, seenX := zeroBytes 256
    mapT := ⟨t, hf.1, hf.2⟩ }

/-- A prefix code `c` that was read, for `tableDone`: a complete code over `size` symbols, with one symbol `sym` if `single`
and otherwise its lengths given by the lists of each length's symbols in `head` and `next`. -/
structure TableFor (size : UInt64) (head next : ByteArray) (single : Bool) (sym : UInt64) (c : PrefixCode) : Prop where
  small : size.toNat ≤ 704
  one : single = true → c = .single sym.toNat
  canon : single = false → ∃ L, c = .canonical L ∧ L.length = size.toNat ∧ ListsIs head next L
  hsz : head.size < 2 ^ 32
  nsz : next.size < 2 ^ 32
  complete : Complete c
  symbols : c.Symbols size.toNat

/-- Some prefix code that was read. -/
def TableArgs (size : UInt64) (head next : ByteArray) (single : Bool) (sym : UInt64) : Prop :=
  ∃ c, TableFor size head next single sym c

/-- A single symbol's code that was read has a symbol below 4096. -/
theorem tableArgs_sym {size : UInt64} {head next : ByteArray} {single : Bool} {sym : UInt64}
    (ha : TableArgs size head next single sym) (hs : single = true) : sym.toNat < 4096 := by
  obtain ⟨c, hf⟩ := ha
  have hc := hf.one hs
  have hsy := hf.symbols
  have h704 := hf.small
  subst hc
  have : sym.toNat < size.toNat := hsy
  omega

/-- A canonical code that was read can be built on an arena of whole slots with room. -/
theorem tableArgs_build {size : UInt64} {head next : ByteArray} {single : Bool} {sym : UInt64}
    (ha : TableArgs size head next single sym) (hs : ¬ single = true) {t : ByteArray}
    (ht : t.size % 2 = 0 ∧ t.size + 2672 < 2 ^ 32) : ∃ L, BuildArgs t head next L := by
  obtain ⟨c, hf⟩ := ha
  obtain ⟨L, hc, hlen, hl⟩ := hf.canon (by cases single <;> simp_all)
  have hC := hf.complete
  rw [hc] at hC
  exact ⟨L, hC, by have := hf.small; omega, hl, hf.hsz, hf.nsz, ht.1, ht.2⟩

/-- The room a context map's table is built in: its alphabet's `treeMax`, so that it grows in place. -/
def soloCap : Nat := treeMax 272

/-- The table of a code that was read, on its own, built in an array with room for it. -/
@[inline] def soloTable (head next : ByteArray) (single : Bool) (sym : UInt64) (size : UInt64)
    (ha : TableArgs size head next single sym) : ByteArray :=
  if hs : single = true then buildSingleFast (freshBytes soloCap) sym (by show 0 + 2672 < _ ∧ 0 % 2 = 0; decide)
  else buildFast (freshBytes soloCap) head next (tableArgs_build ha hs (by show 0 % 2 = 0 ∧ 0 + 2672 < _; decide))

/-- A canonical table built from lists is the code's, and takes its `tableBytes`. -/
theorem built_fast {t head next : ByteArray} {L : List Nat} (ha : BuildArgs t head next L) (h : ∃ L, BuildArgs t head next L) :
    Built t (buildFast t head next h) (.canonical L) ∧ (buildFast t head next h).size = t.size + tableBytes (.canonical L) := by
  rw [buildFast_eq ha h]
  obtain ⟨hC, h704, _, _, _, ht, _⟩ := ha
  obtain ⟨h1, h2, h3, h4⟩ := buildDown_spec (t := t) hC ht h704
  refine ⟨⟨h1, ⟨ht, by omega, h3⟩, h2⟩, ?_⟩
  rw [h4]
  simp only [tableSlots, tableBytes]

/-- The table of a code that was read is the code's, and at most `treeMax` of its alphabet. -/
theorem soloTable_built {size : UInt64} {head next : ByteArray} {single : Bool} {sym : UInt64} {c : PrefixCode}
    (hf : TableFor size head next single sym c) (ha : TableArgs size head next single sym) :
    Built ByteArray.empty (soloTable head next single sym size ha) c ∧
      (soloTable head next single sym size ha).size ≤ treeMax size.toNat := by
  have h0 : (freshBytes soloCap).size = 0 := rfl
  unfold soloTable
  by_cases hb : single = true
  · rw [dite_eq_left hb]
    have hc := hf.one hb
    obtain ⟨b1, b2⟩ := built_single (t := freshBytes soloCap) (tableArgs_sym ha hb)
      (by show 0 + 2672 < _ ∧ 0 % 2 = 0; decide)
    rw [hc]
    refine ⟨b1, ?_⟩
    rw [b2, h0]
    unfold treeMax
    omega
  · rw [dite_eq_right hb]
    obtain ⟨L, hc, hlen, hl⟩ := hf.canon (by cases single <;> simp_all)
    have hC := hf.complete
    rw [hc] at hC
    obtain ⟨b1, b2⟩ := built_fast (t := freshBytes soloCap)
      ⟨hC, by have := hf.small; omega, hl, hf.hsz, hf.nsz, rfl, by decide⟩ _
    refine ⟨by rw [hc]; exact b1, ?_⟩
    have htb := tableBytes_le hC (show PrefixCode.Symbols size.toNat (.canonical L) from hlen)
    rw [b2, h0, Nat.zero_add]
    exact htb

/-- The table of a code that was read fits. -/
theorem soloTable_fits {size : UInt64} {head next : ByteArray} {single : Bool} {sym : UInt64}
    (ha : TableArgs size head next single sym) :
    (soloTable head next single sym size ha).size < 2 ^ 32 ∧
      TableFits (soloTable head next single sym size ha) (USize.ofNat 0).toNat := by
  obtain ⟨c, hf⟩ := id ha
  have h704 := hf.small
  obtain ⟨hB, hsz⟩ := soloTable_built hf ha
  rw [usize_zero']
  unfold treeMax at hsz
  refine ⟨?_, hB.ok.toTableFits⟩
  generalize (soloTable head next single sym size ha).size = z at hsz ⊢
  omega

/-- What happens once a prefix code has been read: `single` says that it has one symbol, and otherwise its lengths' lists
are in the state's `head` and `next`. The arena's reservation always has room for the table (`budH`), so nothing is
checked. -/
def tableDone (st : Hd) (single : Bool) (sym : UInt64) (ha : TableArgs st.size st.head st.next single sym)
    (hi : InstallOk st.role st.idx st.fill) (har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32) : Hd :=
  match st.role with
  | .map => mapTableDone st (soloTable st.head st.next single sym st.size ha) (soloTable_fits ha)
  | _ =>
    let base := UInt64.ofNat (st.d.arena.size / 2)
    if hs : single = true then installTable (growSingle st sym ⟨har.2, har.1⟩) base (growSingle_ok hi)
    else installTable (growLens st (tableArgs_build ha hs har)) base (growLens_ok hi)

/-! ### What happens after a table, in the spec's terms -/

private theorem setBaseT_nOf (d : Done) (i j : Cat) (v : USize) : (d.setBaseT i v).nOf j = d.nOf j := by
  cases i <;> cases j <;> rfl

private theorem setBaseT_baseTOf (d : Done) (i : Cat) (v : USize) : (d.setBaseT i v).baseTOf i = v := by cases i <;> rfl

private theorem setBaseT_arena (d : Done) (i : Cat) (v : USize) :
    (d.setBaseT i v).arena = d.arena ∧ (d.setBaseT i v).arenaMax = d.arenaMax ∧ (d.setBaseT i v).arenaCap = d.arenaCap := by
  cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem setBaseT_others (d : Done) (i : Cat) (v : USize) : ∀ j, j ≠ i →
    (d.setBaseT i v).nOf j = d.nOf j ∧ (d.setBaseT i v).countOf j = d.countOf j ∧ (d.setBaseT i v).baseTOf j = d.baseTOf j ∧
      (d.setBaseT i v).baseCOf j = d.baseCOf j := by
  intro j hne
  cases i <;> cases j <;> first | exact absurd rfl hne | exact ⟨rfl, rfl, rfl, rfl⟩

private theorem setBaseC_nOf (d : Done) (i j : Cat) (v : USize) : (d.setBaseC i v).nOf j = d.nOf j := by
  cases i <;> cases j <;> rfl

private theorem setBaseC_baseTOf (d : Done) (i j : Cat) (v : USize) : (d.setBaseC i v).baseTOf j = d.baseTOf j := by
  cases i <;> cases j <;> rfl

private theorem setBaseC_baseCOf (d : Done) (i : Cat) (v : USize) : (d.setBaseC i v).baseCOf i = v := by cases i <;> rfl

private theorem setBaseC_arena (d : Done) (i : Cat) (v : USize) :
    (d.setBaseC i v).arena = d.arena ∧ (d.setBaseC i v).arenaMax = d.arenaMax ∧ (d.setBaseC i v).arenaCap = d.arenaCap := by
  cases i <;> exact ⟨rfl, rfl, rfl⟩

private theorem setBaseC_others (d : Done) (i : Cat) (v : USize) : ∀ j, j ≠ i →
    (d.setBaseC i v).nOf j = d.nOf j ∧ (d.setBaseC i v).countOf j = d.countOf j ∧ (d.setBaseC i v).baseTOf j = d.baseTOf j ∧
      (d.setBaseC i v).baseCOf j = d.baseCOf j := by
  intro j hne
  cases i <;> cases j <;> first | exact absurd rfl hne | exact ⟨rfl, rfl, rfl, rfl⟩

theorem installTable_arena (st : Hd) (base : UInt64) (hi : InstallOk st.role st.idx st.fill) :
    (installTable st base hi).d.arena = st.d.arena := by
  unfold installTable
  split
  · cases st.cat <;> rfl
  · cases st.cat <;> rfl
  · rfl
  · rfl

theorem installTable_size (st : Hd) (base : UInt64) (hi : InstallOk st.role st.idx st.fill) (h : HSize st) :
    HSize (installTable st base hi) := by
  unfold installTable
  split
  · cases st.cat <;> exact ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
  · cases st.cat <;> exact ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
  · rename_i e
    exact ⟨by show (u32SetU st.fill st.idx base (hi e)).size ≤ _; rw [u32SetU_eq, size_u32Set]; exact h.fill,
      h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
  · exact h

section
variable {α : Type} (K : HK α)

/-- A table in the arena, for anything but a context map: the state moves to what the code was for. -/
theorem install_ok {st : Hd} {g : Gh} {o : Owner} {size : Nat} {c : PrefixCode} {A1 : ByteArray} {base : UInt64}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hu : Upto st.d g (ownerStage o)) (hs : SizeOk st size) (ho : OwnerRel st g size o)
    (hk : Keep st.d.arena A1) (h4 : A1.size % 2 = 0) (hle : A1.size ≤ st.d.arenaCap.toNat) (htab : TableOk A1 base.toNat c)
    (hb : base.toNat = st.d.arena.size / 2) (hC : Complete c) (hsy : c.Symbols size) (hm : ∀ a b e, o ≠ .map a b e)
    {hi : InstallOk st.role st.idx st.fill} :
    ∃ g' p', HRel (installTable { st with d := { st.d with arena := A1 } } base hi) g' p' ∧ (∀ bs, ownerK K g o c bs = hrest K g' p' bs) ∧
      LexLt (rankH p').1 (rankO o) ∧ budH g' p' + treeMax size ≤ budO g o ∧ (g', p') = (g, ownerPlace g o c) := by
  have hup := hu.frame hk h4 hle
  have hsmall : st.d.arena.size < 2 ^ 32 := by
    have := hu.le
    have := hu.max
    omega
  have hbU : base.toUSize.toNat = base.toNat := word_toUSize (by omega)
  cases o with
  | map a b e => exact absurd rfl (hm a b e)
  | type i n =>
    obtain ⟨hrole, hci, hn, h2, h256, hsz⟩ := ho
    subst hci
    subst hsz
    rw [installTable_type (st := { st with d := { st.d with arena := A1 } }) hrole]
    refine ⟨g, .code (.count st.cat n c) blockCountAlphabetSize, ⟨hw, ?_, rfl, ⟨rfl, by decide, by decide⟩, rfl, rfl, ?_, h2, h256, rfl, ?_, hC, hsy⟩, (fun bs => rfl),
      by simp only [rankH, rankO, LexLt]; omega, by simp only [budH, budO, catMax, treeMax, blockTypeAlphabetSize]; omega, rfl⟩
    · have ha := setBaseT_arena { st.d with arena := A1 } st.cat base.toUSize
      exact Upto.setSame hup ha.1 ha.2.1 ha.2.2 (setBaseT_others _ _ _)
    · show (({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).nOf st.cat).toNat = n
      rw [setBaseT_nOf]
      cases hc : st.cat <;> rw [hc] at hn <;> exact hn
    · show TableOk ({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).arena
        (({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).baseTOf st.cat).toNat c
      rw [setBaseT_baseTOf, (setBaseT_arena _ _ _).1, hbU]
      exact htab
  | count i n tc =>
    obtain ⟨hrole, hci, hn, h2, h256, hsz, hT, hTc, hTs⟩ := ho
    subst hci
    subst hsz
    rw [installTable_count (st := { st with d := { st.d with arena := A1 } }) hrole]
    have hT' : TableOk A1 (st.d.baseTOf st.cat).toNat tc := hT.frame hk.four hk.le hk.frame
    refine ⟨g, .first st.cat n tc c, ⟨hw, ?_, rfl, rfl, ?_, h2, h256, ?_, hTc, hTs, ?_, hC, hsy⟩, (fun bs => rfl),
      by simp only [rankH, rankO, LexLt]; omega, by simp only [budH, budO, blockCountAlphabetSize]; omega, rfl⟩
    · have ha := setBaseC_arena { st.d with arena := A1 } st.cat base.toUSize
      exact Upto.setSame hup ha.1 ha.2.1 ha.2.2 (setBaseC_others _ _ _)
    · show (({ st.d with arena := A1 }.setBaseC st.cat base.toUSize).nOf st.cat).toNat = n
      rw [setBaseC_nOf]
      cases hc : st.cat <;> rw [hc] at hn <;> exact hn
    · show TableOk ({ st.d with arena := A1 }.setBaseC st.cat base.toUSize).arena
        (({ st.d with arena := A1 }.setBaseC st.cat base.toUSize).baseTOf st.cat).toNat tc
      rw [setBaseC_baseTOf, (setBaseC_arena _ _ _).1]
      cases hc : st.cat <;> rw [hc] at hT' <;> exact hT'
    · show TableOk ({ st.d with arena := A1 }.setBaseC st.cat base.toUSize).arena
        (({ st.d with arena := A1 }.setBaseC st.cat base.toUSize).baseCOf st.cat).toNat c
      rw [setBaseC_baseCOf, (setBaseC_arena _ _ _).1, hbU]
      exact htab
  | codes k done left =>
    obtain ⟨hrole, hk', hidx, hleft, hsz, hlen, h256, hpart⟩ := ho
    subst hk'
    subst hsz
    rw [installTable_codes (st := { st with d := { st.d with arena := A1 } }) hrole]
    dsimp only
    have hbase : base.toNat < 2 ^ 32 := by omega
    have hidx16 : st.idx.toNat < 2 ^ 16 := by omega
    have hidx1 : (st.idx + 1).toNat = done.length + 1 := by
      rw [UInt64.toNat_add, hidx, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨g, .codes st.ck (done ++ [c]) left, ⟨hw, hup, rfl, rfl, by simpa using hidx1, hleft, ?_, h256, ?_⟩, (fun bs => rfl),
      Or.inr ⟨rfl, show 2 * left < 2 * left + 1 by omega⟩, by cases st.ck <;> simp only [budH, budO, groupsFrom, Nat.add_mul, Nat.one_mul] <;> omega, rfl⟩
    · simp only [List.length_append, List.length_singleton]
      omega
    · refine ⟨?_, by simp only [List.length_append, List.length_singleton]; omega, fun i hi => ?_⟩
      · show (u32Set st.fill st.idx base).size = _
        rw [size_u32Set]
        exact hpart.basesSize
      · simp only [List.length_append, List.length_singleton] at hi
        by_cases he : i = done.length
        · subst he
          refine ⟨c, by simp, ?_, hC, hsy⟩
          show TableOk A1 (u32At (u32Set st.fill st.idx base) done.length) c
          rw [← hidx, u32At_set_same hidx16 (by have := hpart.basesSize; omega) hbase]
          exact htab
        · obtain ⟨c1, h1, h2, h3⟩ := hpart.code i (by omega)
          refine ⟨c1, by rw [List.getElem?_append_left (by omega)]; exact h1, ?_, h3⟩
          show TableOk A1 (u32At (u32Set st.fill st.idx base) i) c1
          rw [u32At_set_ne hidx16 (by omega)]
          exact h2.frame hk.four hk.le hk.frame

/-- A state with an owner has what `installTable` needs. -/
theorem OwnerRel.install {st : Hd} {g : Gh} {size : Nat} {o : Owner} (ho : OwnerRel st g size o) :
    InstallOk st.role st.idx st.fill := by
  intro hr
  cases o with
  | codes k done left =>
    obtain ⟨_, _, hidx, _, _, hlen, h256, hpart⟩ := ho
    have := hpart.basesSize
    omega
  | type i n => exact absurd (ho.1.symm.trans hr) (fun e => Role.noConfusion e)
  | count i n tc => exact absurd (ho.1.symm.trans hr) (fun e => Role.noConfusion e)
  | map a b c => exact absurd (ho.1.symm.trans hr) (fun e => Role.noConfusion e)

/-- What `tableDone` leaves. -/
structure TableDone (g : Gh) (o : Owner) (c : PrefixCode) (st r : Hd) : Prop where
  bits : r.word = st.word ∧ r.count = st.count ∧ r.pos = st.pos
  next : r.status = .next → ∃ g' p' oc, HRel r g' p' ∧ (∀ bs, ownerK K g o c bs = Wr K oc (hrest K g' p' bs)) ∧ LexLt (rankH p').1 (rankO o) ∧
    (∀ q, budH g q = budO g o → HMove st r g q g' p' oc) ∧ (g', p') = (g, ownerPlace g o c)
  status : r.status = st.status

/-- What `tableDone` does in the spec's terms. -/
theorem tableDone_ok {st : Hd} {g : Gh} {o : Owner} {size : Nat} {c : PrefixCode} {single : Bool} {sym : UInt64}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hu : Upto st.d g (ownerStage o)) (hs : SizeOk st size) (ho : OwnerRel st g size o)
    (hf : TableFor st.size st.head st.next single sym c) (hb : st.d.arena.size + budO g o ≤ st.d.arenaCap.toNat)
    {ha : TableArgs st.size st.head st.next single sym} {hi : InstallOk st.role st.idx st.fill}
    {har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32} :
    TableDone K g o c st (tableDone st single sym ha hi har) := by
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hs : SizeOk st size := ⟨hs1, hs2, hs3⟩
  have hC := hf.complete
  have hsy : c.Symbols size := by rw [← hs1]; exact hf.symbols
  have hsmall : st.d.arena.size + 2672 < 2 ^ 32 := by
    have := hu.le
    have := hu.max
    omega
  unfold tableDone
  dsimp only
  by_cases hmap : st.role = .map
  · rw [hmap]
    dsimp only
    cases o with
    | type i n => exact absurd (hmap.symm.trans ho.1) (by decide)
    | count i n tc => exact absurd (hmap.symm.trans ho.1) (by decide)
    | codes k done left => exact absurd (hmap.symm.trans ho.1) (by decide)
    | map isL ntrees rlemax =>
      obtain ⟨_, hi, hn, hr, h2, h256, h16, hsz⟩ := ho
      have hbuilt : Built ByteArray.empty (soloTable st.head st.next single sym st.size ha) c ∧
          (soloTable st.head st.next single sym st.size ha).size ≤ 1296 := by
        obtain ⟨b1, b2⟩ := soloTable_built hf ha
        have hsz' : size ≤ 272 := by rw [hsz]; unfold contextMapAlphabetSize; omega
        unfold treeMax at b2
        rw [hs1] at b2
        exact ⟨b1, Nat.le_trans b2 (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hsz' 376))⟩
      obtain ⟨hB, hsize⟩ := hbuilt
      unfold mapTableDone
      obtain ⟨hmf, hml⟩ := mapSizeFast_eq (g := g) hi hu
      dsimp only
      have hleft : (UInt64.ofNat (mapSizeFast st)).toNat = mapSize g isL := by
        rw [hmf]
        exact u64_lit (by omega)
      have hzs : (zeroBytes (mapSizeFast st)).size = mapSize g isL := by
        rw [hmf]
        exact zeroBytes_size (by omega)
      have hMI := mtfInit_is
      generalize mtfInitLut = M at hMI ⊢
      have hm256 : M.size ≤ 256 := Nat.le_of_eq hMI.sz
      have hz256 : (zeroBytes 256).size ≤ 256 := Nat.le_of_eq SeenIs.zero.sz
      refine ⟨⟨rfl, rfl, rfl⟩, fun _ => ⟨g, .vals isL ntrees rlemax c [] (mapSize g isL), none, ⟨hw, hu, rfl, hi, hn, hr, h2, h256, h16, ?_, hC, ?_,
        rfl, hleft, by show 0 + _ = _; omega, hzs, by simp, by simp, fun i _ => ?_, ?_⟩, (fun bs => rfl), by simp only [rankH, rankO, LexLt]; omega,
        fun q hq => ⟨rfl, rfl, fun h => ⟨by rw [hzs]; exact hml, h.lens, h.clLens, h.clt, hsize, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase,
            ⟨by rw [hzs]; exact hml, hm256, hz256, hz256⟩⟩,
          ⟨rfl, by rw [hq]; simp [budH, budO, tableOf]⟩⟩, rfl⟩, rfl⟩
      · rw [usize_zero']
        exact hB.ok
      · rw [← hsz]
        exact hsy
      · show (zeroBytes (mapSizeFast st)).data[i]?.getD 0 = 0
        rw [hmf]
        exact zeroBytes_get (by omega)
      · exact XfRel.start hmf (by omega) hMI
  · have hrole : ∀ a b e, o ≠ .map a b e := by
      intro a b e he
      subst he
      exact hmap ho.1
    have htb := tableBytes_le hC hsy
    have hbo : treeMax size ≤ budO g o := by
      have ho' := ho
      cases o with
      | map a b e => exact absurd rfl (hrole a b e)
      | type i n =>
        obtain ⟨_, _, _, _, h256, hsz⟩ := ho'
        subst hsz
        simp only [budO, catMax, treeMax, blockTypeAlphabetSize]
        omega
      | count i n tc =>
        obtain ⟨_, _, _, _, _, hsz, _⟩ := ho'
        subst hsz
        simp only [budO, treeMax, blockCountAlphabetSize]
        omega
      | codes k done left =>
        obtain ⟨_, _, _, _, hsz, _⟩ := ho'
        subst hsz
        cases k <;> simp only [budO, groupsFrom, Nat.add_mul, Nat.one_mul] <;> omega
    have hroom : st.d.arena.size + tableBytes c ≤ st.d.arenaCap.toNat := by omega
    have hstart : (match st.role with
        | .map => mapTableDone st (soloTable st.head st.next single sym st.size ha) (soloTable_fits ha)
        | _ =>
          if hs : single = true then installTable (growSingle st sym ⟨har.2, har.1⟩) (UInt64.ofNat (st.d.arena.size / 2)) (growSingle_ok hi)
          else installTable (growLens st (tableArgs_build ha hs har)) (UInt64.ofNat (st.d.arena.size / 2)) (growLens_ok hi)) =
        (if hs : single = true then installTable (growSingle st sym ⟨har.2, har.1⟩) (UInt64.ofNat (st.d.arena.size / 2)) (growSingle_ok hi)
          else installTable (growLens st (tableArgs_build ha hs har)) (UInt64.ofNat (st.d.arena.size / 2)) (growLens_ok hi)) := by
      cases hr : st.role with
      | map => exact absurd hr hmap
      | type => rfl
      | count => rfl
      | codes => rfl
    rw [hstart]
    have hbase : (UInt64.ofNat (st.d.arena.size / 2)).toNat = st.d.arena.size / 2 := u64_lit (by omega)
    have hfinish : ∀ {A1 : ByteArray} {S : Hd} {hS : InstallOk S.role S.idx S.fill}, S = { st with d := { st.d with arena := A1 } } →
        Built st.d.arena A1 c → A1.size ≤ st.d.arenaCap.toNat → A1.size = st.d.arena.size + tableBytes c →
        TableDone K g o c st (installTable S (UInt64.ofNat (st.d.arena.size / 2)) hS) := by
      intro A1 S hS e hB hle hgrow
      subst e
      have hok : TableOk A1 (UInt64.ofNat (st.d.arena.size / 2)).toNat c := by
        rw [hbase]
        exact hB.ok
      obtain ⟨g', p', h1, h2, h3, h4, h5⟩ := install_ok K hw hu hs ho hB.keep hB.four hle hok hbase hC hsy hrole (hi := hS)
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := installTable_spec { st with d := { st.d with arena := A1 } } (UInt64.ofNat (st.d.arena.size / 2)) hS
      refine ⟨⟨b1, b2, b3⟩, fun _ => ⟨g', p', some (.table c), h1, h2, h3, fun q hq => ⟨b5, ?_, ?_, ⟨b6, ?_⟩⟩, h5⟩, b4⟩
      · rw [installTable_arena]
        exact hgrow
      · intro h
        exact installTable_size _ _ _ ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
      · show budH g' p' + tableBytes c ≤ budH g q
        rw [hq]
        omega
    by_cases hsb : single = true
    · rw [dite_eq_left hsb]
      obtain ⟨h1, h2⟩ := built_single (t := st.d.arena) (tableArgs_sym ha hsb) ⟨har.2, har.1⟩
      have := hf.one hsb
      subst this
      exact hfinish (growSingle_eq st _ _) h1 (by rw [h2]; exact hroom) h2
    · rw [dite_eq_right hsb]
      obtain ⟨L, hc, hlen, hl⟩ := hf.canon (by cases single <;> simp_all)
      have hCL := hC
      rw [hc] at hCL
      obtain ⟨h1, h2⟩ := built_fast (t := st.d.arena) ⟨hCL, by have := hf.small; omega, hl, hf.hsz, hf.nsz, har.1, har.2⟩
        (tableArgs_build ha hsb har)
      have hB : Built st.d.arena (buildFast st.d.arena st.head st.next (tableArgs_build ha hsb har)) c := by
        rw [hc]
        exact h1
      exact hfinish (growLens_eq st _) hB (by rw [h2, ← hc]; exact hroom) (by rw [h2, ← hc])

end

end Brotli.Decoder
