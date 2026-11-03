import Brotli.Decoder.HeaderStep3

/-!
# A prefix code finished

When a prefix code has been read, its table is built: into the arena if it stays for the meta-block, into a table of its own
if it's a context map's. `tableDone` does that and moves on to what the code was for.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### What a built table gives -/

/-- A table appended to an array. -/
structure Built (t t' : ByteArray) (c : PrefixCode) : Prop where
  ok : TableOk t' (t.size / 4) c
  keep : Keep t t'
  four : t'.size % 4 = 0

theorem built_canonical {t lens : ByteArray} {n : USize} {hn : n.toNat ≤ lens.size} (h64 : n.toNat < 65536)
    (hC : Complete (.canonical (lensOf lens n.toNat))) (ht : t.size % 4 = 0) (hsize : t.size + 4 * (256 + 32768) < 2 ^ 32) :
    Built t (buildFast t lens n hn) (.canonical (lensOf lens n.toNat)) ∧
      (buildFast t lens n hn).size = t.size + 4 * (256 + offSum (depths (lensOf lens n.toNat)) 256) := by
  rw [buildFast_eq h64 hC hsize]
  obtain ⟨h1, h2, h3, h4⟩ := buildCanonical_spec (t := t) hC ht (by rw [length_lensOf hn]; omega)
  exact ⟨⟨h1, ⟨ht, by omega, h3⟩, h2⟩, h4⟩

theorem built_single {t : ByteArray} {sym : UInt64} (hsym : sym.toNat < 65536) (ht : t.size % 4 = 0) (hsize : t.size + 4 * 256 < 2 ^ 32) :
    Built t (buildSingleFast t sym) (.single sym.toNat) ∧ (buildSingleFast t sym).size = t.size + 1024 := by
  rw [buildSingleFast_eq hsize]
  obtain ⟨h1, h2, h3, h4⟩ := buildSingle_spec (t := t) (sym := sym.toNat) ht hsym
  exact ⟨⟨h1, ⟨ht, by omega, h3⟩, h2⟩, h4⟩

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

/-- Records a table in the arena for what it was for. -/
def installTable (st : Hd) (base : UInt64) : Hd :=
  match st.role with
  | .type => { st with d := st.d.setBaseT st.cat base.toUSize, tag := .code, role := .count, size := 26 }
  | .count => { st with d := st.d.setBaseC st.cat base.toUSize, tag := .first }
  | _ =>
    let fill := st.fill
    let idx := st.idx
    let st0 := clearFill st
    { st0 with fill := u32Set fill idx base, idx := idx + 1, tag := .codes }

theorem installTable_spec (st : Hd) (base : UInt64) : (installTable st base).word = st.word ∧ (installTable st base).count = st.count ∧
    (installTable st base).pos = st.pos ∧ (installTable st base).status = st.status ∧ (installTable st base).d.arenaMax = st.d.arenaMax := by
  unfold installTable
  split
  · cases st.cat <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases st.cat <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Empties a settled record's arena, as `clearRing` does a state's window. -/
@[noinline] def clearArena (d : Done) : Done := { d with arena := ByteArray.empty }

/-- A settled record with nothing in it, to hold a state's place while the real one is written. -/
def Done.none : Done := ⟨ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ByteArray.empty, ByteArray.empty,
  ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Appends a canonical table to the arena, having checked its size. -/
@[inline] def growPlanned (st : Hd) (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) (p : Plan) : Hd :=
  let d := st.d
  let st0 := clearDone st Done.none
  let arena := d.arena
  let d0 := clearArena d
  { st0 with d := { d0 with arena := fillFast arena lens n hn p } }

/-- Appends a single symbol's table to the arena. -/
@[inline] def growSingle (st : Hd) (sym : UInt64) : Hd :=
  let d := st.d
  let st0 := clearDone st Done.none
  let arena := d.arena
  let d0 := clearArena d
  { st0 with d := { d0 with arena := buildSingleFast arena sym } }

theorem growPlanned_eq (st : Hd) (lens : ByteArray) (n : USize) (hn : n.toNat ≤ lens.size) :
    growPlanned st lens n hn (planFast lens n hn) = { st with d := { st.d with arena := buildFast st.d.arena lens n hn } } := rfl

theorem growSingle_eq (st : Hd) (sym : UInt64) :
    growSingle st sym = { st with d := { st.d with arena := buildSingleFast st.d.arena sym } } := rfl

/-- Builds a map's table on its own and goes on to the map's values. -/
@[inline] def mapTableDone (st : Hd) (t : ByteArray) : Hd :=
  if h : fitsFast t 0 = true then
    let size := mapSizeFast st
    { st with
      tag := .vals, idx := 0, left := UInt64.ofNat size, fill := zeroBytes size
      mapT := ⟨t, (fitsFast_iff.mp h).1, by
        have := (fitsFast_iff.mp h).2
        rwa [usize_zero']⟩ }
  else { st with status := .bad }

/-- What happens once a prefix code has been read: `single` says that it has one symbol, and otherwise its lengths are in `lens`. -/
def tableDone (st : Hd) (single : Bool) (sym : UInt64) : Hd :=
  let n := st.size.toUSize
  let lens := st.lens
  if hn : n.toNat ≤ lens.size then
    match st.role with
    | .map =>
      mapTableDone st (if single then buildSingleFast ByteArray.empty sym else buildFast ByteArray.empty lens n hn)
    | _ =>
      let size := UInt64.ofNat st.d.arena.size
      let base := UInt64.ofNat (st.d.arena.size / 4)
      if single then
        if size + 1024 ≤ st.d.arenaMax then installTable (growSingle st sym) base
        else { st with status := .memory }
      else
        let p := planFast lens n hn
        if size + p.bytes ≤ st.d.arenaMax then installTable (growPlanned st lens n hn p) base
        else { st with status := .memory }
  else { st with status := .bad }

/-! ### What happens after a table, in the spec's terms -/

private theorem setBaseT_nOf (d : Done) (i j : Cat) (v : USize) : (d.setBaseT i v).nOf j = d.nOf j := by
  cases i <;> cases j <;> rfl

private theorem setBaseT_baseTOf (d : Done) (i : Cat) (v : USize) : (d.setBaseT i v).baseTOf i = v := by cases i <;> rfl

private theorem setBaseT_arena (d : Done) (i : Cat) (v : USize) :
    (d.setBaseT i v).arena = d.arena ∧ (d.setBaseT i v).arenaMax = d.arenaMax := by
  cases i <;> exact ⟨rfl, rfl⟩

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
    (d.setBaseC i v).arena = d.arena ∧ (d.setBaseC i v).arenaMax = d.arenaMax := by
  cases i <;> exact ⟨rfl, rfl⟩

private theorem setBaseC_others (d : Done) (i : Cat) (v : USize) : ∀ j, j ≠ i →
    (d.setBaseC i v).nOf j = d.nOf j ∧ (d.setBaseC i v).countOf j = d.countOf j ∧ (d.setBaseC i v).baseTOf j = d.baseTOf j ∧
      (d.setBaseC i v).baseCOf j = d.baseCOf j := by
  intro j hne
  cases i <;> cases j <;> first | exact absurd rfl hne | exact ⟨rfl, rfl, rfl, rfl⟩

theorem installTable_arena (st : Hd) (base : UInt64) : (installTable st base).d.arena = st.d.arena := by
  unfold installTable
  split
  · cases st.cat <;> rfl
  · cases st.cat <;> rfl
  · rfl

theorem installTable_size (st : Hd) (base : UInt64) (h : HSize st) : HSize (installTable st base) := by
  unfold installTable
  split
  · cases st.cat <;> exact ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩
  · cases st.cat <;> exact ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩
  · exact ⟨by show (u32Set st.fill st.idx base).size ≤ _; rw [size_u32Set]; exact h.fill,
      h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩

/-- An owner always has a table to come. -/
theorem capO_ne (o : Owner) : capO o ≠ 0 := by
  cases o <;> simp only [capO] <;> omega

section
variable {α : Type} (K : HK α)

/-- Any code but a context map's is hooked. -/
theorem owner_w {o : Owner} (g : Gh) (c : PrefixCode) (bs : List Bool) (hm : ∀ a b e, o ≠ .map a b e) : ∃ x, ownerK K g o c bs = K.w c x := by
  cases o with
  | map a b e => exact absurd rfl (hm a b e)
  | type i n => exact ⟨_, rfl⟩
  | count i n tc => exact ⟨_, rfl⟩
  | codes k done left => exact ⟨_, rfl⟩

/-- A table in the arena, for anything but a context map: the state moves to what the code was for. -/
theorem install_ok {st : Hd} {g : Gh} {o : Owner} {size : Nat} {c : PrefixCode} {A1 : ByteArray} {base : UInt64}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hu : Upto st.d g (ownerStage o)) (hs : SizeOk st size) (ho : OwnerRel st g size o)
    (hk : Keep st.d.arena A1) (h4 : A1.size % 4 = 0) (hle : A1.size ≤ st.d.arenaMax.toNat) (htab : TableOk A1 base.toNat c)
    (hb : base.toNat = st.d.arena.size / 4) (hC : Complete c) (hsy : c.Symbols size) (hm : ∀ a b e, o ≠ .map a b e) :
    ∃ g' p', HRel (installTable { st with d := { st.d with arena := A1 } } base) g' p' ∧ (∀ bs, ownerK K g o c bs = K.w c (hrest K g' p' bs)) ∧
      LexLt (rankH p').1 (rankO o) ∧ capH p' + 1 ≤ capO o ∧ (g', p') = (g, ownerPlace g o c) := by
  have hup := hu.frame hk h4 hle
  have hsmall : st.d.arena.size < 2 ^ 32 := by
    have := hu.le
    have := hu.max
    omega
  have hbU : base.toUSize.toNat = base.toNat := word_toUSize (by omega)
  cases o with
  | map a b e => exact absurd rfl (hm a b e)
  | type i n =>
    obtain ⟨hrole, hi, hn, h2, h256, hsz⟩ := ho
    subst hi
    subst hsz
    unfold installTable
    dsimp only
    rw [hrole]
    dsimp only
    refine ⟨g, .code (.count st.cat n c) blockCountAlphabetSize, ⟨hw, ?_, rfl, ⟨rfl, by decide, by decide⟩, rfl, rfl, ?_, h2, h256, rfl, ?_, hC, hsy⟩, (fun bs => rfl),
      by simp only [rankH, rankO, LexLt]; omega, by simp only [capH, capO]; omega, rfl⟩
    · have ha := setBaseT_arena { st.d with arena := A1 } st.cat base.toUSize
      exact Upto.setSame hup ha.1 ha.2 (setBaseT_others _ _ _)
    · show (({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).nOf st.cat).toNat = n
      rw [setBaseT_nOf]
      cases hc : st.cat <;> rw [hc] at hn <;> exact hn
    · show TableOk ({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).arena
        (({ st.d with arena := A1 }.setBaseT st.cat base.toUSize).baseTOf st.cat).toNat c
      rw [setBaseT_baseTOf, (setBaseT_arena _ _ _).1, hbU]
      exact htab
  | count i n tc =>
    obtain ⟨hrole, hi, hn, h2, h256, hsz, hT, hTc, hTs⟩ := ho
    subst hi
    subst hsz
    unfold installTable
    dsimp only
    rw [hrole]
    dsimp only
    have hT' : TableOk A1 (st.d.baseTOf st.cat).toNat tc := hT.frame hk.four hk.le hk.frame
    refine ⟨g, .first st.cat n tc c, ⟨hw, ?_, rfl, rfl, ?_, h2, h256, ?_, hTc, hTs, ?_, hC, hsy⟩, (fun bs => rfl),
      by simp only [rankH, rankO, LexLt]; omega, by simp only [capH, capO]; omega, rfl⟩
    · have ha := setBaseC_arena { st.d with arena := A1 } st.cat base.toUSize
      exact Upto.setSame hup ha.1 ha.2 (setBaseC_others _ _ _)
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
    unfold installTable
    dsimp only
    rw [hrole]
    dsimp only
    have hbase : base.toNat < 2 ^ 32 := by omega
    have hidx16 : st.idx.toNat < 2 ^ 16 := by omega
    have hidx1 : (st.idx + 1).toNat = done.length + 1 := by
      rw [UInt64.toNat_add, hidx, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨g, .codes st.ck (done ++ [c]) left, ⟨hw, hup, rfl, rfl, by simpa using hidx1, hleft, ?_, h256, ?_⟩, (fun bs => rfl),
      Or.inr ⟨rfl, show 2 * left < 2 * left + 1 by omega⟩, by simp only [capH, capO]; omega, rfl⟩
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

/-- What `tableDone` leaves. -/
structure TableDone (g : Gh) (o : Owner) (c : PrefixCode) (st r : Hd) : Prop where
  bits : r.word = st.word ∧ r.count = st.count ∧ r.pos = st.pos
  next : r.status = .next → ∃ g' p' oc, HRel r g' p' ∧ (∀ bs, ownerK K g o c bs = Wr K oc (hrest K g' p' bs)) ∧ LexLt (rankH p').1 (rankO o) ∧
    (∀ q, capH q = capO o → HMove st r q p' oc) ∧ (g', p') = (g, ownerPlace g o c)
  other : r.status ≠ .next → r.status = .memory ∧ r.d.arenaMax = st.d.arenaMax ∧ st.d.arenaMax.toNat < st.d.arena.size + tableBytes c ∧
    tableBytes c ≤ 132096 ∧ capO o ≠ 0 ∧ ∀ bs, ∃ x, ownerK K g o c bs = K.w c x

/-- What `tableDone` does in the spec's terms. -/
theorem tableDone_ok {st : Hd} {g : Gh} {o : Owner} {size : Nat} {c : PrefixCode} {single : Bool} {sym : UInt64}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hu : Upto st.d g (ownerStage o)) (hs : SizeOk st size) (ho : OwnerRel st g size o)
    (hst : st.status = .next) (hsg : single = true → c = .single sym.toNat) (hcn : single = false → c = .canonical (lensOf st.lens size))
    (hlens : st.lens.size = size) (hC : Complete c) (hsy : c.Symbols size) : TableDone K g o c st (tableDone st single sym) := by
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hs : SizeOk st size := ⟨hs1, hs2, hs3⟩
  have hun : st.size.toUSize.toNat = size := by rw [word_toUSize (by omega), hs1]
  have hnle : st.size.toUSize.toNat ≤ st.lens.size := by omega
  have hsmall : st.d.arena.size + 132096 < 2 ^ 32 := by
    have := hu.le
    have := hu.max
    omega
  unfold tableDone
  dsimp only
  rw [dite_eq_left hnle]
  have hsymLt : single = true → sym.toNat < 65536 := by
    intro h
    have := hsg h
    subst this
    have : sym.toNat < size := hsy
    omega
  by_cases hmap : st.role = .map
  · rw [hmap]
    dsimp only
    cases o with
    | type i n => exact absurd (hmap.symm.trans ho.1) (by decide)
    | count i n tc => exact absurd (hmap.symm.trans ho.1) (by decide)
    | codes k done left => exact absurd (hmap.symm.trans ho.1) (by decide)
    | map isL ntrees rlemax =>
      obtain ⟨_, hi, hn, hr, h2, h256, h16, hsz⟩ := ho
      have hempty : (ByteArray.empty).size = 0 := rfl
      have hbuilt : ∃ t, (if single then buildSingleFast ByteArray.empty sym else buildFast ByteArray.empty st.lens st.size.toUSize hnle) = t ∧
          Built ByteArray.empty t c ∧ t.size ≤ 132096 := by
        cases hb : single with
        | true =>
          simp only [↓reduceIte]
          have := hsg hb
          obtain ⟨h1, h2⟩ := built_single (t := ByteArray.empty) (hsymLt hb) (by decide) (by decide)
          refine ⟨_, rfl, ?_, ?_⟩
          · rw [this]
            exact h1
          · rw [h2]
            decide
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          have hc := hcn hb
          rw [← hun] at hc
          have hC' : Complete (.canonical (lensOf st.lens st.size.toUSize.toNat)) := by
            rw [← hc]
            exact hC
          obtain ⟨h1, h2⟩ := built_canonical (t := ByteArray.empty) (hn := hnle) (by omega) hC' (by decide) (by decide)
          refine ⟨_, rfl, ?_, ?_⟩
          · rw [hc]
            exact h1
          · rw [h2, hempty]
            have := (planFast_bytes (hn := hnle) (by omega) hC').2
            omega
      obtain ⟨t, ht, hB, hsize⟩ := hbuilt
      rw [ht]
      have hfit : fitsFast t 0 = true := fitsFast_iff.mpr ⟨by omega, hB.ok.toTableFits⟩
      unfold mapTableDone
      rw [dite_eq_left hfit]
      obtain ⟨hmf, hml⟩ := mapSizeFast_eq (g := g) hi hu
      dsimp only
      have hleft : (UInt64.ofNat (mapSizeFast st)).toNat = mapSize g isL := by
        rw [hmf]
        exact u64_lit (by omega)
      have hzs : (zeroBytes (mapSizeFast st)).size = mapSize g isL := by
        rw [hmf]
        exact zeroBytes_size (by omega)
      refine ⟨⟨rfl, rfl, rfl⟩, fun _ => ⟨g, .vals isL ntrees rlemax c [] (mapSize g isL), none, ⟨hw, hu, rfl, hi, hn, hr, h2, h256, h16, ?_, hC, ?_,
        rfl, hleft, by show 0 + _ = _; omega, hzs, by simp, by simp, fun i _ => ?_⟩, (fun bs => rfl), by simp only [rankH, rankO, LexLt]; omega,
        fun q hq => ⟨rfl, rfl, fun h => ⟨by rw [hzs]; exact hml, h.lens, h.clLens, h.clt, hsize, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩,
          by rw [hq]; simp only [capH, capO, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩, rfl⟩, fun h => absurd hst h⟩
      · rw [usize_zero']
        exact hB.ok
      · rw [← hsz]
        exact hsy
      · show (zeroBytes (mapSizeFast st)).data[i]?.getD 0 = 0
        rw [hmf]
        exact zeroBytes_get (by omega)
  · have hrole : ∀ a b e, o ≠ .map a b e := by
      intro a b e he
      subst he
      exact hmap ho.1
    have hstart : (match st.role with
        | .map => mapTableDone st (if single then buildSingleFast ByteArray.empty sym else buildFast ByteArray.empty st.lens st.size.toUSize hnle)
        | _ =>
          if single = true then
            if UInt64.ofNat st.d.arena.size + 1024 ≤ st.d.arenaMax then installTable (growSingle st sym) (UInt64.ofNat (st.d.arena.size / 4))
            else { st with status := .memory }
          else
            if UInt64.ofNat st.d.arena.size + (planFast st.lens st.size.toUSize hnle).bytes ≤ st.d.arenaMax then
              installTable (growPlanned st st.lens st.size.toUSize hnle (planFast st.lens st.size.toUSize hnle)) (UInt64.ofNat (st.d.arena.size / 4))
            else { st with status := .memory }) =
        (if single = true then
            if UInt64.ofNat st.d.arena.size + 1024 ≤ st.d.arenaMax then installTable (growSingle st sym) (UInt64.ofNat (st.d.arena.size / 4))
            else { st with status := .memory }
          else
            if UInt64.ofNat st.d.arena.size + (planFast st.lens st.size.toUSize hnle).bytes ≤ st.d.arenaMax then
              installTable (growPlanned st st.lens st.size.toUSize hnle (planFast st.lens st.size.toUSize hnle)) (UInt64.ofNat (st.d.arena.size / 4))
            else { st with status := .memory }) := by
      cases hr : st.role with
      | map => exact absurd hr hmap
      | type => rfl
      | count => rfl
      | codes => rfl
    rw [hstart]
    have hbase : (UInt64.ofNat (st.d.arena.size / 4)).toNat = st.d.arena.size / 4 := u64_lit (by omega)
    have hsizeN : (UInt64.ofNat st.d.arena.size).toNat = st.d.arena.size := u64_lit (by omega)
    have hfinish : ∀ {A1 : ByteArray}, Built st.d.arena A1 c → A1.size ≤ st.d.arenaMax.toNat → A1.size = st.d.arena.size + tableBytes c → tableBytes c ≤ 132096 →
        TableDone K g o c st (installTable { st with d := { st.d with arena := A1 } } (UInt64.ofNat (st.d.arena.size / 4))) := by
      intro A1 hB hle hgrow hone
      have hok : TableOk A1 (UInt64.ofNat (st.d.arena.size / 4)).toNat c := by
        rw [hbase]
        exact hB.ok
      obtain ⟨g', p', h1, h2, h3, h4, h5⟩ := install_ok K hw hu hs ho hB.keep hB.four hle hok hbase hC hsy hrole
      obtain ⟨b1, b2, b3, b4, b5⟩ := installTable_spec { st with d := { st.d with arena := A1 } } (UInt64.ofNat (st.d.arena.size / 4))
      refine ⟨⟨b1, b2, b3⟩, fun _ => ⟨g', p', some c, h1, h2, h3, fun q hq => ⟨b5, ?_, ?_, ?_, hone⟩, h5⟩, fun h => absurd (b4.trans hst) h⟩
      · rw [installTable_arena]
        exact hgrow
      · intro h
        exact installTable_size _ _ ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase⟩
      · rw [hq]
        simpa using h4
    have hother : st.d.arenaMax.toNat < st.d.arena.size + tableBytes c → tableBytes c ≤ 132096 → TableDone K g o c st { st with status := .memory } :=
      fun hlt hone => ⟨⟨rfl, rfl, rfl⟩, fun h => HStatus.noConfusion h, fun _ => ⟨rfl, rfl, hlt, hone, capO_ne o, fun bs => owner_w K g c bs hrole⟩⟩
    cases hb : single with
    | true =>
      simp only [↓reduceIte]
      obtain ⟨h1, h2⟩ := built_single (t := st.d.arena) (hsymLt hb) hu.four (by omega)
      have := hsg hb
      subst this
      have hlt : (UInt64.ofNat st.d.arena.size + 1024).toNat = st.d.arena.size + 1024 := by
        rw [UInt64.toNat_add, hsizeN, show (1024 : UInt64).toNat = 1024 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      by_cases hc : UInt64.ofNat st.d.arena.size + 1024 ≤ st.d.arenaMax
      · rw [ite_eq_left hc]
        have hle := UInt64.le_iff_toNat_le.mp hc
        rw [hlt] at hle
        rw [growSingle_eq]
        exact hfinish h1 (by omega) h2 (show 1024 ≤ 132096 by decide)
      · rw [ite_eq_right hc]
        exact hother (Nat.lt_of_not_le fun e => hc (UInt64.le_iff_toNat_le.mpr (by rw [hlt]; exact e))) (show 1024 ≤ 132096 by decide)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hc := hcn hb
      rw [← hun] at hc
      have hC' : Complete (.canonical (lensOf st.lens st.size.toUSize.toNat)) := by
        rw [← hc]
        exact hC
      obtain ⟨h1, h2⟩ := built_canonical (t := st.d.arena) (hn := hnle) (by omega) hC' hu.four (by omega)
      obtain ⟨p1, p2⟩ := planFast_bytes (hn := hnle) (by omega) hC'
      have hbytes : tableBytes c = 4 * (256 + offSum (depths (lensOf st.lens st.size.toUSize.toNat)) 256) := by
        rw [hc]
        rfl
      have hlt : (UInt64.ofNat st.d.arena.size + (planFast st.lens st.size.toUSize hnle).bytes).toNat =
          st.d.arena.size + 4 * (256 + offSum (depths (lensOf st.lens st.size.toUSize.toNat)) 256) := by
        rw [UInt64.toNat_add, hsizeN, p1]
        exact Nat.mod_eq_of_lt (by omega)
      by_cases hc2 : UInt64.ofNat st.d.arena.size + (planFast st.lens st.size.toUSize hnle).bytes ≤ st.d.arenaMax
      · rw [ite_eq_left hc2]
        have hle := UInt64.le_iff_toNat_le.mp hc2
        rw [hlt] at hle
        have hB : Built st.d.arena (buildFast st.d.arena st.lens st.size.toUSize hnle) c := by
          rw [hc]
          exact h1
        rw [growPlanned_eq]
        exact hfinish hB (by rw [h2]; exact hle) (by rw [h2, hbytes]) (by rw [hbytes]; omega)
      · rw [ite_eq_right hc2]
        exact hother (by
          rw [hbytes]
          exact Nat.lt_of_not_le fun e => hc2 (UInt64.le_iff_toNat_le.mpr (by rw [hlt]; exact e))) (by rw [hbytes]; omega)

end

end Brotli.Decoder
