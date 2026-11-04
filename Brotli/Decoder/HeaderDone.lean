import Brotli.Decoder.HeaderMap

/-!
# The header machine, and the header it leaves

`stepH` is one step of the header machine, proved by `stepH_ok`. When it is ready, `mkHdr` makes the command loop's `Hdr`
with the checks that loop's proofs rest on, made once here and proved never to fail on a header that was read.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The machine -/

/-- A step, once the buffer is refilled. -/
def stepAtH (st : Hd) (pos : USize) : Hd :=
  match st.tag with
  | .cat => stepHCat st pos
  | .code => stepHCode st pos
  | .clens => stepHClens st pos
  | .syms => stepHSyms st pos
  | .first => stepHFirst st pos
  | .np => stepHNp st pos
  | .modes => stepHModes st pos
  | .trees => stepHTrees st pos
  | .rlemax => stepHRlemax st pos
  | .vals => stepHVals st pos
  | .imtf => stepHImtf st pos
  | .codes => stepHCodes st pos
  | .ready => markH st pos .ready

/-- One step of the header machine. -/
def stepH (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Hd) (pos : USize) : Hd :=
  if hp : pos ≤ stop then
    let r := refill st.word st.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    stepAtH { st with word := rw, count := rc } rp
  else markH st pos .bad

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepAtH_ok {g : Gh} {p : HPhase} {st : Hd} {pos : USize} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) : HStepOk K a stop g p st pos (stepAtH st pos) := by
  unfold stepAtH
  cases p with
  | cat i =>
    rw [hrel.2.2.1]
    exact stepHCat_ok hrel hp hfull
  | code o size =>
    rw [hrel.2.2.1]
    exact stepHCode_ok hrel hp hfull
  | clens o size order acc sum =>
    rw [hrel.2.2.1]
    exact stepHClens_ok hrel hp hfull
  | syms o size clc ls =>
    rw [hrel.2.2.1]
    exact stepHSyms_ok hrel hp hfull
  | first i n tc cc =>
    rw [hrel.2.2.1]
    exact stepHFirst_ok hrel hp hfull
  | np =>
    rw [hrel.2.2]
    exact stepHNp_ok hrel hp hfull
  | modes done left =>
    rw [hrel.2.2.1]
    exact stepHModes_ok hrel hp hfull
  | trees isL =>
    rw [hrel.2.2.1]
    exact stepHTrees_ok hrel hp hfull
  | rlemax isL ntrees =>
    rw [hrel.2.2.1]
    exact stepHRlemax_ok hrel hp hfull
  | vals isL ntrees rlemax code done left =>
    rw [hrel.2.2.1]
    exact stepHVals_ok hrel hp hfull
  | imtf isL ntrees vals =>
    rw [hrel.2.2.1]
    exact stepHImtf_ok hrel hp hfull
  | codes k done left =>
    rw [hrel.2.2.1]
    exact stepHCodes_ok hrel hp

/-- What a step of the header machine does in the spec's terms, for every future. -/
theorem stepH_ok {g : Gh} {p : HPhase} {st : Hd} {pos : USize} {hs : stop.toNat ≤ a.size} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat) :
    HStepOk K a stop g p st pos (stepH a stop hs st pos) := by
  unfold stepH
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hp)]
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  dsimp only
  refine (stepAtH_ok (hrel.withBits h1) h3 h5).refilled (fun F => ?_) h2 h3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
    (refill st.word st.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F)
  rw [← List.append_assoc, ← List.append_assoc, h4]

end

/-! ### Checks made once -/

/-- Checks that `k` bytes from `i` are below `n`. -/
def bytesBelow (t : ByteArray) (n i k : UInt64) : Bool :=
  if _hk : k = 0 then true
  else if (getU t i.toUSize).toUInt64 < n then bytesBelow t n (i + 1) (k - 1) else false
termination_by k.toNat
decreasing_by
  have hne : k.toNat ≠ 0 := fun e => _hk (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (k - 1).toNat = k.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem bytesBelow_iff (t : ByteArray) (n : UInt64) : ∀ (N : Nat) (i k : UInt64), k.toNat = N → i.toNat + N < 2 ^ 32 →
    (bytesBelow t n i k = true ↔ ∀ j, i.toNat ≤ j → j < i.toNat + N → (t.data[j]?.getD 0).toNat < n.toNat) := by
  intro N
  induction N with
  | zero =>
    intro i k hk _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [bytesBelow, dite_eq_left hz]
    exact ⟨fun _ j h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro i k hk h32
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    have hv : (getU t i.toUSize).toUInt64.toNat = (t.data[i.toNat]?.getD 0).toNat := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hus]
    rw [bytesBelow, dite_eq_right hz]
    by_cases hc : (getU t i.toUSize).toUInt64 < n
    · have hc' := UInt64.lt_iff_toNat_lt.mp hc
      rw [hv] at hc'
      rw [ite_eq_left hc, ih (i + 1) (k - 1) hk1 (by rw [hi1]; omega), hi1]
      constructor
      · intro h j h1 h2
        by_cases he : j = i.toNat
        · rw [he]
          exact hc'
        · exact h j (by omega) (by omega)
      · intro h j h1 h2
        exact h j (by omega) (by omega)
    · rw [ite_eq_right hc]
      constructor
      · exact fun h => Bool.noConfusion h
      · intro h
        have := h i.toNat (Nat.le_refl _) (by omega)
        rw [← hv] at this
        exact absurd (UInt64.lt_iff_toNat_lt.mpr this) hc

/-- A 32-bit value in an array. -/
@[inline] def u32Fast (t : ByteArray) (i : UInt64) : UInt64 :=
  (getU t (i * 4).toUSize).toUInt64 + 256 * (getU t (i * 4 + 1).toUSize).toUInt64 + 65536 * (getU t (i * 4 + 2).toUSize).toUInt64 +
    16777216 * (getU t (i * 4 + 3).toUSize).toUInt64

theorem u32Fast_toNat (t : ByteArray) {i : UInt64} (hi : i.toNat < 2 ^ 16) : (u32Fast t i).toNat = u32At t i.toNat := by
  have hp : (i * 4).toNat = 4 * i.toNat := by
    rw [UInt64.toNat_mul, show (4 : UInt64).toNat = 4 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  have hj : ∀ j : UInt64, j.toNat ≤ 3 → (i * 4 + j).toNat = 4 * i.toNat + j.toNat := by
    intro j hj
    rw [UInt64.toNat_add, hp]
    exact Nat.mod_eq_of_lt (by omega)
  have g0 : (getU t (i * 4).toUSize).toUInt64.toNat = (t.data[4 * i.toNat]?.getD 0).toNat := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by rw [hp]; omega), hp]
  have g1 : (getU t (i * 4 + 1).toUSize).toUInt64.toNat = (t.data[4 * i.toNat + 1]?.getD 0).toNat := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by rw [hj 1 (by decide)]; show 4 * i.toNat + 1 < _; omega), hj 1 (by decide)]
    rfl
  have g2 : (getU t (i * 4 + 2).toUSize).toUInt64.toNat = (t.data[4 * i.toNat + 2]?.getD 0).toNat := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by rw [hj 2 (by decide)]; show 4 * i.toNat + 2 < _; omega), hj 2 (by decide)]
    rfl
  have g3 : (getU t (i * 4 + 3).toUSize).toUInt64.toNat = (t.data[4 * i.toNat + 3]?.getD 0).toNat := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by rw [hj 3 (by decide)]; show 4 * i.toNat + 3 < _; omega), hj 3 (by decide)]
    rfl
  unfold u32Fast u32At
  generalize (getU t (i * 4).toUSize).toUInt64 = a0 at g0
  generalize (getU t (i * 4 + 1).toUSize).toUInt64 = a1 at g1
  generalize (getU t (i * 4 + 2).toUSize).toUInt64 = a2 at g2
  generalize (getU t (i * 4 + 3).toUSize).toUInt64 = a3 at g3
  have b0 := (t.data[4 * i.toNat]?.getD 0).toNat_lt
  have b1 := (t.data[4 * i.toNat + 1]?.getD 0).toNat_lt
  have b2 := (t.data[4 * i.toNat + 2]?.getD 0).toNat_lt
  have b3 := (t.data[4 * i.toNat + 3]?.getD 0).toNat_lt
  rw [← g0, ← g1, ← g2, ← g3] at *
  have m1 : (256 * a1).toNat = 256 * a1.toNat := by
    rw [UInt64.toNat_mul, show (256 : UInt64).toNat = 256 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have m2 : (65536 * a2).toNat = 65536 * a2.toNat := by
    rw [UInt64.toNat_mul, show (65536 : UInt64).toNat = 65536 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have m3 : (16777216 * a3).toNat = 16777216 * a3.toNat := by
    rw [UInt64.toNat_mul, show (16777216 : UInt64).toNat = 16777216 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have s1 : (a0 + 256 * a1).toNat = a0.toNat + 256 * a1.toNat := by
    rw [UInt64.toNat_add, m1]
    exact Nat.mod_eq_of_lt (by omega)
  have s2 : (a0 + 256 * a1 + 65536 * a2).toNat = a0.toNat + 256 * a1.toNat + 65536 * a2.toNat := by
    rw [UInt64.toNat_add, s1, m2]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_add, s2, m3]
  exact Nat.mod_eq_of_lt (by omega)

/-- Checks the tables of `k` trees from `i`. -/
def treesFit (arena bases : ByteArray) (i k : UInt64) : Bool :=
  if _hk : k = 0 then true
  else if fitsFast arena (u32Fast bases i) then treesFit arena bases (i + 1) (k - 1) else false
termination_by k.toNat
decreasing_by
  have hne : k.toNat ≠ 0 := fun e => _hk (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (k - 1).toNat = k.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem treesFit_iff (arena bases : ByteArray) (h32 : arena.size < 2 ^ 32) : ∀ (N : Nat) (i k : UInt64), k.toNat = N → i.toNat + N < 2 ^ 16 →
    (treesFit arena bases i k = true ↔ ∀ j, i.toNat ≤ j → j < i.toNat + N → TableFits arena (u32At bases j)) := by
  intro N
  induction N with
  | zero =>
    intro i k hk _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [treesFit, dite_eq_left hz]
    exact ⟨fun _ j h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro i k hk h16
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hv := u32Fast_toNat bases (i := i) (by omega)
    have hone : fitsFast arena (u32Fast bases i) = true ↔ TableFits arena (u32At bases i.toNat) := by
      rw [fitsFast_iff, hv]
      exact ⟨fun h => h.2, fun h => ⟨h32, h⟩⟩
    rw [treesFit, dite_eq_right hz]
    by_cases hc : fitsFast arena (u32Fast bases i) = true
    · rw [ite_eq_left hc, ih (i + 1) (k - 1) hk1 (by rw [hi1]; omega), hi1]
      constructor
      · intro h j h1 h2
        by_cases he : j = i.toNat
        · rw [he]
          exact hone.mp hc
        · exact h j (by omega) (by omega)
      · intro h j h1 h2
        exact h j (by omega) (by omega)
    · rw [ite_eq_right hc]
      constructor
      · exact fun h => Bool.noConfusion h
      · intro h
        exact absurd (hone.mpr (h i.toNat (Nat.le_refl _) (by omega))) hc

/-! ### The command loop's header -/

/-- The sizes and small values a command loop's header needs. -/
def HdrSizes (d : Done) : Prop :=
  d.arena.size < 4294967296 ∧ d.litBase.size < 4294967296 ∧ d.lMap.size < 4294967296 ∧ d.litBase.size = 4 * d.treesL.toNat ∧
    d.npostfix.toNat ≤ 3 ∧ d.ndirect.toNat ≤ 120 ∧ d.lMap.size = 64 * d.nL.toNat ∧ d.modes.size = d.nL.toNat ∧
    d.icBase.size = 4 * d.nI.toNat ∧ d.icBase.size < 4294967296 ∧ d.dBase.size = 4 * d.treesD.toNat ∧ d.dBase.size < 4294967296 ∧
    d.dMap.size = 4 * d.nD.toNat ∧ d.dMap.size < 4294967296 ∧ d.treesL.toNat ≤ 256 ∧ d.treesD.toNat ≤ 256 ∧ d.nI.toNat ≤ 256

instance (d : Done) : Decidable (HdrSizes d) := by
  unfold HdrSizes
  exact inferInstance

/-- A category's switch tables, checked if it has two block types or more. -/
@[inline] def catFit (arena : ByteArray) (n : UInt64) (bt bc : USize) : Bool :=
  if n < 2 then true else tableCheck arena bt && tableCheck arena bc

/-- The checks a command loop's header needs. -/
def hdrChecks (d : Done) : Bool :=
  bytesBelow d.lMap d.treesL 0 (UInt64.ofNat d.lMap.size) && bytesBelow d.modes 4 0 (UInt64.ofNat d.modes.size) &&
    bytesBelow d.dMap d.treesD 0 (UInt64.ofNat d.dMap.size) && treesFit d.arena d.litBase 0 d.treesL && treesFit d.arena d.icBase 0 d.nI &&
    treesFit d.arena d.dBase 0 d.treesD && catFit d.arena d.nL d.baseTL d.baseCL && catFit d.arena d.nI d.baseTI d.baseCI &&
    catFit d.arena d.nD d.baseTD d.baseCD

/-- What the checks give, as `Hdr` states it. -/
structure HdrProps (d : Done) : Prop where
  treeLt : ∀ p : USize, ∀ h : p.toNat < d.lMap.size, (d.lMap.uget p h).toNat < d.treesL.toNat
  fits : ∀ tree, tree < d.treesL.toNat → TableFits d.arena (u32At d.litBase tree)
  modesLt : ∀ p : USize, ∀ h : p.toNat < d.modes.size, (d.modes.uget p h).toNat < 4
  icFits : ∀ t, t < d.nI.toNat → TableFits d.arena (u32At d.icBase t)
  dMapLt : ∀ p : USize, ∀ h : p.toNat < d.dMap.size, (d.dMap.uget p h).toNat < d.treesD.toNat
  dFits : ∀ tree, tree < d.treesD.toNat → TableFits d.arena (u32At d.dBase tree)
  swL : 2 ≤ d.nL.toNat → TableFits d.arena d.baseTL.toNat ∧ TableFits d.arena d.baseCL.toNat
  swI : 2 ≤ d.nI.toNat → TableFits d.arena d.baseTI.toNat ∧ TableFits d.arena d.baseCI.toNat
  swD : 2 ≤ d.nD.toNat → TableFits d.arena d.baseTD.toNat ∧ TableFits d.arena d.baseCD.toNat

private theorem bytes_all {t : ByteArray} {n : UInt64} (hs : t.size < 2 ^ 32) :
    bytesBelow t n 0 (UInt64.ofNat t.size) = true ↔ ∀ p : USize, ∀ h : p.toNat < t.size, (t.uget p h).toNat < n.toNat := by
  have hz : (0 : UInt64).toNat = 0 := rfl
  have hl : (UInt64.ofNat t.size).toNat = t.size := u64_lit (by omega)
  rw [bytesBelow_iff t n _ 0 _ hl (by rw [hz]; omega), hz]
  constructor
  · intro h p hp
    rw [uget_toNat]
    exact h _ (Nat.zero_le _) (by omega)
  · intro h j _ hj
    have hp : (USize.ofNat j).toNat = j := by
      rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
      have := USize.le_size
      exact Nat.mod_eq_of_lt (by omega)
    have := h (USize.ofNat j) (by rw [hp]; omega)
    rwa [uget_toNat, hp] at this

private theorem cat_fit {arena : ByteArray} {n : UInt64} {bt bc : USize} :
    catFit arena n bt bc = true ↔ (arena.size < 2 ^ 32 ∨ n.toNat < 2) ∧ (2 ≤ n.toNat → TableFits arena bt.toNat ∧ TableFits arena bc.toNat) := by
  unfold catFit
  by_cases h : n < 2
  · have h' : n.toNat < 2 := UInt64.lt_iff_toNat_lt.mp h
    rw [ite_eq_left h]
    exact ⟨fun _ => ⟨Or.inr h', fun e => absurd e (by omega)⟩, fun _ => rfl⟩
  · have h' : ¬ n.toNat < 2 := fun e => h (UInt64.lt_iff_toNat_lt.mpr e)
    rw [ite_eq_right h, Bool.and_eq_true, tableCheck_iff, tableCheck_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨_, h3⟩⟩
      exact ⟨Or.inl h1, fun _ => ⟨h2, h3⟩⟩
    · rintro ⟨h1, h2⟩
      have h1' : arena.size < 2 ^ 32 := h1.resolve_right h'
      obtain ⟨h3, h4⟩ := h2 (by omega)
      exact ⟨⟨h1', h3⟩, ⟨h1', h4⟩⟩

/-- The checks say exactly what `Hdr` states. -/
theorem hdrChecks_iff {d : Done} (hs : HdrSizes d) : hdrChecks d = true ↔ HdrProps d := by
  obtain ⟨h1, h2, h3, h4, _, _, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hs
  have ha32 : d.arena.size < 2 ^ 32 := h1
  have hz : (0 : UInt64).toNat = 0 := rfl
  have tl := treesFit_iff d.arena d.litBase ha32 _ 0 d.treesL rfl (by rw [hz]; omega)
  have ti := treesFit_iff d.arena d.icBase ha32 _ 0 d.nI rfl (by rw [hz]; omega)
  have td := treesFit_iff d.arena d.dBase ha32 _ 0 d.treesD rfl (by rw [hz]; omega)
  rw [hz] at tl ti td
  have bl := bytes_all (t := d.lMap) (n := d.treesL) h3
  have bm := bytes_all (t := d.modes) (n := 4) (by rw [h8]; have := h7; omega)
  have bd := bytes_all (t := d.dMap) (n := d.treesD) h14
  unfold hdrChecks
  simp only [Bool.and_eq_true]
  rw [bl, bm, bd, tl, ti, td, cat_fit, cat_fit, cat_fit]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩
    exact ⟨a1, fun t ht => a4 t (Nat.zero_le _) (by omega), a2, fun t ht => a5 t (Nat.zero_le _) (by omega), a3,
      fun t ht => a6 t (Nat.zero_le _) (by omega), a7.2, a8.2, a9.2⟩
  · intro h
    exact ⟨⟨⟨⟨⟨⟨⟨⟨h.treeLt, h.modesLt⟩, h.dMapLt⟩, fun t _ ht => h.fits t (by omega)⟩, fun t _ ht => h.icFits t (by omega)⟩,
      fun t _ ht => h.dFits t (by omega)⟩, ⟨Or.inl ha32, h.swL⟩⟩, ⟨Or.inl ha32, h.swI⟩⟩, ⟨Or.inl ha32, h.swD⟩⟩

/-- Makes the command loop's header, making its checks once. -/
def mkHdr (d : Done) : Option Hdr :=
  if hs : HdrSizes d then
    if hc : hdrChecks d = true then
      some {
        arena := d.arena, arenaCap := d.arenaCap, litBase := d.litBase, lMap := d.lMap, icBase := d.icBase, dBase := d.dBase
        dMap := d.dMap, modes := d.modes
        nL := d.nL, nI := d.nI, nD := d.nD, treesL := d.treesL, treesD := d.treesD
        baseTL := d.baseTL, baseCL := d.baseCL, baseTI := d.baseTI, baseCI := d.baseCI, baseTD := d.baseTD, baseCD := d.baseCD
        npostfix := d.npostfix, ndirect := d.ndirect
        npLe := hs.2.2.2.2.1, ndLe := hs.2.2.2.2.2.1
        lit := ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ((hdrChecks_iff hs).mp hc).treeLt, ((hdrChecks_iff hs).mp hc).fits⟩
        lMapSize := hs.2.2.2.2.2.2.1
        modesSize := hs.2.2.2.2.2.2.2.1
        modesLt := ((hdrChecks_iff hs).mp hc).modesLt
        icSize := hs.2.2.2.2.2.2.2.2.1
        ic32 := hs.2.2.2.2.2.2.2.2.2.1
        icFits := ((hdrChecks_iff hs).mp hc).icFits
        dSize := hs.2.2.2.2.2.2.2.2.2.2.1
        d32 := hs.2.2.2.2.2.2.2.2.2.2.2.1
        dMapSize := hs.2.2.2.2.2.2.2.2.2.2.2.2.1
        dMap32 := hs.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        dMapLt := ((hdrChecks_iff hs).mp hc).dMapLt
        dFits := ((hdrChecks_iff hs).mp hc).dFits
        swL := ((hdrChecks_iff hs).mp hc).swL
        swI := ((hdrChecks_iff hs).mp hc).swI
        swD := ((hdrChecks_iff hs).mp hc).swD }
    else none
  else none

/-- A header that was read passes the checks, and the header they make matches the spec's. -/
theorem mkHdr_ok {d : Done} {g : Gh} (hu : Upto d g 10) : ∃ H, mkHdr d = some H ∧ HdrRel H g.m ∧ H.arena = d.arena ∧ H.litBase = d.litBase ∧ H.lMap = d.lMap ∧
    H.icBase = d.icBase ∧ H.dBase = d.dBase ∧ H.dMap = d.dMap ∧ H.modes = d.modes ∧ H.arenaCap = d.arenaCap := by
  have hL := hu.cat .L (by decide)
  have hI := hu.cat .I (by decide)
  have hD := hu.cat .D (by decide)
  have hLn : d.nL.toNat = g.m.literal.n := hL.n
  have hIn : d.nI.toNat = g.m.insertCopy.n := hI.n
  have hDn : d.nD.toNat = g.m.distance.n := hD.n
  have hLw : g.m.literal.n ≤ 256 := hL.wf.2.1
  have hIw : g.m.insertCopy.n ≤ 256 := hI.wf.2.1
  have hDw : g.m.distance.n ≤ 256 := hD.wf.2.1
  obtain ⟨np1, np2, np3, np4⟩ := hu.np (by decide)
  have hm := hu.modes (by decide)
  obtain ⟨tl1, tl2, tl3, ml⟩ := hu.lmap (by decide)
  obtain ⟨td1, td2, td3, md⟩ := hu.dmap (by decide)
  obtain ⟨cl1, cl⟩ := hu.codes .L (by decide)
  obtain ⟨ci1, ci⟩ := hu.codes .I (by decide)
  obtain ⟨cd1, cd⟩ := hu.codes .D (by decide)
  have ha32 : d.arena.size < 4294967296 := by
    have := hu.le
    have := hu.max
    omega
  have clB : d.litBase.size = 4 * g.treesL := cl.basesSize
  have ciB : d.icBase.size = 4 * g.m.insertCopy.n := ci.basesSize
  have cdB : d.dBase.size = 4 * g.treesD := cd.basesSize
  have hmL : d.lMap.size = 64 * d.nL.toNat := by rw [ml.sz, hLn]; rfl
  have hmD : d.dMap.size = 4 * d.nD.toNat := by rw [md.sz, hDn]; rfl
  have hsizes : HdrSizes d := by
    refine ⟨ha32, by rw [clB]; omega, by rw [hmL]; omega, by rw [clB, tl1], by omega, by omega, hmL, ?_, by rw [ciB, hIn], by rw [ciB]; omega,
      by rw [cdB, td1], by rw [cdB]; omega, hmD, by rw [hmD]; omega, by omega, by omega, by omega⟩
    rw [hm.sz, hLn]
  have hprops : HdrProps d := by
    have tablesFrom : ∀ {cs : List PrefixCode} {bases : ByteArray} {total size : Nat}, CodesPart d.arena bases cs total size → cs.length = total →
        ∀ t, t < total → TableFits d.arena (u32At bases t) := by
      intro cs bases total size hp hl t ht
      obtain ⟨c, _, h2, _⟩ := hp.code t (by omega)
      exact h2.toTableFits
    have mapLt : ∀ {b : ByteArray} {l : List Nat} {size n : Nat}, MapOk b l size n → ∀ p : USize, ∀ h : p.toNat < b.size,
        (b.uget p h).toNat < n := by
      intro b l size n hm p h
      rw [uget_toNat]
      have hps : p.toNat < size := by rw [← hm.sz]; exact h
      exact hm.lt _ (List.mem_of_getElem? (hm.at_ _ hps))
    have catOf : ∀ {i : Cat} {c : BlockCategory}, CatOk d i c → 2 ≤ (d.nOf i).toNat →
        TableFits d.arena (d.baseTOf i).toNat ∧ TableFits d.arena (d.baseCOf i).toNat := by
      intro i c h hn
      have h2 : 2 ≤ c.n := by rw [← h.n]; exact hn
      exact ⟨(h.rel.type h2).1.toTableFits, (h.rel.count h2).1.toTableFits⟩
    exact ⟨by rw [tl1]; exact mapLt ml, by rw [tl1]; exact tablesFrom cl cl1.symm, mapLt hm, by rw [hIn]; exact tablesFrom ci ci1.symm,
      by rw [td1]; exact mapLt md, by rw [td1]; exact tablesFrom cd cd1.symm, catOf hL, catOf hI, catOf hD⟩
  have hchecks := (hdrChecks_iff hsizes).mpr hprops
  have codesMem : ∀ {cs : List PrefixCode} {bases : ByteArray} {total size : Nat}, CodesPart d.arena bases cs total size →
      ∀ c ∈ cs, c.Symbols size ∧ Complete c := by
    intro cs bases total size hp c hc
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨c1, h1, _, h3, h4⟩ := hp.code i hi
    rw [List.getElem?_eq_getElem hi, e] at h1
    have := Option.some.inj h1
    subst this
    exact ⟨h4, h3⟩
  unfold mkHdr
  rw [dite_eq_left hsizes, dite_eq_left hchecks]
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact {
    ok := {
      literal := hL.wf
      insertCopy := hI.wf
      distance := hD.wf
      literalCount := fun h => (hL.rel.count h).2.2
      insertCopyCount := fun h => (hI.rel.count h).2.2
      distanceCount := fun h => (hD.rel.count h).2.2
      modes_length := hm.length
      literalMap_length := ml.length
      literalMap_lt := fun v hv => by
        have := ml.lt v hv
        rw [← show g.treesL = g.m.literalCodes.length from cl1]
        exact this
      literalCodes := codesMem cl
      insertCopyCodes_length := ci1.symm
      insertCopyCodes := codesMem ci
      distanceMap_length := md.length
      distanceMap_lt := fun v hv => by
        have := md.lt v hv
        rw [← show g.treesD = g.m.distanceCodes.length from cd1]
        exact this
      distanceCodes := codesMem cd
      literalSwitch := ⟨hL.tc, hL.cc⟩
      insertCopySwitch := ⟨hI.tc, hI.cc⟩
      distanceSwitch := ⟨hD.tc, hD.cc⟩ }
    nL := hLn
    nI := hIn
    nD := hDn
    npostfix := np1
    ndirect := np2
    lit := {
      map := fun p h => by
        rw [uget_toNat]
        exact ml.at_ _ (by rw [← ml.sz]; exact h)
      code := fun t ht => by
        obtain ⟨c, h1, h2, h3, h4⟩ := cl.code t (by rw [← cl1]; rw [tl1] at ht; exact ht)
        exact ⟨c, h1, h2, h3, h4⟩ }
    modes := fun p h => by
      rw [uget_toNat]
      exact hm.at_ _ (by rw [← hm.sz]; exact h)
    ic := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := ci.code t (by rw [← ci1]; rw [hIn] at ht; exact ht)
      exact ⟨c, h1, h2, h3, h4⟩
    dMap := fun p h => by
      rw [uget_toNat]
      exact md.at_ _ (by rw [← md.sz]; exact h)
    d := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := cd.code t (by rw [← cd1]; rw [td1] at ht; exact ht)
      exact ⟨c, h1, h2, h3, h4⟩
    catL := hL.rel
    catI := hI.rel
    catD := hD.rel }

end Brotli.Decoder
