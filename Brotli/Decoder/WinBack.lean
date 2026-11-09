module

public import Brotli.Decoder.FastLoop
public import Brotli.Decoder.CopyRing

@[expose] public section

/-!
# The window's context bytes, back from a position

`backB` is the byte `j` back from an unmasked window position `o`, 0 before `j` bytes: a byte written at `o` makes it
the first back from `o + 1`, and the old first the second (`backB_put`), so the copy, word and literal runs keep the
two context bytes the window's two before the position they leave at (`copyRun_back`, `wordRun_back`,
`literalRun_back`). The command loop that carries only the bytes waiting (`kstepY`, `LoopY.lean`) works out the
window's fields from these.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Masked positions -/

theorem umask_mod {x mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) : (x &&& mask).toNat = x.toNat % 2 ^ k := by
  rw [USize.toNat_and, hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem udvd {k : Nat} (hk : k ≤ 24) : 2 ^ k ∣ 2 ^ System.Platform.numBits :=
  Nat.pow_dvd_pow 2 (by rcases System.Platform.numBits_eq with h | h <;> omega)

/-- A sum's masked value depends only on the masked value of a summand. -/
theorem mask_add_l {a b mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ((a &&& mask) + b) &&& mask = (a + b) &&& mask := by
  apply USize.toNat_inj.mp
  simp only [umask_mod hm, USize.toNat_add, Nat.mod_mod_of_dvd _ (udvd hk), Nat.mod_add_mod]

theorem mask_add_r {a b mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    (a + (b &&& mask)) &&& mask = (a + b) &&& mask := by
  rw [USize.add_comm a, mask_add_l hk hm, USize.add_comm]

/-- A difference's masked value depends only on the masked value of what it is taken from. -/
theorem mask_sub_l {a b mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ((a &&& mask) - b) &&& mask = (a - b) &&& mask := by
  apply USize.toNat_inj.mp
  simp only [umask_mod hm, USize.toNat_sub, Nat.mod_mod_of_dvd _ (udvd hk), Nat.add_mod_mod]

/-- Masking forgets what `x - (x &&& mask)` adds, a multiple of the window. -/
theorem mask_add_hi {a x mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    (a + (x - (x &&& mask))) &&& mask = a &&& mask := by
  rw [← mask_add_r hk hm, ← mask_sub_l (a := x) (b := x &&& mask) hk hm, USize.sub_self]
  apply USize.toNat_inj.mp
  simp only [umask_mod hm, USize.toNat_add, Nat.mod_mod_of_dvd _ (udvd hk), USize.toNat_zero, Nat.zero_mod,
    Nat.add_zero]

/-- A masked position is masked. -/
theorem mask_mask {x mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) :
    (x &&& mask) &&& mask = x &&& mask := by
  apply USize.toNat_inj.mp
  rw [umask_mod hm, umask_mod hm, Nat.mod_mod]

/-! ### The context bytes back from a position -/

/-- The window's byte at `i`, masked, with no bound to give. -/
def rbyte (ring : ByteArray) (i mask : USize) : UInt8 := ring.data[(i &&& mask).toNat]?.getD 0

theorem wget_rbyte {ring : ByteArray} {i mask : USize} {k : Nat} {hm : mask.toNat = 2 ^ k - 1}
    {hs : ring.size = 2 ^ k} : wget ring i mask hm hs = rbyte ring i mask :=
  UInt8.toNat_inj.mp (by unfold wget rbyte; rw [uget_toNat])

theorem rbyte_congr {ring : ByteArray} {i j mask : USize} (h : i &&& mask = j &&& mask) :
    rbyte ring i mask = rbyte ring j mask := by
  unfold rbyte
  rw [h]

/-- The byte `j` back from the unmasked window position `o`, or 0 before `j` bytes are written. -/
def backB (ring : ByteArray) (mask o j : USize) : UInt8 := if j ≤ o then rbyte ring (o - j) mask else 0

private theorem data_uset' (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) :
    (a.uset i v h).data = a.data.set i.toNat v h := by
  cases a
  rfl

theorem rbyte_put_same {ring : ByteArray} {i mask : USize} {v : UInt8} (h : (i &&& mask).toNat < ring.size) :
    rbyte (ringWrite ring (i &&& mask) v h) i mask = v := by
  unfold rbyte ringWrite
  rw [data_uset']
  simp

theorem rbyte_put_ne {ring : ByteArray} {i j mask : USize} {v : UInt8} (h : (i &&& mask).toNat < ring.size)
    (hne : j &&& mask ≠ i &&& mask) : rbyte (ringWrite ring (i &&& mask) v h) j mask = rbyte ring j mask := by
  unfold rbyte ringWrite
  rw [data_uset', Array.getElem?_set]
  have hne' : (i &&& mask).toNat ≠ (j &&& mask).toNat := fun e => hne (USize.toNat_inj.mp e).symm
  rw [ite_eq_right hne']

theorem one_toNat' : (USize.ofNat 1).toNat = 1 := fastLit (by decide)

theorem two_toNat' : (USize.ofNat 2).toNat = 2 := fastLit (by decide)

/-- A byte written at `o` is the first back from `o + 1`, and the first back from `o` the second. -/
theorem backB_put {ring : ByteArray} {mask o : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (h2 : 2 ≤ 2 ^ k) (ho : o.toNat + 1 < 2 ^ 32) (v : UInt8) (h : (o &&& mask).toNat < ring.size) :
    backB (ringWrite ring (o &&& mask) v h) mask (o + USize.ofNat 1) (USize.ofNat 1) = v ∧
      backB (ringWrite ring (o &&& mask) v h) mask (o + USize.ofNat 1) (USize.ofNat 2) =
        backB ring mask o (USize.ofNat 1) := by
  have e1 : (o + USize.ofNat 1).toNat = o.toNat + 1 := fastIdx_add ho
  have h1 := one_toNat'
  have h2' := two_toNat'
  constructor
  · unfold backB
    rw [ite_eq_left (USize.le_iff_toNat_le.mpr (by rw [h1, e1]; omega)), USize.add_sub_cancel]
    exact rbyte_put_same h
  · unfold backB
    by_cases h0 : 1 ≤ o.toNat
    · rw [ite_eq_left (USize.le_iff_toNat_le.mpr (by rw [h2', e1]; omega)),
        ite_eq_left (USize.le_iff_toNat_le.mpr (by rw [h1]; omega))]
      have e : o + USize.ofNat 1 - USize.ofNat 2 = o - USize.ofNat 1 := by
        apply USize.toNat_inj.mp
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h2', e1]; omega)), e1, h2',
          USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h1]; omega)), h1]
        omega
      rw [e]
      apply rbyte_put_ne
      -- one back from `o` is another place in a window of at least two bytes
      have hn := ringNext_ne hk hm h2 (mask_lt (i := o - USize.ofNat 1) hm)
      intro he
      apply hn
      unfold ringNext
      rw [mask_add_l hk hm, USize.sub_add_cancel, ← he]
    · rw [ite_eq_right (fun h => by have := USize.le_iff_toNat_le.mp h; rw [h2', e1] at this; omega),
        ite_eq_right (fun h => by have := USize.le_iff_toNat_le.mp h; rw [h1] at this; omega)]

/-- `(o + 1) + (n - 1)` is `o + n`. -/
theorem us_succ_pred (o n : USize) : o + USize.ofNat 1 + (n - USize.ofNat 1) = o + n := by
  rw [USize.add_assoc, USize.add_comm (USize.ofNat 1), USize.sub_add_cancel]

/-! ### The runs keep the context bytes -/

/-- A window position `wpos` at the unmasked `o`, and the context bytes the window's two before it. -/
def BackAt (mask : USize) (ring : ByteArray) (wpos o : USize) (p1 p2 : UInt8) : Prop :=
  wpos = o &&& mask ∧ p1 = backB ring mask o (USize.ofNat 1) ∧ p2 = backB ring mask o (USize.ofNat 2)

/-- What a literal run of `n` leaves, from `o`: no more literals left than it was given, and the position and context
bytes at `o` plus the literals it wrote. -/
def LitBack (mask : USize) (n o : USize) (r : LitRun) : Prop :=
  r.left.toNat ≤ n.toNat ∧ BackAt mask r.ring r.wpos (o + n - r.left) r.p1 r.p2

theorem LitBack.step {mask n o : USize} {r : LitRun} (hn : n ≠ 0)
    (h : LitBack mask (n - USize.ofNat 1) (o + USize.ofNat 1) r) : LitBack mask n o r := by
  obtain ⟨h1, h2⟩ := h
  rw [us_succ_pred] at h2
  exact ⟨by rw [usize_pred hn] at h1; omega, h2⟩

section
variable {k : Nat} {mask : USize} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (h2 : 2 ≤ 2 ^ k)

include hk hmask h2 in
/-- A byte written, as each run writes one. -/
theorem BackAt.put {ring : ByteArray} {wpos o : USize} {p1 p2 : UInt8} (hb : BackAt mask ring wpos o p1 p2)
    (ho : o.toNat + 1 < 2 ^ 32) (v : UInt8) (h : wpos.toNat < ring.size) :
    BackAt mask (ringWrite ring wpos v h) (ringNext wpos mask) (o + USize.ofNat 1) v p1 := by
  obtain ⟨rfl, rfl, rfl⟩ := hb
  have e := backB_put hk hmask h2 ho v h
  exact ⟨(by unfold ringNext; rw [mask_add_l hk hmask]), e.1.symm, e.2.symm⟩

include hk hmask h2 in
theorem copyRun_back {d size : USize} (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (N : Nat) (n : USize) (o : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N → o.toNat + n.toNat < 2 ^ 32 → BackAt mask ring wpos o p1 p2 →
      BackAt mask (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).ring
        (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).wpos (o + n)
        (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).p1
        (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).p2 := by
  intro N
  induction N with
  | zero =>
    intro n o ring wpos p1 p2 hsize hwp hN _ hb
    have hn := usize_zero hN
    rw [copyRun, dite_eq_left hn, hn, USize.add_zero]
    exact hb
  | succ N ih =>
    intro n o ring wpos p1 p2 hsize hwp hN ho hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRun, dite_eq_right hn]
    dsimp only
    have hp := usize_pred hn
    rw [← us_succ_pred o n]
    exact ih (n - USize.ofNat 1) (o + USize.ofNat 1) _ _ _ _ _ _ (by rw [hp]; omega)
      (by rw [hp, fastIdx_add (by omega)]; omega) (BackAt.put hk hmask h2 hb (by omega) _ _)

include hk hmask h2 in
theorem wordRun_back {buf : ByteArray} :
    ∀ (N : Nat) (n idx : USize) (o : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
      (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N → o.toNat + n.toNat < 2 ^ 32 → BackAt mask ring wpos o p1 p2 →
      BackAt mask (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).ring
        (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).wpos (o + n)
        (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).p1
        (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).p2 := by
  intro N
  induction N with
  | zero =>
    intro n idx o ring wpos p1 p2 hb hb32 hsize hwp hN _ hk'
    have hn := usize_zero hN
    rw [wordRun, dite_eq_left hn, hn, USize.add_zero]
    exact hk'
  | succ N ih =>
    intro n idx o ring wpos p1 p2 hb hb32 hsize hwp hN ho hk'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [wordRun, dite_eq_right hn]
    dsimp only
    have hp := usize_pred hn
    rw [← us_succ_pred o n]
    exact ih (n - USize.ofNat 1) _ (o + USize.ofNat 1) _ _ _ _ _ _ _ _ (by rw [hp]; omega)
      (by rw [hp, fastIdx_add (by omega)]; omega) (BackAt.put hk hmask h2 hk' (by omega) _ _)

include hk hmask h2 in
theorem literalRun_back {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff : USize)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0) :
    ∀ (N : Nat) (n : USize) (o : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N → o.toNat + n.toNat < 2 ^ 32 → BackAt mask ring wpos o p1 p2 →
      LitBack mask n o (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2
        hp hw hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n o word count pos wpos ring p1 p2 hp hw hsize hwp hN _ hb
    have hn := usize_zero hN
    rw [literalRun, dite_eq_left hn]
    refine ⟨Nat.zero_le _, ?_⟩
    show BackAt mask ring wpos (o + n - 0) p1 p2
    rw [hn, USize.add_zero, USize.sub_zero]
    exact hb
  | succ N ih =>
    intro n o word count pos wpos ring p1 p2 hp hw hsize hwp hN ho hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [literalRun, dite_eq_right hn]
    dsimp only
    have hpr := usize_pred hn
    split
    · refine LitBack.step hn ?_
      exact ih (n - USize.ofNat 1) (o + USize.ofNat 1) _ _ _ _ _ _ _ _ _ _ _ (by rw [hpr]; omega)
        (by rw [hpr, fastIdx_add (by omega)]; omega) (BackAt.put hk hmask h2 hb (by omega) _ _)
    · refine ⟨Nat.le_refl _, ?_⟩
      show BackAt mask ring wpos (o + n - n) p1 p2
      rw [USize.add_sub_cancel]
      exact hb

end

end Brotli.Decoder
