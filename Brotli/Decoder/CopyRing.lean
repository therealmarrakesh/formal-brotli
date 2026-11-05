import Brotli.Decoder.LoopInv

/-!
# Copy and word runs that return only the window

`copyRing` and `wordRing` are the copy and word loops without the last two bytes: they carry and return only the window,
so that their result is the array itself and nothing is allocated. What `copyRun` and `wordRun` also return is worked
out after the loop: the write position is the old one plus the run, wrapped to the window, and the last two bytes are
read back from the window, the second only when the run wrote at least two (`copyRunF`, `wordRunF`). Each is proved
equal to the loop it replaces, for a window of at least two bytes and a run of at least one.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Positions in the window -/

private theorem mask_mod {x mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) :
    (x &&& mask).toNat = x.toNat % 2 ^ k := by
  rw [USize.toNat_and, hm]
  exact Nat.and_two_pow_sub_one_eq_mod _ _

private theorem one_toNat : (USize.ofNat 1).toNat = 1 := usize_ofNat' (by decide)

private theorem two_toNat : (USize.ofNat 2).toNat = 2 := usize_ofNat' (by decide)

/-- The next position, as a number. -/
theorem ringNext_toNat {p mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hp : p.toNat < 2 ^ k) : (ringNext p mask).toNat = if p.toNat + 1 = 2 ^ k then 0 else p.toNat + 1 := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  unfold ringNext
  rw [mask_mod hm, usize_succ (by omega)]
  split
  · rename_i he
    rw [he, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem ringNext_lt {p mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) (hp : p.toNat < 2 ^ k) :
    (ringNext p mask).toNat < 2 ^ k := by
  rw [ringNext_toNat hk hm hp]
  split <;> omega

/-- One back from the next position is the position written. -/
theorem back_one {p mask size : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : size.toNat = 2 ^ k) (hp : p.toNat < 2 ^ k) : ringBack (ringNext p mask) (USize.ofNat 1) mask size = p := by
  apply USize.toNat_inj.mp
  have hR1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h1 := one_toNat
  rw [ringBack_toNat hk hm hs (ringNext_lt hk hm hp) (by omega) (by omega), h1, ringNext_toNat hk hm hp]
  by_cases he : p.toNat + 1 = 2 ^ k
  · simp only [he, ↓reduceIte]
    unfold ringIdx
    split <;> omega
  · simp only [he, ↓reduceIte]
    unfold ringIdx
    split <;> omega

/-- Two back from two positions on is the first position written. -/
theorem back_two {p mask size : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : size.toNat = 2 ^ k) (h2 : 2 ≤ 2 ^ k) (hp : p.toNat < 2 ^ k) :
    ringBack (ringNext (ringNext p mask) mask) (USize.ofNat 2) mask size = p := by
  apply USize.toNat_inj.mp
  have h2' := two_toNat
  have hq := ringNext_lt hk hm hp
  rw [ringBack_toNat hk hm hs (ringNext_lt hk hm hq) (by omega) (by omega), h2', ringNext_toNat hk hm hq,
    ringNext_toNat hk hm hp]
  by_cases he : p.toNat + 1 = 2 ^ k
  · simp only [he, ↓reduceIte]
    have h0 : ¬ (0 + 1 = 2 ^ k) := by omega
    simp only [h0, ↓reduceIte]
    unfold ringIdx
    split <;> omega
  · simp only [he, ↓reduceIte]
    by_cases he2 : p.toNat + 1 + 1 = 2 ^ k
    · simp only [he2, ↓reduceIte]
      unfold ringIdx
      split <;> omega
    · simp only [he2, ↓reduceIte]
      unfold ringIdx
      split <;> omega

/-- The next position is another, in a window of at least two bytes. -/
theorem ringNext_ne {p mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) (h2 : 2 ≤ 2 ^ k)
    (hp : p.toNat < 2 ^ k) : p ≠ ringNext p mask := fun e => by
  have := congrArg USize.toNat e
  rw [ringNext_toNat hk hm hp] at this
  split at this <;> omega

/-! ### Reading back what was written -/

theorem uget_congr {a : ByteArray} {i j : USize} (e : i = j) (h : i.toNat < a.size) (h' : j.toNat < a.size) :
    a.uget i h = a.uget j h' := by
  subst e
  rfl

theorem uget_write_same (ring : ByteArray) (w : USize) (v : UInt8) (h : w.toNat < ring.size)
    (h' : w.toNat < (ringWrite ring w v h).size) : (ringWrite ring w v h).uget w h' = v := by
  cases ring
  simp [ringWrite, ByteArray.uset, ByteArray.uget, Array.uset]

theorem uget_write_ne (ring : ByteArray) (w i : USize) (v : UInt8) (h : w.toNat < ring.size)
    (h' : i.toNat < (ringWrite ring w v h).size) (h'' : i.toNat < ring.size) (hne : i ≠ w) :
    (ringWrite ring w v h).uget i h' = ring.uget i h'' := by
  have hne' : w.toNat ≠ i.toNat := fun e => hne (USize.toNat_inj.mp e).symm
  cases ring
  simp [ringWrite, ByteArray.uset, ByteArray.uget, Array.uset, Array.getElem_set, hne']

private theorem pow_dvd_usize {k : Nat} (hk : k ≤ 24) : 2 ^ k ∣ 2 ^ System.Platform.numBits :=
  Nat.pow_dvd_pow 2 (by rcases System.Platform.numBits_eq with h | h <;> omega)

/-- The position after `n` more, wrapped to the window. -/
private theorem next_add {w n mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) (hn : n ≠ 0) :
    (ringNext w mask + (n - USize.ofNat 1)) &&& mask = (w + n) &&& mask := by
  apply USize.toNat_inj.mp
  have hd := pow_dvd_usize hk
  have hn1 := usize_ne hn
  unfold ringNext
  rw [mask_mod hm, mask_mod hm, USize.toNat_add, USize.toNat_add, mask_mod hm, USize.toNat_add, usize_pred hn, one_toNat,
    Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd, Nat.mod_add_mod]
  congr 1
  omega

private theorem add_zero_mask {w mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) (hw : w.toNat < 2 ^ k) :
    w = (w + 0) &&& mask := by
  apply USize.toNat_inj.mp
  rw [mask_mod hm, USize.add_zero, Nat.mod_eq_of_lt hw]

/-! ### The copy run -/

/-- Copies `n` bytes from `d` back, returning only the window. -/
def copyRing (d mask size : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k)
    (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : ByteArray :=
  if hn : n = 0 then ring
  else
    have hb : (ringBack wpos d mask size).toNat < ring.size := by
      rw [ringBack_toNat hk hmask hsz hwp hd1 hd2, hsize]
      exact ringIdx_lt hwp (by omega)
    let byte := ring.uget (ringBack wpos d mask size) hb
    have hr : wpos.toNat < ring.size := by omega
    copyRing d mask size k hk hmask hsz hd1 hd2 (n - USize.ofNat 1) (ringWrite ring wpos byte hr) (ringNext wpos mask)
      ((size_ringWrite ring wpos byte hr).trans hsize) (ringNext_lt hk hmask hwp)
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

section
variable {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k)
  (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k)

include hk hmask hsz hd1 hd2 in
theorem copyRun_ring : ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).ring =
      copyRing d mask size k hk hmask hsz hd1 hd2 n ring wpos hsize hwp := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn := usize_zero hN
    rw [copyRun, copyRing, dite_eq_left hn, dite_eq_left hn]
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRun, copyRing, dite_eq_right hn, dite_eq_right hn]
    apply ih
    rw [usize_pred hn]
    omega

include hk hmask hsz hd1 hd2 in
theorem copyRun_wpos : ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).wpos = (wpos + n) &&& mask := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn := usize_zero hN
    rw [copyRun, dite_eq_left hn, hn]
    exact add_zero_mask hmask hwp
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRun, dite_eq_right hn]
    dsimp only
    rw [ih _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega), next_add hk hmask hn]

include hk hmask hsz hd1 hd2 in
theorem copyRun_p1 : ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N + 1 →
    ∀ hb, (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).p1 =
      (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).ring.uget
        (ringBack (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).wpos (USize.ofNat 1) mask
          size) hb := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hn1 : n - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn]; omega)
    revert hb
    rw [copyRun, dite_eq_right hn]
    dsimp only
    rw [copyRun, dite_eq_left hn1]
    intro hb
    dsimp only at hb ⊢
    rw [uget_congr (back_one hk hmask hsz hwp) hb (by rw [size_ringWrite]; omega), uget_write_same]
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    revert hb
    rw [copyRun, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

include hk hmask hsz hd1 hd2 in
theorem copyRun_p2_one {n : USize} {ring : ByteArray} {wpos : USize} {p1 p2 : UInt8} {hsize : ring.size = 2 ^ k}
    {hwp : wpos.toNat < 2 ^ k} (hN : n.toNat = 1) :
    (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).p2 = p1 := by
  have hn : n ≠ 0 := fun e => by rw [e] at hN; exact absurd hN (by decide)
  have hn1 : n - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn]; omega)
  rw [copyRun, dite_eq_right hn]
  dsimp only
  rw [copyRun, dite_eq_left hn1]

include hk hmask hsz hd1 hd2 in
theorem copyRun_p2 (h2 : 2 ≤ 2 ^ k) : ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N + 2 →
    ∀ hb, (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).p2 =
      (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).ring.uget
        (ringBack (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).wpos (USize.ofNat 2) mask
          size) hb := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact absurd hN (by decide)
    have hn1 : n - USize.ofNat 1 ≠ 0 := fun e => by
      have := usize_pred hn
      rw [e] at this
      exact absurd this (by simp; omega)
    have hn2 : n - USize.ofNat 1 - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn1, usize_pred hn]; omega)
    revert hb
    rw [copyRun, dite_eq_right hn]
    dsimp only
    rw [copyRun, dite_eq_right hn1]
    dsimp only
    rw [copyRun, dite_eq_left hn2]
    intro hb
    dsimp only at hb ⊢
    have hq := ringNext_lt hk hmask hwp
    rw [uget_congr (back_two hk hmask hsz h2 hwp) hb (by rw [size_ringWrite, size_ringWrite]; omega),
      uget_write_ne _ _ _ _ _ _ (by rw [size_ringWrite]; omega) (ringNext_ne hk hmask h2 hwp), uget_write_same]
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    revert hb
    rw [copyRun, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

end

/-- `copyRun` with the window-only loop: the position and the last two bytes worked out after it. -/
@[inline] def copyRunF (d mask size : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (h2 : 2 ≤ 2 ^ k) (_hn : n ≠ 0) : CopyRun :=
  let rg := copyRing d mask size k hk hmask hsz hd1 hd2 n ring wpos hsize hwp
  let wp := (wpos + n) &&& mask
  have hwp' : wp.toNat < 2 ^ k := by
    show ((wpos + n) &&& mask).toNat < 2 ^ k
    rw [mask_mod hmask]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hrs : rg.size = 2 ^ k := by
    show (copyRing d mask size k hk hmask hsz hd1 hd2 n ring wpos hsize hwp).size = 2 ^ k
    rw [← copyRun_ring hk hmask hsz hd1 hd2 _ n ring wpos p1 p2 hsize hwp rfl]
    exact (copyRun_inv hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp).1
  have hb1 : (ringBack wp (USize.ofNat 1) mask size).toNat < rg.size := by
    have := one_toNat
    rw [ringBack_toNat hk hmask hsz hwp' (by omega) (by have := Nat.one_le_two_pow (n := k); omega), hrs]
    exact ringIdx_lt hwp' (by omega)
  have hb2 : (ringBack wp (USize.ofNat 2) mask size).toNat < rg.size := by
    have := two_toNat
    rw [ringBack_toNat hk hmask hsz hwp' (by omega) (by omega), hrs]
    exact ringIdx_lt hwp' (by omega)
  ⟨rg, wp, rg.uget (ringBack wp (USize.ofNat 1) mask size) hb1,
    if USize.ofNat 2 ≤ n then rg.uget (ringBack wp (USize.ofNat 2) mask size) hb2 else p1⟩

/-- `copyRunF` is `copyRun`, for a run of at least one byte. -/
theorem copyRunF_eq {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (h2 : 2 ≤ 2 ^ k) (hn : n ≠ 0) :
    copyRunF d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp h2 hn =
      copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp := by
  have hn' := usize_ne hn
  have e1 := copyRun_ring hk hmask hsz hd1 hd2 _ n ring wpos p1 p2 hsize hwp rfl
  have e2 := copyRun_wpos hk hmask hsz hd1 hd2 _ n ring wpos p1 p2 hsize hwp rfl
  have e3 := copyRun_p1 hk hmask hsz hd1 hd2 (n.toNat - 1) n ring wpos p1 p2 hsize hwp (by omega)
  have e4 := fun (h : 2 ≤ n.toNat) => copyRun_p2 hk hmask hsz hd1 hd2 h2 (n.toNat - 2) n ring wpos p1 p2 hsize hwp
    (by omega)
  have e5 := fun (h : n.toNat = 1) => copyRun_p2_one hk hmask hsz hd1 hd2 (p1 := p1) (p2 := p2) (hsize := hsize)
    (hwp := hwp) h
  unfold copyRunF
  revert e1 e2 e3 e4 e5
  generalize copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp = r
  intro e1 e2 e3 e4 e5
  obtain ⟨rg, wp, q1, q2⟩ := r
  dsimp only at e1 e2 e3 e4 e5
  subst e1 e2
  dsimp only
  congr 1
  · exact (e3 _).symm
  · by_cases h : USize.ofNat 2 ≤ n
    · have h' : 2 ≤ n.toNat := by
        have := USize.le_iff_toNat_le.mp h
        rwa [two_toNat] at this
      rw [ite_eq_left h]
      exact (e4 h' _).symm
    · have h' : n.toNat = 1 := by
        have : ¬ (USize.ofNat 2).toNat ≤ n.toNat := fun e => h (USize.le_iff_toNat_le.mpr e)
        rw [two_toNat] at this
        omega
      rw [ite_eq_right h]
      exact (e5 h').symm

/-- What a copy run on the window alone leaves. -/
theorem copyRunF_inv {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (h2 : 2 ≤ 2 ^ k) (hn : n ≠ 0) :
    RingInv k (copyRunF d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp h2 hn) := by
  rw [copyRunF_eq hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp h2 hn]
  exact copyRun_inv hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp

/-! ### The word run -/

/-- Writes the next `n` bytes of a dictionary word, returning only the window. -/
def wordRing (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (n idx : USize)
    (ring : ByteArray) (wpos : USize) (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : ByteArray :=
  if hn : n = 0 then ring
  else
    have hnz := usize_ne hn
    have hpred := usize_pred hn
    let byte := buf.uget idx (by omega)
    have hr : wpos.toNat < ring.size := by omega
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    wordRing buf mask k hk hmask (n - USize.ofNat 1) (idx + USize.ofNat 1) (ringWrite ring wpos byte hr)
      (ringNext wpos mask) (by rw [hi]; omega) (by rw [hi]; omega) ((size_ringWrite ring wpos byte hr).trans hsize)
      (ringNext_lt hk hmask hwp)
termination_by n.toNat
decreasing_by
  omega

section
variable {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)

include hk hmask in
theorem wordRun_ring : ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).ring =
      wordRing buf mask k hk hmask n idx ring wpos hb hb32 hsize hwp := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn := usize_zero hN
    rw [wordRun, wordRing, dite_eq_left hn, dite_eq_left hn]
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [wordRun, wordRing, dite_eq_right hn, dite_eq_right hn]
    apply ih
    rw [usize_pred hn]
    omega

include hk hmask in
theorem wordRun_wpos : ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).wpos = (wpos + n) &&& mask := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn := usize_zero hN
    rw [wordRun, dite_eq_left hn, hn]
    exact add_zero_mask hmask hwp
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [wordRun, dite_eq_right hn]
    dsimp only
    rw [ih _ _ _ _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega), next_add hk hmask hn]

include hk hmask in
theorem wordRun_p1 : ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N + 1 →
    ∀ hb', (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).p1 =
      (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).ring.uget
        (ringBack (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).wpos (USize.ofNat 1) mask
          (mask + USize.ofNat 1)) hb' := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN hb'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hn1 : n - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn]; omega)
    have hsz : (mask + USize.ofNat 1).toNat = 2 ^ k := by
      have := Nat.one_le_two_pow (n := k)
      have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
      have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
      rw [usize_succ (by omega), hmask]
      omega
    revert hb'
    rw [wordRun, dite_eq_right hn]
    dsimp only
    rw [wordRun, dite_eq_left hn1]
    intro hb'
    dsimp only at hb' ⊢
    rw [uget_congr (back_one hk hmask hsz hwp) hb' (by rw [size_ringWrite]; omega), uget_write_same]
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN hb'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    revert hb'
    rw [wordRun, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

include hk hmask in
theorem wordRun_p2_one {n idx : USize} {ring : ByteArray} {wpos : USize} {p1 p2 : UInt8}
    {hb : idx.toNat + n.toNat ≤ buf.size} {hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1} {hsize : ring.size = 2 ^ k}
    {hwp : wpos.toNat < 2 ^ k} (hN : n.toNat = 1) :
    (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).p2 = p1 := by
  have hn : n ≠ 0 := fun e => by rw [e] at hN; exact absurd hN (by decide)
  have hn1 : n - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn]; omega)
  rw [wordRun, dite_eq_right hn]
  dsimp only
  rw [wordRun, dite_eq_left hn1]

include hk hmask in
theorem wordRun_p2 (h2 : 2 ≤ 2 ^ k) : ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N + 2 →
    ∀ hb', (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).p2 =
      (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).ring.uget
        (ringBack (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).wpos (USize.ofNat 2) mask
          (mask + USize.ofNat 1)) hb' := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN hb'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact absurd hN (by decide)
    have hn1 : n - USize.ofNat 1 ≠ 0 := fun e => by
      have := usize_pred hn
      rw [e] at this
      exact absurd this (by simp; omega)
    have hn2 : n - USize.ofNat 1 - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn1, usize_pred hn]; omega)
    have hsz : (mask + USize.ofNat 1).toNat = 2 ^ k := by
      have := Nat.one_le_two_pow (n := k)
      have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
      have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
      rw [usize_succ (by omega), hmask]
      omega
    revert hb'
    rw [wordRun, dite_eq_right hn]
    dsimp only
    rw [wordRun, dite_eq_right hn1]
    dsimp only
    rw [wordRun, dite_eq_left hn2]
    intro hb'
    dsimp only at hb' ⊢
    have hq := ringNext_lt hk hmask hwp
    rw [uget_congr (back_two hk hmask hsz h2 hwp) hb' (by rw [size_ringWrite, size_ringWrite]; omega),
      uget_write_ne _ _ _ _ _ _ (by rw [size_ringWrite]; omega) (ringNext_ne hk hmask h2 hwp), uget_write_same]
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN hb'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    revert hb'
    rw [wordRun, dite_eq_right hn]
    dsimp only
    exact ih _ _ _ _ _ _ _ _ _ _ (by rw [usize_pred hn]; omega)

end

/-- `wordRun` with the window-only loop: the position and the last two bytes worked out after it. -/
@[inline] def wordRunF (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
    (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k)
    (h2 : 2 ≤ 2 ^ k) (_hn : n ≠ 0) : CopyRun :=
  let rg := wordRing buf mask k hk hmask n idx ring wpos hb hb32 hsize hwp
  let wp := (wpos + n) &&& mask
  have hsz : (mask + USize.ofNat 1).toNat = 2 ^ k := by
    have := Nat.one_le_two_pow (n := k)
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
    rw [usize_succ (by omega), hmask]
    omega
  have hwp' : wp.toNat < 2 ^ k := by
    show ((wpos + n) &&& mask).toNat < 2 ^ k
    rw [mask_mod hmask]
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hrs : rg.size = 2 ^ k := by
    show (wordRing buf mask k hk hmask n idx ring wpos hb hb32 hsize hwp).size = 2 ^ k
    rw [← wordRun_ring hk hmask _ n idx ring wpos p1 p2 hb hb32 hsize hwp rfl]
    exact (wordRun_inv hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp).1
  have hb1 : (ringBack wp (USize.ofNat 1) mask (mask + USize.ofNat 1)).toNat < rg.size := by
    have := one_toNat
    rw [ringBack_toNat hk hmask hsz hwp' (by omega) (by have := Nat.one_le_two_pow (n := k); omega), hrs]
    exact ringIdx_lt hwp' (by omega)
  have hb2 : (ringBack wp (USize.ofNat 2) mask (mask + USize.ofNat 1)).toNat < rg.size := by
    have := two_toNat
    rw [ringBack_toNat hk hmask hsz hwp' (by omega) (by omega), hrs]
    exact ringIdx_lt hwp' (by omega)
  ⟨rg, wp, rg.uget (ringBack wp (USize.ofNat 1) mask (mask + USize.ofNat 1)) hb1,
    if USize.ofNat 2 ≤ n then rg.uget (ringBack wp (USize.ofNat 2) mask (mask + USize.ofNat 1)) hb2 else p1⟩

/-- `wordRunF` is `wordRun`, for a run of at least one byte. -/
theorem wordRunF_eq {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
    (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (h2 : 2 ≤ 2 ^ k)
    (hn : n ≠ 0) :
    wordRunF buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp h2 hn =
      wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp := by
  have hn' := usize_ne hn
  have e1 := wordRun_ring hk hmask _ n idx ring wpos p1 p2 hb hb32 hsize hwp rfl
  have e2 := wordRun_wpos hk hmask _ n idx ring wpos p1 p2 hb hb32 hsize hwp rfl
  have e3 := wordRun_p1 hk hmask (n.toNat - 1) n idx ring wpos p1 p2 hb hb32 hsize hwp (by omega)
  have e4 := fun (h : 2 ≤ n.toNat) => wordRun_p2 hk hmask h2 (n.toNat - 2) n idx ring wpos p1 p2 hb hb32 hsize hwp
    (by omega)
  have e5 := fun (h : n.toNat = 1) => wordRun_p2_one hk hmask (p1 := p1) (p2 := p2) (hb := hb) (hb32 := hb32)
    (hsize := hsize) (hwp := hwp) h
  unfold wordRunF
  revert e1 e2 e3 e4 e5
  generalize wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp = r
  intro e1 e2 e3 e4 e5
  obtain ⟨rg, wp, q1, q2⟩ := r
  dsimp only at e1 e2 e3 e4 e5
  subst e1 e2
  dsimp only
  congr 1
  · exact (e3 _).symm
  · by_cases h : USize.ofNat 2 ≤ n
    · have h' : 2 ≤ n.toNat := by
        have := USize.le_iff_toNat_le.mp h
        rwa [two_toNat] at this
      rw [ite_eq_left h]
      exact (e4 h' _).symm
    · have h' : n.toNat = 1 := by
        have : ¬ (USize.ofNat 2).toNat ≤ n.toNat := fun e => h (USize.le_iff_toNat_le.mpr e)
        rw [two_toNat] at this
        omega
      rw [ite_eq_right h]
      exact (e5 h').symm

/-- What a word run on the window alone leaves. -/
theorem wordRunF_inv {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
    (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (h2 : 2 ≤ 2 ^ k)
    (hn : n ≠ 0) : RingInv k (wordRunF buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp h2 hn) := by
  rw [wordRunF_eq hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp h2 hn]
  exact wordRun_inv hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp

/-! ### The runs the steps take are at least one byte -/

/-- A copy step with bytes left and room has a run of at least one. -/
theorem copy_run_ne {k cap pend : USize} {left : UInt64} (hk : k.toNat ≤ 24) (hl : ¬ left = 0)
    (hr : ¬ room k cap ≤ pend) : (umin left (room k cap - pend).toUInt64).toUSize ≠ 0 := fun e => by
  have h0 := congrArg USize.toNat e
  have hlt := room_lt hr
  have hle := room_le (cap := cap) hk
  have hR : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hU := USize.le_size
  have hU' : USize.size = 2 ^ System.Platform.numBits := USize.size_eq_two_pow
  have hl' : left.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by rw [e]; rfl))
  rw [UInt64.toNat_toUSize, umin_toNat, room_sub (Nat.le_of_lt hlt)] at h0
  have h00 : (0 : USize).toNat = 0 := rfl
  rw [h00, Nat.mod_eq_of_lt (by omega)] at h0
  omega

/-- A word step with bytes left and room has a run of at least one. -/
theorem word_run_ne {k cap pend a : USize} (hw : ¬ a = 0) (hr : ¬ room k cap ≤ pend) :
    usmin a (room k cap - pend) ≠ 0 := fun e => by
  have h0 := congrArg USize.toNat e
  have hlt := room_lt hr
  have ha : a.toNat ≠ 0 := usize_ne hw
  rw [usmin_toNat, room_sub' (Nat.le_of_lt hlt)] at h0
  have h00 : (0 : USize).toNat = 0 := rfl
  rw [h00] at h0
  omega

end Brotli.Decoder
