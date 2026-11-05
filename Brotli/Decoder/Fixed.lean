module

public import Brotli.Spec.Stream

@[expose] public section

/-!
# Distances in fixed-width values

The spec's distance functions, on `UInt64`, each proved to be the spec's. A distance of 0 stands for the spec's `none`,
since every distance the spec gives is at least 1.
-/

namespace Brotli.Decoder

open Brotli.Spec

theorem u64_lit {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

private theorem add_small {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

private theorem sub_le {a b : UInt64} (h : b.toNat ≤ a.toNat) : (a - b).toNat = a.toNat - b.toNat :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h)

private theorem shr_small {a b : UInt64} (h : b.toNat < 64) : (a >>> b).toNat = a.toNat >>> b.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt h]

private theorem shl_small {a b : UInt64} (h : b.toNat < 64) (hv : a.toNat <<< b.toNat < 2 ^ 64) :
    (a <<< b).toNat = a.toNat <<< b.toNat := by
  rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt hv]

/-- The smaller of two values. -/
@[inline] def umin (a b : UInt64) : UInt64 := if a ≤ b then a else b

theorem umin_toNat (a b : UInt64) : (umin a b).toNat = min a.toNat b.toNat := by
  unfold umin
  by_cases h : a ≤ b
  · have h' := UInt64.le_iff_toNat_le.mp h
    rw [ite_eq_left h]
    omega
  · have h' : ¬ a.toNat ≤ b.toNat := fun e => h (UInt64.le_iff_toNat_le.mpr e)
    rw [ite_eq_right h]
    omega

/-- The context ID of a distance, from the copy length. -/
@[inline] def distCid (clen : UInt64) : UInt64 :=
  if clen = 2 then 0 else if clen = 3 then 1 else if clen = 4 then 2 else 3

/-- `distCid` is the spec's. -/
theorem distCid_toNat (clen : UInt64) : (distCid clen).toNat = distanceContextId clen.toNat := by
  unfold distCid
  by_cases h2 : clen = 2
  · subst h2
    rfl
  · by_cases h3 : clen = 3
    · subst h3
      rfl
    · by_cases h4 : clen = 4
      · subst h4
        rfl
      · rw [ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
        have e2 : clen.toNat ≠ 2 := fun e => h2 (UInt64.toNat_inj.mp e)
        have e3 : clen.toNat ≠ 3 := fun e => h3 (UInt64.toNat_inj.mp e)
        have e4 : clen.toNat ≠ 4 := fun e => h4 (UInt64.toNat_inj.mp e)
        unfold distanceContextId
        split
        · contradiction
        · contradiction
        · contradiction
        · rfl

/-- The extra bits of a distance symbol. -/
@[inline] def extraBitsFast (np nd dcode : UInt64) : UInt64 :=
  if dcode < 16 + nd then 0 else 1 + ((dcode - nd - 16) >>> (np + 1))

/-- `extraBitsFast` is the spec's. -/
theorem extraBitsFast_toNat {np nd dcode : UInt64} (hnp : np.toNat ≤ 3) (hnd : nd.toNat ≤ 120) (hd : dcode.toNat < 2 ^ 16) :
    (extraBitsFast np nd dcode).toNat = distanceExtraBits np.toNat nd.toNat dcode.toNat := by
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have hadd : (16 + nd).toNat = 16 + nd.toNat := add_small (by rw [h16]; omega)
  have hnp1 : (np + 1).toNat = np.toNat + 1 := add_small (by rw [h1]; omega)
  unfold extraBitsFast distanceExtraBits
  by_cases hlt : dcode < 16 + nd
  · have hlt' : dcode.toNat < 16 + nd.toNat := by
      rw [← hadd]
      exact UInt64.lt_iff_toNat_lt.mp hlt
    rw [ite_eq_left hlt, ite_eq_left hlt']
    rfl
  · have hge : ¬ dcode.toNat < 16 + nd.toNat := by
      rw [← hadd]
      exact fun h => hlt (UInt64.lt_iff_toNat_lt.mpr h)
    rw [ite_eq_right hlt, ite_eq_right hge]
    have hs1 : (dcode - nd).toNat = dcode.toNat - nd.toNat := sub_le (by omega)
    have hs2 : (dcode - nd - 16).toNat = dcode.toNat - nd.toNat - 16 := by
      rw [sub_le (by rw [hs1, h16]; omega), hs1, h16]
    have hshift := shr_small (a := dcode - nd - 16) (b := np + 1) (by rw [hnp1]; omega)
    rw [hs2, hnp1] at hshift
    have hle : (dcode.toNat - nd.toNat - 16) >>> (np.toNat + 1) ≤ dcode.toNat - nd.toNat - 16 := Nat.shiftRight_le _ _
    rw [add_small (by rw [h1, hshift]; omega), h1, hshift]

/-- A base less a small amount, 0 if that isn't positive. -/
@[inline] def shortSub (b x : UInt64) : UInt64 :=
  if b ≤ x then 0 else b - x

/-- The offsets of the special distance symbols from 4 on. -/
@[inline] def shortAdjust (b i : UInt64) : UInt64 :=
  if i = 0 then shortSub b 1
  else if i = 1 then b + 1
  else if i = 2 then shortSub b 2
  else if i = 3 then b + 2
  else if i = 4 then shortSub b 3
  else b + 3

/-- A special distance symbol's value, 0 if it isn't positive. -/
@[inline] def shortDist (d0 d1 d2 d3 dcode : UInt64) : UInt64 :=
  if dcode = 0 then d0
  else if dcode = 1 then d1
  else if dcode = 2 then d2
  else if dcode = 3 then d3
  else if dcode < 10 then shortAdjust d0 (dcode - 4)
  else shortAdjust d1 (dcode - 10)

private theorem shortSub_toNat (b x : UInt64) : (shortSub b x).toNat = ((b.toNat : Int) - (x.toNat : Int)).toNat := by
  unfold shortSub
  by_cases h : b ≤ x
  · have h' := UInt64.le_iff_toNat_le.mp h
    rw [ite_eq_left h]
    show 0 = _
    omega
  · have h' : ¬ b.toNat ≤ x.toNat := fun e => h (UInt64.le_iff_toNat_le.mpr e)
    rw [ite_eq_right h, sub_le (by omega)]
    omega

private theorem plus_toNat {b x : UInt64} (hb : b.toNat < 2 ^ 32) (hx : x.toNat ≤ 3) :
    (b + x).toNat = ((b.toNat : Int) + (x.toNat : Int)).toNat := by
  rw [add_small (by omega)]
  omega

/-- `shortDist` is the spec's `specialDistance`, with 0 standing for any value that isn't positive. -/
theorem shortDist_toNat {d0 d1 d2 d3 dcode : UInt64} (h0 : d0.toNat < 2 ^ 32) (h1 : d1.toNat < 2 ^ 32) (h : dcode.toNat < 16) :
    (shortDist d0 d1 d2 d3 dcode).toNat =
      (specialDistance ⟨d0.toNat, d1.toNat, d2.toNat, d3.toNat⟩ ⟨dcode.toNat, h⟩).toNat := by
  have hid : dcode = UInt64.ofNat dcode.toNat := by simp
  generalize hn : dcode.toNat = n at h
  have hd : dcode = UInt64.ofNat n := by rw [← hn]; exact hid
  subst hd
  have one : (1 : UInt64).toNat = 1 := rfl
  have two : (2 : UInt64).toNat = 2 := rfl
  have three : (3 : UInt64).toNat = 3 := rfl
  match n, h with
  | 0, _ => show d0.toNat = (d0.toNat : Int).toNat; omega
  | 1, _ => show d1.toNat = (d1.toNat : Int).toNat; omega
  | 2, _ => show d2.toNat = (d2.toNat : Int).toNat; omega
  | 3, _ => show d3.toNat = (d3.toNat : Int).toNat; omega
  | 4, _ => exact shortSub_toNat d0 1
  | 5, _ => exact plus_toNat (x := 1) h0 (by rw [one]; omega)
  | 6, _ => exact shortSub_toNat d0 2
  | 7, _ => exact plus_toNat (x := 2) h0 (by rw [two]; omega)
  | 8, _ => exact shortSub_toNat d0 3
  | 9, _ => exact plus_toNat (x := 3) h0 (by rw [three]; omega)
  | 10, _ => exact shortSub_toNat d1 1
  | 11, _ => exact plus_toNat (x := 1) h1 (by rw [one]; omega)
  | 12, _ => exact shortSub_toNat d1 2
  | 13, _ => exact plus_toNat (x := 2) h1 (by rw [two]; omega)
  | 14, _ => exact shortSub_toNat d1 3
  | 15, _ => exact plus_toNat (x := 3) h1 (by rw [three]; omega)
  | _ + 16, h => exact absurd h (by omega)

/-- A distance symbol's distance, 0 where the spec gives `none`. -/
@[inline] def distFast (np nd d0 d1 d2 d3 dcode extra : UInt64) : UInt64 :=
  if dcode < 16 then shortDist d0 d1 d2 d3 dcode
  else if dcode < 16 + nd then dcode - 15
  else
    let x := dcode - nd - 16
    let offset := ((2 + ((x >>> np) &&& 1)) <<< extraBitsFast np nd dcode) - 4
    ((offset + extra) <<< np) + (x &&& (((1 : UInt64) <<< np) - 1)) + nd + 1

private theorem far_toNat {np nd dcode extra : UInt64} (hnp : np.toNat ≤ 3) (hnd : nd.toNat ≤ 120) (hd : dcode.toNat < 2 ^ 16)
    (hge : 16 + nd.toNat ≤ dcode.toNat) (hbits : (extraBitsFast np nd dcode).toNat ≤ 24)
    (hx : extra.toNat < 2 ^ (extraBitsFast np nd dcode).toNat) :
    ((((2 + (((dcode - nd - 16) >>> np) &&& 1)) <<< extraBitsFast np nd dcode) - 4 + extra) <<< np +
        ((dcode - nd - 16) &&& (((1 : UInt64) <<< np) - 1)) + nd + 1).toNat =
      ((((2 + (((dcode.toNat - nd.toNat - 16) >>> np.toNat) &&& 1)) <<< distanceExtraBits np.toNat nd.toNat dcode.toNat) - 4 +
        extra.toNat) <<< np.toNat) + ((dcode.toNat - nd.toNat - 16) &&& postfixMask np.toNat) + nd.toNat + 1 := by
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h2 : (2 : UInt64).toNat = 2 := rfl
  have h4 : (4 : UInt64).toNat = 4 := rfl
  have hs1 : (dcode - nd).toNat = dcode.toNat - nd.toNat := sub_le (by omega)
  have hs2 : (dcode - nd - 16).toNat = dcode.toNat - nd.toNat - 16 := by
    rw [sub_le (by rw [hs1, h16]; omega), hs1, h16]
  have hnb1 : 1 ≤ (extraBitsFast np nd dcode).toNat := by
    rw [extraBitsFast_toNat hnp hnd hd]
    unfold distanceExtraBits
    rw [ite_eq_right (by omega)]
    exact Nat.le_add_right 1 _
  rw [← extraBitsFast_toNat hnp hnd hd]
  generalize extraBitsFast np nd dcode = nb at hbits hx hnb1 ⊢
  generalize dcode - nd - 16 = X at hs2 ⊢
  rw [← hs2]
  have hxs : (X >>> np).toNat = X.toNat >>> np.toNat := shr_small (by omega)
  have hbit : ((X >>> np) &&& 1).toNat = (X.toNat >>> np.toNat) &&& 1 := by
    rw [UInt64.toNat_and, hxs, h1]
  have hbitle : (X.toNat >>> np.toNat) &&& 1 ≤ 1 := Nat.and_le_right
  have htop : (2 + ((X >>> np) &&& 1)).toNat = 2 + ((X.toNat >>> np.toNat) &&& 1) := by
    rw [add_small (by rw [h2, hbit]; omega), h2, hbit]
  have hpow : 2 ^ nb.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hbits
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hposN : 1 ≤ 2 ^ nb.toNat := Nat.two_pow_pos _
  have hprod : (2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat ≤ 3 * 2 ^ 24 := by
    rw [Nat.shiftLeft_eq]
    exact Nat.mul_le_mul (by omega) hpow
  have hge4 : 4 ≤ (2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat := by
    rw [Nat.shiftLeft_eq]
    have hp2 : 2 ^ 1 ≤ 2 ^ nb.toNat := Nat.pow_le_pow_right (by decide) hnb1
    have hm := Nat.mul_le_mul (show 2 ≤ 2 + ((X.toNat >>> np.toNat) &&& 1) by omega) hp2
    exact Nat.le_trans (by decide) hm
  have hb64 : nb.toNat < 64 := by omega
  have hshift : ((2 + ((X >>> np) &&& 1)) <<< nb).toNat = (2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat := by
    rw [shl_small hb64 (by rw [htop]; omega), htop]
  have hoff : ((2 + ((X >>> np) &&& 1)) <<< nb - 4).toNat = ((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat) - 4 := by
    rw [sub_le (by rw [hshift, h4]; omega), hshift, h4]
  have hA : ((2 + ((X >>> np) &&& 1)) <<< nb - 4 + extra).toNat =
      ((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat) - 4 + extra.toNat := by
    rw [add_small (by rw [hoff]; omega), hoff]
  have hAlt : ((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat) - 4 + extra.toNat < 2 ^ 26 := by
    have : (2 : Nat) ^ 26 = 67108864 := by decide
    omega
  have hpow8 : 2 ^ np.toNat ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hnp
  have hs8 : (2 : Nat) ^ 3 = 8 := by decide
  have hAshift : (((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat) - 4 + extra.toNat) <<< np.toNat < 2 ^ 29 := by
    rw [Nat.shiftLeft_eq]
    have hm := Nat.mul_le_mul (Nat.le_of_lt hAlt) hpow8
    have : (2 : Nat) ^ 26 * 2 ^ 3 < 2 ^ 29 + 1 := by decide
    have h229 : (2 : Nat) ^ 29 = 536870912 := by decide
    have h226 : (2 : Nat) ^ 26 = 67108864 := by decide
    have hltm : ((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat - 4 + extra.toNat) * 2 ^ np.toNat < 2 ^ 26 * 2 ^ 3 :=
      Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hAlt (Nat.two_pow_pos _)) (Nat.mul_le_mul_left _ hpow8)
    have : (2 : Nat) ^ 26 * 2 ^ 3 = 2 ^ 29 := by decide
    omega
  have hC : (((2 + ((X >>> np) &&& 1)) <<< nb - 4 + extra) <<< np).toNat =
      (((2 + ((X.toNat >>> np.toNat) &&& 1)) <<< nb.toNat) - 4 + extra.toNat) <<< np.toNat := by
    rw [shl_small (by omega) (by rw [hA]; have : (2 : Nat) ^ 29 < 2 ^ 64 := by decide
                                 omega), hA]
  have hmask : (((1 : UInt64) <<< np) - 1).toNat = postfixMask np.toNat := by
    have hone : ((1 : UInt64) <<< np).toNat = 1 <<< np.toNat := shl_small (by omega) (by
      rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
      have : (2 : Nat) ^ 3 < 2 ^ 64 := by decide
      omega)
    have hgt : 1 ≤ 1 <<< np.toNat := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.two_pow_pos _
    rw [sub_le (by rw [hone, h1]; exact hgt), hone, h1]
    rfl
  have hl : (X &&& (((1 : UInt64) <<< np) - 1)).toNat = X.toNat &&& postfixMask np.toNat := by
    rw [UInt64.toNat_and, hmask]
  have hmle : postfixMask np.toNat ≤ 7 := by
    unfold postfixMask
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    omega
  have hlle : X.toNat &&& postfixMask np.toNat ≤ 7 := Nat.le_trans Nat.and_le_right hmle
  have h229 : (2 : Nat) ^ 29 = 536870912 := by decide
  rw [add_small (by
      rw [add_small (by
          rw [add_small (by rw [hC, hl]; omega), hC, hl]
          omega), add_small (by rw [hC, hl]; omega), hC, hl, h1]
      omega),
    add_small (by
      rw [add_small (by rw [hC, hl]; omega), hC, hl]
      omega),
    add_small (by rw [hC, hl]; omega), hC, hl, h1]

/-- `distFast` is the spec's `distanceOf`. -/
theorem distFast_spec {np nd d0 d1 d2 d3 dcode extra : UInt64} (hnp : np.toNat ≤ 3) (hnd : nd.toNat ≤ 120)
    (hd : dcode.toNat < 2 ^ 16) (h0 : d0.toNat < 2 ^ 32) (h1 : d1.toNat < 2 ^ 32)
    (hbits : (extraBitsFast np nd dcode).toNat ≤ 24) (hx : extra.toNat < 2 ^ (extraBitsFast np nd dcode).toNat) :
    distanceOf np.toNat nd.toNat ⟨d0.toNat, d1.toNat, d2.toNat, d3.toNat⟩ dcode.toNat extra.toNat =
      if distFast np nd d0 d1 d2 d3 dcode extra = 0 then none else some (distFast np nd d0 d1 d2 d3 dcode extra).toNat := by
  have h16 : (16 : UInt64).toNat = 16 := rfl
  have zero : ∀ x : UInt64, x = 0 ↔ x.toNat = 0 := fun x =>
    ⟨fun e => by rw [e]; rfl, fun e => UInt64.toNat_inj.mp (by rw [e]; rfl)⟩
  have hadd : (16 + nd).toNat = 16 + nd.toNat := add_small (by rw [h16]; omega)
  unfold distFast distanceOf
  by_cases hs : dcode < 16
  · have hs' : dcode.toNat < 16 := UInt64.lt_iff_toNat_lt.mp hs
    rw [ite_eq_left hs, dite_eq_left hs']
    have hv := shortDist_toNat (d2 := d2) (d3 := d3) h0 h1 hs'
    dsimp only
    by_cases hz : shortDist d0 d1 d2 d3 dcode = 0
    · rw [ite_eq_left hz]
      have : ((specialDistance ⟨d0.toNat, d1.toNat, d2.toNat, d3.toNat⟩ ⟨dcode.toNat, hs'⟩).toNat) = 0 := by
        rw [← hv, hz]
        rfl
      rw [ite_eq_left (by omega)]
    · rw [ite_eq_right hz]
      have hne : (shortDist d0 d1 d2 d3 dcode).toNat ≠ 0 := fun e => hz ((zero _).mpr e)
      rw [ite_eq_right (by omega), hv]
  · have hs' : ¬ dcode.toNat < 16 := fun e => hs (UInt64.lt_iff_toNat_lt.mpr e)
    rw [ite_eq_right hs, dite_eq_right hs']
    by_cases hdir : dcode < 16 + nd
    · have hdir' : dcode.toNat < 16 + nd.toNat := by
        rw [← hadd]
        exact UInt64.lt_iff_toNat_lt.mp hdir
      rw [ite_eq_left hdir, ite_eq_left hdir']
      have h15 : (15 : UInt64).toNat = 15 := rfl
      have hv : (dcode - 15).toNat = dcode.toNat - 15 := sub_le (by rw [h15]; omega)
      rw [ite_eq_right (fun e => by
        have := (zero _).mp e
        omega), hv]
    · have hdir' : ¬ dcode.toNat < 16 + nd.toNat := by
        rw [← hadd]
        exact fun e => hdir (UInt64.lt_iff_toNat_lt.mpr e)
      rw [ite_eq_right hdir, ite_eq_right hdir']
      dsimp only
      have hv := far_toNat hnp hnd hd (by omega) hbits hx
      rw [ite_eq_right (fun e => by
        have := (zero _).mp e
        rw [hv] at this
        exact Nat.succ_ne_zero _ this), hv]

/-- With distance symbol 0, the distance is the last one. -/
theorem distanceOf_zero (np nd : Nat) (r : Distances) :
    distanceOf np nd r 0 0 = if r.last = 0 then none else some r.last := by
  unfold distanceOf
  rw [dite_eq_left (by decide)]
  show (if ((r.last : Int)) ≤ 0 then none else some ((r.last : Int)).toNat) = _
  by_cases h : r.last = 0
  · simp [h]
  · simp [h]

end Brotli.Decoder
