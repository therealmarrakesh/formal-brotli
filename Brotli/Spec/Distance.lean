module

public import Brotli.Spec.PrefixCode

@[expose] public section

/-!
# Encoding of distances

RFC 7932 §4.
-/

namespace Brotli.Spec

/-- POSTFIX_MASK (§4). -/
def postfixMask (npostfix : Nat) : Nat :=
  (1 <<< npostfix) - 1

/-- The number of extra bits of the distance symbol `dcode` (§4). -/
def distanceExtraBits (npostfix ndirect dcode : Nat) : Nat :=
  if dcode < 16 + ndirect then 0 else 1 + ((dcode - ndirect - 16) >>> (npostfix + 1))

/-- The size of the distance alphabet (§4). -/
def distanceAlphabetSize (npostfix ndirect : Nat) : Nat :=
  16 + ndirect + (48 <<< npostfix)

/-- The distance alphabet is exactly the symbols whose extra bits are at most 24. -/
theorem distanceExtraBits_le_iff (npostfix ndirect dcode : Nat) :
    dcode < distanceAlphabetSize npostfix ndirect ↔
      distanceExtraBits npostfix ndirect dcode ≤ 24 := by
  unfold distanceExtraBits distanceAlphabetSize
  rw [Nat.shiftLeft_eq]
  have hpos := Nat.two_pow_pos npostfix
  by_cases hd : dcode < 16 + ndirect
  · rw [ite_eq_left hd]
    constructor
    · intro _; omega
    · intro _; omega
  · rw [ite_eq_right hd, Nat.shiftRight_eq_div_pow]
    have h48 : 24 * 2 ^ (npostfix + 1) = 48 * 2 ^ npostfix := by rw [Nat.pow_succ]; omega
    have hdiv : (dcode - ndirect - 16) / 2 ^ (npostfix + 1) < 24 ↔
        dcode - ndirect - 16 < 24 * 2 ^ (npostfix + 1) :=
      Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)
    omega

/-- The maximum of 24 extra bits is reached: the last symbol of the distance alphabet has 24. -/
theorem distanceExtraBits_last (npostfix ndirect : Nat) :
    distanceExtraBits npostfix ndirect (distanceAlphabetSize npostfix ndirect - 1) = 24 := by
  unfold distanceExtraBits distanceAlphabetSize
  rw [Nat.shiftLeft_eq]
  have hpos := Nat.two_pow_pos npostfix
  rw [ite_eq_right (by omega), Nat.shiftRight_eq_div_pow]
  have hpow : 2 ^ (npostfix + 1) = 2 * 2 ^ npostfix := by rw [Nat.pow_succ]; omega
  have : (16 + ndirect + 48 * 2 ^ npostfix - 1 - ndirect - 16) / 2 ^ (npostfix + 1) = 23 := by
    rw [hpow]
    apply Nat.div_eq_of_lt_le <;> omega
  omega

/-- The ring buffer of the four last distances (§4). -/
structure Distances where
  last : Nat
  secondToLast : Nat
  thirdToLast : Nat
  fourthToLast : Nat
  deriving DecidableEq

/-- The ring buffer's initial values (§4). -/
def initialDistances : Distances :=
  ⟨4, 11, 15, 16⟩

/-- The value of each of the 16 special distance symbols (§4). -/
def specialDistance (r : Distances) : Fin 16 → Int
  | 0 => r.last
  | 1 => r.secondToLast
  | 2 => r.thirdToLast
  | 3 => r.fourthToLast
  | 4 => r.last - 1
  | 5 => r.last + 1
  | 6 => r.last - 2
  | 7 => r.last + 2
  | 8 => r.last - 3
  | 9 => r.last + 3
  | 10 => r.secondToLast - 1
  | 11 => r.secondToLast + 1
  | 12 => r.secondToLast - 2
  | 13 => r.secondToLast + 2
  | 14 => r.secondToLast - 3
  | 15 => r.secondToLast + 3
  | ⟨_ + 16, h⟩ => absurd h (by omega)

/-- The backward distance of the distance symbol `dcode` with extra bits value `dextra` (§4), or `none`
if a special symbol resolves to a zero or negative value. -/
def distanceOf (npostfix ndirect : Nat) (r : Distances) (dcode dextra : Nat) : Option Nat :=
  if h : dcode < 16 then
    let v := specialDistance r ⟨dcode, h⟩
    if v ≤ 0 then none else some v.toNat
  else if dcode < 16 + ndirect then
    some (dcode - 15)
  else
    let ndistbits := distanceExtraBits npostfix ndirect dcode
    let hcode := (dcode - ndirect - 16) >>> npostfix
    let lcode := (dcode - ndirect - 16) &&& postfixMask npostfix
    let offset := ((2 + (hcode &&& 1)) <<< ndistbits) - 4
    some (((offset + dextra) <<< npostfix) + lcode + ndirect + 1)

/-- A distance code and its extra bits (§4). Returns the distance symbol and the distance. -/
def readDistance (npostfix ndirect : Nat) (code : PrefixCode) (r : Distances) (bs : List Bool) :
    Option ((Nat × Nat) × List Bool) := do
  let (dcode, bs) ← decodeSymbol code bs
  let (dextra, bs) ← readInt (distanceExtraBits npostfix ndirect dcode) bs
  let d ← distanceOf npostfix ndirect r dcode dextra
  some ((dcode, d), bs)

/-- The ring buffer after a distance: symbol 0 and dictionary references are not pushed (§4). -/
def pushDistance (r : Distances) (dcode d : Nat) (dictionary : Bool) : Distances :=
  if dcode = 0 ∨ dictionary then r else ⟨d, r.last, r.secondToLast, r.thirdToLast⟩

end Brotli.Spec
