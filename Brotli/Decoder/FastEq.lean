module

@[expose] public section

/-!
# Equality tests on enumerations, compiled as byte comparisons

A derived `DecidableEq` on an enumeration compiles each test `x = .c` to two calls of `ctorIdx`, which return boxed
`Nat`s, and a `Nat` comparison. `fast_deceq T [c₀, …, cₙ]`, with `T`'s constructors in order, gives the index as a byte
(`T.toU8`), a test by the bytes (`T.decEqF`) and a `@[csimp]` theorem that runs it in place of the derived one. The two
are equal because `Decidable` has one value per proposition, so proofs keep the derived instance.
-/

namespace Brotli.Decoder

open Lean in
/-- The byte index, its injectivity, the test by bytes and the `@[csimp]` swap for an enumeration `T` whose
constructors, in order, are `cs`. -/
macro "fast_deceq " T:ident " [" cs:ident,* "]" : command => do
  let n := cs.getElems.size
  let lits := (Array.range n).map fun i => Syntax.mkNumLit (toString i)
  let toU8 := mkIdent (T.getId ++ `toU8)
  let inj := mkIdent (T.getId ++ `toU8_inj)
  let fast := mkIdent (T.getId ++ `decEqF)
  let swap := mkIdent (T.getId ++ `decEq_csimp)
  let casesOn := mkIdent (T.getId ++ `casesOn)
  let inst := mkIdent (Name.mkSimple ("instDecidableEq" ++ T.getId.toString))
  `(
    /-- The constructor's index as a byte. -/
    @[inline] def $toU8 (x : $T) : UInt8 := $casesOn (motive := fun _ => UInt8) x $lits*
    theorem $inj {x y : $T} (h : $toU8 x = $toU8 y) : x = y := by
      cases x <;> cases y <;> first | rfl | exact absurd h (by decide)
    /-- Equality by the bytes. -/
    @[inline] def $fast (x y : $T) : Decidable (x = y) :=
      if h : $toU8 x = $toU8 y then isTrue ($inj h) else isFalse (fun e => h (congrArg $toU8 e))
    /-- The derived test, run as the byte comparison. -/
    @[csimp] theorem $swap : @$inst = @$fast := by
      funext x y
      exact Subsingleton.elim _ _)

end Brotli.Decoder
