module

public import Brotli.Decoder.HeaderDone

@[expose] public section

/-!
# A code's lengths on scalars

At a code's lengths (`.syms`) the header machine reads one code length symbol a step, and each step builds the whole
header state again (`stepHSyms`), about forty fields for a byte or two written. `symsPlain` is such a step on the
fields it changes (`SymsS`), for its plain cases: a zero, a nonzero length, and a run of zeros. Every other case (the
code complete, a symbol too many, a short or bad read, an overflow, a run of a nonzero length) is left to `stepHSyms`
itself. `stepH_symsPlain` proves the step equal to `stepH` on the state they're written back into (`SymsS.put`): the
same refill, the same read, the same writes.

The scalar step needs no relation of its own: the lists' sizes are carried with them, and the bound `ln < 704` that
`setNext` needs comes from `ln ≤ size ≤ 704`, which each plain case keeps.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- What a step at a code's lengths changes of the header state, apart from its status. -/
structure SymsS where
  word : UInt64
  count : UInt64
  pos : USize
  head : ByteArray
  next : ByteArray
  ln : UInt64
  prevLen : UInt64
  repSym : UInt64
  repCount : UInt64
  symSum : UInt64
  headSz : head.size = 32
  nextSz : next.size = 1408

/-- A header state's fields that a step at a code's lengths changes. -/
@[inline] def SymsS.of (st : Hd) : SymsS :=
  ⟨st.word, st.count, st.pos, st.head, st.next, st.ln, st.prevLen, st.repSym, st.repCount, st.symSum, st.headSz,
    st.nextSz⟩

/-- The header state with a step's fields written back, moving on. -/
@[inline] def SymsS.put (st : Hd) (s : SymsS) : Hd :=
  { st with word := s.word, count := s.count, pos := s.pos, status := .next, head := s.head, next := s.next,
            headSz := s.headSz, nextSz := s.nextSz, ln := s.ln, prevLen := s.prevLen, repSym := s.repSym,
            repCount := s.repCount, symSum := s.symSum }

/-- The bounds a code's lengths are read within: the code's size is at most 704, and the symbols read so far at most
its size. -/
theorem syms_bounds {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) :
    st.size.toNat ≤ 704 ∧ st.ln.toNat ≤ st.size.toNat := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  have hs : SizeOk st size := hrel.2.2.2.1
  have hy : SymRel st size clc ls := hrel.2.2.2.2.2
  have := hy.ln
  have := hy.le
  have := hs.1
  have := hs.2.2
  omega

/-- Writing a state's own fields back changes only its status. -/
theorem SymsS.put_of (st : Hd) (hn : st.status = .next) : SymsS.put st (SymsS.of st) = st := by
  cases st
  cases hn
  rfl

/-- Writing back twice is writing back the second time. -/
theorem SymsS.put_put (st : Hd) (s s' : SymsS) : SymsS.put (SymsS.put st s) s' = SymsS.put st s' := rfl

/-- The fields of a state written back are the fields written. -/
theorem SymsS.of_put (st : Hd) (s : SymsS) : SymsS.of (SymsS.put st s) = s := rfl

/-- A symbol index below a code's size is below 704. -/
theorem ln_lt704 {ln size : UInt64} (hsz : size.toNat ≤ 704) (hln : ln.toNat ≤ size.toNat) (h1 : ¬ ln = size) :
    ln.toNat < 704 := by
  have : ln.toNat ≠ size.toNat := fun e => h1 (UInt64.toNat_inj.mp e)
  omega

/-- One more symbol keeps the index within the code's size. -/
theorem ln_succ_le {ln size : UInt64} (hsz : size.toNat ≤ 704) (hln : ln.toNat ≤ size.toNat) (h1 : ¬ ln = size) :
    (ln + 1).toNat ≤ size.toNat := by
  have : ln.toNat ≠ size.toNat := fun e => h1 (UInt64.toNat_inj.mp e)
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  omega

/-- A run that fits keeps the index within the code's size. -/
theorem ln_run_le {ln size x : UInt64} (he : ¬ size < ln + x) : (ln + x).toNat ≤ size.toNat :=
  Nat.le_of_not_lt fun e => he (UInt64.lt_iff_toNat_lt.mpr e)

/-- A repeat code `r` read, which makes the repeat count `new` from `old`, applied to the fields: `symsRep`'s plain case
(a run of zeros that fits), `none` for every other case. -/
@[inline] def symsRepPlain (size : UInt64) (pos : USize) (s : SymsS) (r : Rd) (new old : UInt64) :
    Option { s' : SymsS // s'.ln.toNat ≤ size.toNat } :=
  if he : size < s.ln + (new - old) then none
  else
    let len := if r.a = 16 then s.prevLen else 0
    if 32768 < s.symSum then none
    else if len = 0 then
      some ⟨
        { s with
          word := r.word, count := r.count, pos := pos, ln := s.ln + (new - old), repSym := r.a, repCount := new },
        ln_run_le he⟩
    else none

/-- `symsRep`'s plain case is `symsRepPlain`'s, written back. -/
theorem symsRep_plain {st : Hd} {pos : USize} {h : ∃ g p, HRel st g p} {ht : st.tag = .syms} {h1 : ¬ st.ln = st.size}
    {r : Rd} {new old : UInt64} {s' : { s' : SymsS // s'.ln.toNat ≤ st.size.toNat }}
    (hs' : symsRepPlain st.size pos (SymsS.of st) r new old = some s') :
    symsRep st pos h ht h1 r new old = SymsS.put st s'.1 := by
  unfold symsRepPlain at hs'
  unfold symsRep
  dsimp only [SymsS.of] at hs'
  by_cases he : st.size < st.ln + (new - old)
  · simp [he] at hs'
  · simp only [he, ↓reduceDIte] at hs' ⊢
    by_cases hlen : (if r.a = 16 then st.prevLen else 0) = 0
    · by_cases hov : 32768 < st.symSum
      · simp [hov] at hs'
      · simp only [hov, hlen, ↓reduceIte] at hs' ⊢
        cases hs'
        rfl
    · simp [hlen] at hs'

/-- A code length symbol `r` read at a code's lengths, applied to the fields: `symsOk`'s plain cases (a zero, a nonzero
length, a run of zeros), `none` for every other case. -/
@[inline] def symsPlainOk (size : UInt64) (hsz : size.toNat ≤ 704) (pos : USize) (s : SymsS)
    (hln : s.ln.toNat ≤ size.toNat) (hl1 : ¬ s.ln = size) (r : Rd) : Option { s' : SymsS // s'.ln.toNat ≤ size.toNat } :=
      if hlow : r.a < 16 then
        let sum := if r.a = 0 then s.symSum else s.symSum + ((32768 : UInt64) >>> r.a)
        if 32768 < sum then none
        else if r.a = 0 then
          some ⟨{ s with word := r.word, count := r.count, pos := pos, ln := s.ln + 1, repCount := 0, symSum := sum },
            ln_succ_le hsz hln hl1⟩
        else
          let old := getHead s.head s.headSz r.a (UInt64.lt_iff_toNat_lt.mp hlow)
          some ⟨
            { s with
              word := r.word, count := r.count, pos := pos
              head := setHead s.head s.headSz r.a (s.ln + 1) (UInt64.lt_iff_toNat_lt.mp hlow)
              next := setNext s.next s.nextSz s.ln old (ln_lt704 hsz hln hl1)
              headSz := setHead_size, nextSz := setNext_size
              ln := s.ln + 1, prevLen := r.a, repCount := 0, symSum := sum },
            ln_succ_le hsz hln hl1⟩
      else
        let mult : UInt64 := if r.a = 16 then 4 else 8
        let old := if s.repCount ≠ 0 ∧ s.repSym = r.a then s.repCount else 0
        let new := if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)
        symsRepPlain size pos s r new old

/-- One step at a code's lengths on its fields, the buffer `word`/`count` refilled and the position `pos`: the new
fields for `stepHSyms`'s plain cases (a zero, a nonzero length, a run of zeros), `none` for every other case. -/
@[inline] def symsPlain (clt : Tab) (size : UInt64) (hsz : size.toNat ≤ 704) (word count : UInt64) (pos : USize)
    (s : SymsS) (hln : s.ln.toNat ≤ size.toNat) : Option { s' : SymsS // s'.ln.toNat ≤ size.toNat } :=
  if s.symSum = 32768 then none
  else if hl1 : s.ln = size then none
  else
    let r := lenSymFast clt.t (USize.ofNat 0) clt.fits clt.h32 ⟨word, count⟩
    match r.status with
    | .ok => symsPlainOk size hsz pos s hln hl1 r
    | _ => none

/-- `symsOk`'s plain cases are `symsPlainOk`'s, written back. -/
theorem symsOk_plain {st : Hd} {pos : USize} {h : ∃ g p, HRel st g p} {ht : st.tag = .syms} {h1 : ¬ st.ln = st.size}
    {r : Rd} (hsz : st.size.toNat ≤ 704) (hln : st.ln.toNat ≤ st.size.toNat)
    {s' : { s' : SymsS // s'.ln.toNat ≤ st.size.toNat }}
    (hs' : symsPlainOk st.size hsz pos (SymsS.of st) hln h1 r = some s') :
    symsOk st pos h ht h1 r = SymsS.put st s'.1 := by
  unfold symsPlainOk at hs'
  unfold symsOk
  dsimp only [SymsS.of] at hs'
  by_cases hlow : r.a < 16
  · simp only [hlow, ↓reduceDIte] at hs' ⊢
    by_cases hz : r.a = 0
    · simp only [hz, ↓reduceIte] at hs' ⊢
      by_cases hov : 32768 < st.symSum
      · simp [hov] at hs'
      · simp only [hov, ↓reduceIte] at hs' ⊢
        cases hs'
        rfl
    · simp only [hz, ↓reduceIte] at hs' ⊢
      by_cases hov : 32768 < st.symSum + ((32768 : UInt64) >>> r.a)
      · simp [hov] at hs'
      · simp only [hov, ↓reduceIte] at hs' ⊢
        cases hs'
        rfl
  · simp only [hlow, ↓reduceDIte] at hs' ⊢
    exact symsRep_plain hs'

/-- A plain step at a code's lengths is `stepH`: the same refill and read, and the fields it writes are those `stepH`'s
step writes into the state. -/
theorem stepH_symsPlain {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} {h : HIn st}
    {hp : pos.toNat ≤ stop.toNat} (ht : st.tag = .syms) (hsz : st.size.toNat ≤ 704) (hln : st.ln.toNat ≤ st.size.toNat)
    {s' : { s' : SymsS // s'.ln.toNat ≤ st.size.toNat }}
    (hs' : symsPlain st.clt st.size hsz (refill st.word st.count a pos stop hs hp).word
      (refill st.word st.count a pos stop hs hp).count (refill st.word st.count a pos stop hs hp).pos (SymsS.of st) hln =
        some s') :
    stepH a stop hs st pos h hp = SymsS.put st s'.1 := by
  unfold stepH
  dsimp only [refillH]
  rw [stepAtH_syms (by exact ht)]
  unfold stepHSyms symsPlain at *
  dsimp only [SymsS.of] at hs' ⊢
  split
  · rename_i h0
    simp [h0] at hs'
  rename_i h0
  split
  · rename_i h1
    simp [h1] at hs'
  rename_i h1
  simp only [h0, h1, ↓reduceIte, ↓reduceDIte] at hs'
  split
  · rename_i hq
    simp [hq] at hs'
  · rename_i hq
    simp [hq] at hs'
  rename_i hq
  simp only [hq] at hs'
  exact symsOk_plain
    (st := { st with word := (refill st.word st.count a pos stop hs hp).word
                     count := (refill st.word st.count a pos stop hs hp).count })
    hsz hln hs'

end Brotli.Decoder
