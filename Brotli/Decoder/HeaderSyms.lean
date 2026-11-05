module

public import Brotli.Decoder.HeaderRest
public import Brotli.Decoder.Rest
public import Brotli.Decoder.HeaderStep
public import Brotli.Decoder.HeaderCode

@[expose] public section

/-!
# A prefix code's lengths

The place reading a complex prefix code's lengths, one code length symbol at a time.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Reads length `l`'s link in `head`. -/
@[inline] def getHead (t : ByteArray) (ht : t.size = 32) (l : UInt64) (hl : l.toNat < 16) : UInt64 :=
  getSlot t l (by omega) (by omega)

theorem getHead_toNat {t : ByteArray} {ht : t.size = 32} {l : UInt64} {hl : l.toNat < 16} :
    (getHead t ht l hl).toNat = u16At t l.toNat := by
  rw [getHead, getSlot_toNat, slotNum_eq_u16At]

/-- Links the symbols from `i` up to `e` in `next`, each to the one before it. -/
def linkRun (t : ByteArray) (ht : t.size = 1408) (i e : UInt64) (he : e.toNat ≤ 704) : ByteArray :=
  if hi : i < e then
    linkRun (setNext t ht i i (by have := UInt64.lt_iff_toNat_lt.mp hi; omega)) setNext_size (i + 1) e he
  else t
termination_by e.toNat - i.toNat
decreasing_by
  have h1 := UInt64.lt_iff_toNat_lt.mp hi
  have h2 : (i + 1).toNat = i.toNat + 1 := u64_succ (by omega)
  omega

theorem linkRun_spec {e : UInt64} {he : e.toNat ≤ 704} : ∀ (N : Nat) (t : ByteArray) (ht : t.size = 1408) (i : UInt64),
    e.toNat - i.toNat = N → (linkRun t ht i e he).size = 1408 ∧
      ∀ j, u16At (linkRun t ht i e he) j = if i.toNat ≤ j ∧ j < e.toNat then j else u16At t j := by
  intro N
  induction N with
  | zero =>
    intro t ht i hN
    have hi : ¬ i < e := fun h => by have := UInt64.lt_iff_toNat_lt.mp h; omega
    rw [linkRun, dite_eq_right hi]
    exact ⟨ht, fun j => by rw [ite_eq_right (by omega)]⟩
  | succ N ih =>
    intro t ht i hN
    have hi : i < e := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have hi' := UInt64.lt_iff_toNat_lt.mp hi
    have h1 : (i + 1).toNat = i.toNat + 1 := u64_succ (by omega)
    rw [linkRun, dite_eq_left hi]
    obtain ⟨s, f⟩ := ih _ setNext_size (i + 1) (by omega)
    refine ⟨s, fun j => ?_⟩
    rw [f j, u16At_setNext, h1]
    by_cases hj : j = i.toNat
    · subst hj
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by omega)]
      omega
    · rw [ite_eq_right hj]
      by_cases hin : i.toNat + 1 ≤ j ∧ j < e.toNat
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

theorem linkRun_size {t : ByteArray} {ht : t.size = 1408} {i e : UInt64} {he : e.toNat ≤ 704} : (linkRun t ht i e he).size = 1408 :=
  (linkRun_spec _ t ht i rfl).1

/-- One more symbol `sym`, nonzero, whose list's last symbol was linked from `old`: it goes in front of its length's
list. -/
@[inline] def pushSym (st : Hd) (r : Rd) (pos : USize) (sym sum : UInt64) (hl : sym.toNat < 16) (hn : st.ln.toNat < 704)
    (old : UInt64) : Hd :=
  { st with
    word := r.word, count := r.count, pos := pos, status := .next
    head := setHead st.head st.headSz sym (st.ln + 1) hl, next := setNext st.next st.nextSz st.ln old hn
    headSz := setHead_size, nextSz := setNext_size, ln := st.ln + 1, prevLen := sym, repCount := 0, symSum := sum }

/-- A run of nonzero length `len` up to symbol `e`, whose list's last symbol was linked from `old`: the run goes in front
of its length's list, each symbol linked to the one before it. -/
@[inline] def pushRunAt (st : Hd) (r : Rd) (pos : USize) (len e new sum : UInt64) (hl : len.toNat < 16) (hn : st.ln.toNat < 704)
    (he : e.toNat ≤ 704) (old : UInt64) : Hd :=
  { st with
    word := r.word, count := r.count, pos := pos, status := .next
    head := setHead st.head st.headSz len e hl, next := linkRun (setNext st.next st.nextSz st.ln old hn) setNext_size (st.ln + 1) e he
    headSz := setHead_size, nextSz := linkRun_size, ln := e, repSym := r.a, repCount := new, symSum := sum }

/-- What `fillVals` needs for its writes to stay in the array. -/
def FillPre (t : ByteArray) (i n : UInt64) : Prop := i.toNat + n.toNat < 2 ^ 32 ∧ i.toNat + n.toNat ≤ t.size

theorem FillPre.at {t : ByteArray} {i n : UInt64} (h : FillPre t i n) (hn : ¬ n = 0) : i.toUSize.toNat < t.size := by
  obtain ⟨h1, h2⟩ := h
  have : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  rw [word_toUSize (by omega)]
  omega

theorem FillPre.next {t : ByteArray} {i n : UInt64} (h : FillPre t i n) (hn : ¬ n = 0) {t' : ByteArray} (hs : t'.size = t.size) :
    FillPre t' (i + 1) (n - 1) := by
  obtain ⟨h1, h2⟩ := h
  have : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have hn1 : (n - 1).toNat = n.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨by rw [hi1, hn1]; omega, by rw [hi1, hn1, hs]; omega⟩

/-- Writes `v` into `n` bytes from `i`, which are in the array: a context map's values. -/
def fillVals (t : ByteArray) (i n : UInt64) (v : UInt8) (h : FillPre t i n) : ByteArray :=
  if hn : n = 0 then t else fillVals (t.uset i.toUSize v (h.at hn)) (i + 1) (n - 1) v (h.next hn (size_uset' _ _ _ _))
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem fillVals_spec (v : UInt8) : ∀ (N : Nat) (t : ByteArray) (i n : UInt64) (h : FillPre t i n), n.toNat = N →
    (fillVals t i n v h).size = t.size ∧ ∀ j, (fillVals t i n v h).data[j]?.getD 0 =
      if i.toNat ≤ j ∧ j < i.toNat + N then v else t.data[j]?.getD 0 := by
  intro N
  induction N with
  | zero =>
    intro t i n h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [fillVals, dite_eq_left hz]
    refine ⟨rfl, fun j => ?_⟩
    rw [ite_eq_right (by omega)]
  | succ N ih =>
    intro t i n h hn
    obtain ⟨h32, hle⟩ := id h
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    rw [fillVals, dite_eq_right hz]
    have hsz := size_uset' t i.toUSize v (h.at hz)
    obtain ⟨h1, h2⟩ := ih (t.uset i.toUSize v (h.at hz)) (i + 1) (n - 1) (h.next hz hsz) hn1
    refine ⟨by rw [h1, hsz], fun j => ?_⟩
    rw [h2 j, hi1]
    by_cases he : j = i.toNat
    · subst he
      rw [ite_eq_right (by omega), ite_eq_left (by omega)]
      have := uset_get_same (t := t) (i := i.toUSize) (v := v) (h.at hz)
      rwa [hus] at this
    · have e : (t.uset i.toUSize v (h.at hz)).data[j]? = t.data[j]? := uset_get_ne (h.at hz) (by rw [hus]; exact he)
      rw [e]
      by_cases hin : i.toNat + 1 ≤ j ∧ j < i.toNat + 1 + N
      · rw [ite_eq_left hin, ite_eq_left (by omega)]
      · rw [ite_eq_right hin, ite_eq_right (by omega)]

section
variable {α : Type} (K : HK α)

/-- One more code length symbol. -/
theorem hrest_syms_step (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hlt : ls.lens.length < size) (h : lengthSum ls.lens ≠ 32768) :
    hrest K g (.syms o size clc ls) bs = lenSym clc bs >>= fun p =>
      if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else hrest K g (.syms o size clc (applyCodeLength ls p.1.1 p.1.2)) p.2 := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_step bs hlt h]
  cases lenSym clc bs with
  | none => rfl
  | some p =>
    show ((if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else symsFrom size clc (applyCodeLength ls p.1.1 p.1.2) p.2) >>= _) =
      (if size < (applyCodeLength ls p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens then none
      else hrest K g (.syms o size clc (applyCodeLength ls p.1.1 p.1.2)) p.2)
    by_cases h1 : size < (applyCodeLength ls p.1.1 p.1.2).lens.length
    · rw [ite_eq_left h1, ite_eq_left h1]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : 32768 < lengthSum (applyCodeLength ls p.1.1 p.1.2).lens
      · rw [ite_eq_left h2, ite_eq_left h2]
        rfl
      · rw [ite_eq_right h2, ite_eq_right h2]
        rfl

/-- The code lengths are done when their space is used up. -/
theorem hrest_syms_done (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hle : ls.lens.length ≤ size) (h : lengthSum ls.lens = 32768) :
    hrest K g (.syms o size clc ls) bs = ownerK K g o (.canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0)) bs := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_done bs hle h]
  rfl

/-- With all the lengths read and space left, the code is invalid. -/
theorem hrest_syms_full (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (ls : LengthState) (bs : List Bool)
    (hlen : ls.lens.length = size) (h : lengthSum ls.lens ≠ 32768) : hrest K g (.syms o size clc ls) bs = none := by
  show (symsFrom size clc ls bs >>= _) = _
  rw [symsFrom_full bs h hlen]
  rfl

end

private theorem lenSym_bounds {clc : PrefixCode} {bs r : List Bool} {s e : Nat} (hs : clc.Symbols 18)
    (h : lenSym clc bs = some ((s, e), r)) : s < 18 ∧ e < 8 := by
  unfold lenSym at h
  cases hd : decodeSymbol clc bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, b1⟩ := p
    rw [hd] at h
    change (readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b1 >>= _) = _ at h
    have hlt := decodeSymbol_lt hs hd
    cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b1 with
    | none => rw [hx] at h; cases h
    | some q =>
      obtain ⟨x, b2⟩ := q
      rw [hx] at h
      have h' : some ((sym, x), b2) = some ((s, e), r) := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      have hxl := readInt_lt _ _ _ _ hx
      obtain ⟨⟨e1, e2⟩, _⟩ := h'
      subst e1
      subst e2
      refine ⟨hlt, ?_⟩
      have hp : 2 ^ (if sym = 16 then 2 else if sym = 17 then 3 else 0) ≤ 2 ^ 3 := by
        refine Nat.pow_le_pow_right (by decide) ?_
        split
        · omega
        · split <;> omega
      have h8 : (2 : Nat) ^ 3 = 8 := rfl
      omega

/-- The sum of a run of one code length. -/
private theorem lengthSum_replicate (n l : Nat) : lengthSum (List.replicate n l) = n * (if l = 0 then 0 else 32768 >>> l) := by
  simp only [lengthSum, List.map_replicate, List.sum_replicate_nat]

/-- A state at a code's lengths stands for a place there. -/
theorem syms_ex {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) :
    ∃ g o size clc ls, HRel st g (.syms o size clc ls) := by
  obtain ⟨g, p, hr⟩ := h
  cases p with
  | syms o size clc ls => exact ⟨g, o, size, clc, ls, hr⟩
  | np => exact absurd (hr.2.2.symm.trans ht) (fun e => HTag.noConfusion e)
  | _ => exact absurd (hr.2.2.1.symm.trans ht) (fun e => HTag.noConfusion e)

/-- Lengths that fill the code space, with zeros after them, are the code that was read. -/
theorem syms_for {st : Hd} {size : Nat} {ls : LengthState} (hs : SizeOk st size) (hy : ListsIs st.head st.next ls.lens)
    (hle : ls.lens.length ≤ size) (hsmall : ∀ l ∈ ls.lens, l ≤ 15) (hsum : lengthSum ls.lens = 32768) :
    TableFor st.size st.head st.next false 0 (.canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0)) := by
  obtain ⟨hs1, _, hs3⟩ := hs
  have hlen : (ls.lens ++ List.replicate (size - ls.lens.length) 0).length = size := by simp; omega
  refine ⟨by omega, fun e => Bool.noConfusion e, fun _ => ⟨_, rfl, by rw [hlen, hs1], hy.zeros _⟩,
    by rw [st.headSz]; decide, by rw [st.nextSz]; decide, ⟨?_, ?_⟩, by rw [hs1]; exact hlen⟩
  · intro l hl
    rcases List.mem_append.mp hl with h | h
    · exact hsmall l h
    · rw [(List.mem_replicate.mp h).2]
      omega
  · rw [lengthSum_append, lengthSum_replicate_zero, hsum]

/-- Lengths that fill the code space are a code that was read. -/
theorem syms_args {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (h0 : st.symSum = 32768) :
    TableArgs st.size st.head st.next false 0 := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  have hs : SizeOk st size := hrel.2.2.2.1
  have hy : SymRel st size clc ls := hrel.2.2.2.2.2
  have hsum : lengthSum ls.lens = 32768 := by
    rw [← hy.sumOk, h0]
    rfl
  exact ⟨_, syms_for hs hy.lists hy.le hy.small hsum⟩

/-- Bounds the reading of a code's lengths needs: the next symbol, when there is one, is below 704. -/
theorem syms_lnLt {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (h1 : ¬ st.ln = st.size) : st.ln.toNat < 704 := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  have hs : SizeOk st size := hrel.2.2.2.1
  have hy : SymRel st size clc ls := hrel.2.2.2.2.2
  have := hy.ln
  have := hy.le
  have := hs.1
  have := hs.2.2
  have : st.ln.toNat ≠ st.size.toNat := fun e => h1 (UInt64.toNat_inj.mp e)
  omega

/-- A repeat's length is below 16. -/
theorem syms_lenLt {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (sym : UInt64) :
    (if sym = 16 then st.prevLen else 0).toNat < 16 := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  have hy : SymRel st size clc ls := hrel.2.2.2.2.2
  have := hy.prev
  have := hy.prevOk
  split
  · omega
  · decide

/-- A run that fits the alphabet ends at 704 or below. -/
theorem syms_eLe {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) {e : UInt64} (he : ¬ st.size < e) : e.toNat ≤ 704 := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  have hs : SizeOk st size := hrel.2.2.2.1
  have := hs.1
  have := hs.2.2
  have : ¬ st.size.toNat < e.toNat := fun e' => he (UInt64.lt_iff_toNat_lt.mpr e')
  omega

/-- A state at a code's lengths has what `installTable` needs. -/
theorem syms_install {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) : InstallOk st.role st.idx st.fill := by
  obtain ⟨g, o, size, clc, ls, hrel⟩ := syms_ex h ht
  exact hrel.2.2.2.2.1.install

/-- A run of the repeat's length, nonzero, up to symbol `e`. -/
@[inline] def pushRun (st : Hd) (r : Rd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (e new sum : UInt64)
    (hn : st.ln.toNat < 704) (he : e.toNat ≤ 704) : Hd :=
  pushRunAt st r pos (if r.a = 16 then st.prevLen else 0) e new sum (syms_lenLt h ht r.a) hn he
    (getHead st.head st.headSz (if r.a = 16 then st.prevLen else 0) (syms_lenLt h ht r.a))

/-- A repeat code `r` read, which makes the repeat count `new` from `old`, applied to a code's lengths. -/
@[inline] def symsRep (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (h1 : ¬ st.ln = st.size) (r : Rd)
    (new old : UInt64) : Hd :=
  if he : st.size < st.ln + (new - old) then markH st pos .bad
  else
    let len := if r.a = 16 then st.prevLen else 0
    let sum := if len = 0 then st.symSum else st.symSum + (new - old) * ((32768 : UInt64) >>> len)
    if 32768 < sum then markH st pos .bad
    else if len = 0 then
      { st with
        word := r.word, count := r.count, pos := pos, status := .next, ln := st.ln + (new - old), repSym := r.a
        repCount := new, symSum := sum }
    else
      pushRun st r pos h ht (st.ln + (new - old)) new sum (syms_lnLt h ht h1) (syms_eLe h ht he)

/-- A code length symbol `r` read, applied to a code's lengths. -/
@[inline] def symsOk (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) (h1 : ¬ st.ln = st.size) (r : Rd) : Hd :=
      if hlow : r.a < 16 then
        let sum := if r.a = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> r.a)
        if 32768 < sum then markH st pos .bad
        else if r.a = 0 then { st with word := r.word, count := r.count, pos := pos, status := .next, ln := st.ln + 1, repCount := 0, symSum := sum }
        else
          pushSym st r pos r.a sum (UInt64.lt_iff_toNat_lt.mp hlow) (syms_lnLt h ht h1)
            (getHead st.head st.headSz r.a (UInt64.lt_iff_toNat_lt.mp hlow))
      else
        let mult : UInt64 := if r.a = 16 then 4 else 8
        let old := if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0
        let new := if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)
        symsRep st pos h ht h1 r new old

/-- The place reading a code's lengths. -/
def stepHSyms (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .syms) : Hd :=
  if h0 : st.symSum = 32768 then
    tableDone { st with pos := pos, status := .next } false 0 (syms_args (st := st) h ht h0) (syms_install (st := st) h ht)
      (hrel_arena (st := st) h)
  else if h1 : st.ln = st.size then markH st pos .bad
  else
    let r := lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok => symsOk st pos h ht h1 r

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHSyms_ok {o : Owner} {size : Nat} {clc : PrefixCode} {ls : LengthState} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.syms o size clc ls)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop)
    (hb : st.d.arena.size + budH g (.syms o size clc ls) ≤ st.d.arenaCap.toNat) {hH : ∃ g p, HRel st g p} {hT : st.tag = .syms} :
    HStepOk K a stop g (.syms o size clc ls) st pos (stepHSyms st pos hH hT) := by
  obtain ⟨hw, hu, ht, hs, ho, hy⟩ := hrel
  have hrel : HRel st g (.syms o size clc ls) := ⟨hw, hu, ht, hs, ho, hy⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hs : SizeOk st size := ⟨hs1, hs2, hs3⟩
  have hlenLe := hy.le
  unfold stepHSyms
  by_cases h0 : st.symSum = 32768
  · rw [dite_eq_left h0]
    have hsum : lengthSum ls.lens = 32768 := by
      rw [← hy.sumOk, h0]
      rfl
    have hdone := tableDone_ok K (st := { st with pos := pos, status := .next }) (c := .canonical (ls.lens ++ List.replicate (size - ls.lens.length) 0))
      (single := false) (sym := 0) hw hu hs ho (syms_for (st := { st with pos := pos, status := .next }) hs hy.lists hlenLe hy.small hsum) hb
      (ha := syms_args (st := st) hH hT h0) (hi := syms_install (st := st) hH hT) (har := hrel_arena (st := st) hH)
    exact hdone.toStep rfl hp rfl (fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩)
      (fun F => hrest_syms_done K g o size clc ls _ hlenLe hsum) (fun F => hStep_syms_done _ hlenLe hsum)
  rw [dite_eq_right h0]
  have hsumNe : lengthSum ls.lens ≠ 32768 := by
    rw [← hy.sumOk]
    exact fun e => h0 (UInt64.toNat_inj.mp e)
  by_cases h1 : st.ln = st.size
  · rw [dite_eq_left h1]
    have hlen : ls.lens.length = size := by
      rw [← hy.ln, h1, hs1]
    exact HStepOk.ofBad rfl (fun F => hrest_syms_full K g o size clc ls _ hlen hsumNe)
  rw [dite_eq_right h1]
  have hlenLt : ls.lens.length < size := by
    have : ls.lens.length ≠ size := by
      rw [← hy.ln, ← hs1]
      exact fun e => h1 (UInt64.toNat_inj.mp e)
    omega
  have R := lenSymFast_ok (t := st.clt.t) (base := USize.ofNat 0) (hfit := st.clt.fits) (h32 := st.clt.h32) hw hy.table hy.complete
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.syms o size clc ls)) (N := fun v b =>
    if size < (applyCodeLength ls v.1 v.2).lens.length then none
    else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then none
    else hrest K g (.syms o size clc (applyCodeLength ls v.1 v.2)) b) (fun bs => hrest_syms_step K g o size clc ls bs hlenLt hsumNe)
  have hval := R.ok
  have hsh0 := R.short
  dsimp only
  generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval hsh0
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    exact HStepOk.ofShortRead (X := 18) hrel hfull (by omega) h3 h4
      (by rw [hStep_syms_step _ hlenLt hsumNe]; exact readIn_short h5 (by rw [held_len]; exact h3))
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  | ok =>
    dsimp only
    unfold symsOk
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨hs18, he8⟩ := lenSym_bounds hy.symbols ((hval hsr).2 [])
    have hsize32 : size < 2 ^ 32 := by omega
    have hln : st.ln.toNat = ls.lens.length := hy.ln
    by_cases hlow : r.a < 16
    · rw [dite_eq_left hlow]
      have hlow' : r.a.toNat < 16 := UInt64.lt_iff_toNat_lt.mp hlow
      have happly : applyCodeLength ls r.a.toNat r.b.toNat = ⟨ls.lens ++ [r.a.toNat], if r.a.toNat = 0 then ls.prev else r.a.toNat, none⟩ := by
        simp [applyCodeLength, hlow']
      have hsumP : lengthSum (ls.lens ++ [r.a.toNat]) = lengthSum ls.lens + (if r.a.toNat = 0 then 0 else 32768 >>> r.a.toNat) := by
        rw [lengthSum_append]
        simp [lengthSum]
      have hshLe : 32768 >>> r.a.toNat ≤ 32768 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_le_self _ _
      have hsumU : (if r.a = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> r.a)).toNat = lengthSum (ls.lens ++ [r.a.toNat]) := by
        rw [hsumP, ← hy.sumOk]
        by_cases hz : r.a = 0
        · have hz' : r.a.toNat = 0 := by rw [hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz']
          rfl
        · have hz' : ¬ r.a.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
          rw [ite_eq_right hz, ite_eq_right hz', UInt64.toNat_add, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega)]
          have hsl := hy.sumOk
          have hsl2 := hy.sumLe
          exact Nat.mod_eq_of_lt (by
            show st.symSum.toNat + 32768 >>> r.a.toNat < _
            omega)
      generalize (if r.a = 0 then st.symSum else st.symSum + ((32768 : UInt64) >>> r.a)) = sum at hsumU ⊢
      have hlt1 : ¬ size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
        rw [happly]
        simp
        omega
      by_cases hbig : 32768 < sum
      · rw [ite_eq_left hbig]
        have hbig' : 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly, ← hsumU]
          exact UInt64.lt_iff_toNat_lt.mp hbig
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hlt1, hbig', ↓reduceIte]
      · rw [ite_eq_right hbig]
        have hbig' : ¬ 32768 < lengthSum (ls.lens ++ [r.a.toNat]) := by
          rw [← hsumU]
          exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
        have hbig2 : ¬ 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          exact hbig'
        have hln1 : (st.ln + 1).toNat = ls.lens.length + 1 := by
          rw [UInt64.toNat_add, hln, show (1 : UInt64).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        have hgrow : size + 1 - (applyCodeLength ls r.a.toNat r.b.toNat).lens.length < size + 1 - ls.lens.length := by
          rw [happly]
          simp only [List.length_append, List.length_singleton]
          omega
        have hsmallP : ∀ l ∈ ls.lens ++ [r.a.toNat], l ≤ 15 := by
          intro l hl
          rcases List.mem_append.mp hl with h | h
          · exact hy.small l h
          · rw [List.mem_singleton.mp h]
            omega
        by_cases hz : r.a = 0
        · rw [ite_eq_left hz]
          have hz' : r.a.toNat = 0 := by rw [hz]; rfl
          have hnew : SymRel { st with
              word := r.word, count := r.count, pos := pos, status := .next, ln := st.ln + 1, repCount := 0, symSum := sum }
              size clc (applyCodeLength ls r.a.toNat r.b.toNat) := by
            rw [happly]
            exact {
              table := hy.table
              complete := hy.complete
              symbols := hy.symbols
              ln := by
                show (st.ln + 1).toNat = _
                rw [hln1]
                simp
              le := by
                simp
                omega
              lists := by
                show ListsIs st.head st.next (ls.lens ++ [r.a.toNat])
                rw [hz']
                exact hy.lists.zero
              small := hsmallP
              prev := by
                show st.prevLen.toNat = (if r.a.toNat = 0 then ls.prev else r.a.toNat)
                rw [ite_eq_left hz']
                exact hy.prev
              prevOk := by
                have := hy.prevOk
                show 1 ≤ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ∧ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ≤ 15
                split <;> omega
              rep := rfl
              sumOk := hsumU
              sumLe := Nat.le_of_not_lt hbig' }
          refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
            (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hgrow⟩⟩)
            (hm := HMove.ofD rfl (fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase,
              h.work⟩) (Nat.le_refl _)) rfl
            ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
          · rw [avail_mk, hN]
            simp only [hlt1, hbig2, ↓reduceIte]
            rfl
          · rw [avail_mk, hStep_syms_step _ hlenLt hsumNe, readIn_some ((hval hsr).2 _)]
            simp only [hlt1, hbig2, ↓reduceIte]
            rfl
        · rw [ite_eq_right hz]
          have hz' : ¬ r.a.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
          have hold : (getHead st.head st.headSz r.a hlow').toNat = u16At st.head r.a.toNat := getHead_toNat
          have hnew : SymRel (pushSym st r pos r.a sum hlow' (syms_lnLt hH hT h1) (getHead st.head st.headSz r.a hlow')) size clc
              (applyCodeLength ls r.a.toNat r.b.toNat) := by
            rw [happly]
            exact {
              table := hy.table
              complete := hy.complete
              symbols := hy.symbols
              ln := by
                show (st.ln + 1).toNat = _
                rw [hln1]
                simp
              le := by
                simp
                omega
              lists := ListsIs.run (L := ls.lens) (l := r.a.toNat) (n := 1) hy.lists
                (head' := setHead st.head st.headSz r.a (st.ln + 1) hlow')
                (next' := setNext st.next st.nextSz st.ln (getHead st.head st.headSz r.a hlow') (syms_lnLt hH hT h1))
                (by rw [setNext_size]; omega)
                (fun j hj => by rw [u16At_setNext, ite_eq_right (by omega)])
                (fun j hj1 hj2 => by
                  rw [u16At_setNext, ite_eq_left (show j = st.ln.toNat by omega), ite_eq_left (show j = ls.lens.length by omega), hold,
                    Nat.mod_eq_of_lt (u16At_lt _ _)])
                (fun j hj => by rw [u16At_setHead, ite_eq_right hj])
                (by
                  rw [u16At_setHead, ite_eq_left rfl, ite_eq_right (by decide), hln1]
                  exact Nat.mod_eq_of_lt (by omega))
                (by rw [setHead_size]; omega)
              small := hsmallP
              prev := by
                show r.a.toNat = (if r.a.toNat = 0 then ls.prev else r.a.toNat)
                rw [ite_eq_right hz']
              prevOk := by
                show 1 ≤ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ∧ (if r.a.toNat = 0 then ls.prev else r.a.toNat) ≤ 15
                rw [ite_eq_right hz']
                omega
              rep := rfl
              sumOk := hsumU
              sumLe := Nat.le_of_not_lt hbig' }
          refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
            (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hgrow⟩⟩)
            (hm := HMove.ofD rfl (fun h => ⟨h.fill, ⟨Nat.le_of_eq (Hd.headSz _), Nat.le_of_eq (Hd.nextSz _)⟩, h.clLens, h.clt, h.mapT, h.modes,
              h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩) (Nat.le_refl _)) rfl
            ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
          · rw [avail_mk, hN]
            simp only [hlt1, hbig2, ↓reduceIte]
            rfl
          · rw [avail_mk, hStep_syms_step _ hlenLt hsumNe, readIn_some ((hval hsr).2 _)]
            simp only [hlt1, hbig2, ↓reduceIte]
            rfl
    · rw [dite_eq_right hlow]
      have hhigh : ¬ r.a.toNat < 16 := fun h => hlow (UInt64.lt_iff_toNat_lt.mpr h)
      have hprevOk := hy.prevOk
      generalize hL : (if r.a.toNat = 16 then ls.prev else 0) = Ln
      generalize hM : (if r.a.toNat = 16 then 4 else 8) = Mn
      generalize hO : (match ls.rep with
        | some (s, count) => if s = r.a.toNat then count else 0
        | none => 0) = On
      have hLU : (if r.a = 16 then st.prevLen else 0).toNat = Ln := by
        rw [← hL]
        by_cases h16 : r.a = 16
        · rw [ite_eq_left h16, ite_eq_left (show r.a.toNat = 16 by rw [h16]; rfl)]
          exact hy.prev
        · rw [ite_eq_right h16, ite_eq_right (show ¬ r.a.toNat = 16 from fun e => h16 (UInt64.toNat_inj.mp e))]
          rfl
      have hMU : (if r.a = 16 then (4 : UInt64) else 8).toNat = Mn := by
        rw [← hM]
        by_cases h16 : r.a = 16
        · rw [ite_eq_left h16, ite_eq_left (show r.a.toNat = 16 by rw [h16]; rfl)]
          rfl
        · rw [ite_eq_right h16, ite_eq_right (show ¬ r.a.toNat = 16 from fun e => h16 (UInt64.toNat_inj.mp e))]
          rfl
      have hMc : Mn = 4 ∨ Mn = 8 := by
        rw [← hM]
        split
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hLle : Ln ≤ 15 := by
        rw [← hL]
        split <;> omega
      have hOU : (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0).toNat = On ∧ On ≤ ls.lens.length ∧ (On = 0 ∨ 3 ≤ On) := by
        have hr := hy.rep
        rw [← hO]
        cases hrep : ls.rep with
        | none =>
          rw [hrep] at hr
          have hz : st.repCount = 0 := UInt64.toNat_inj.mp hr
          rw [ite_eq_right (fun h => h.1 hz)]
          exact ⟨rfl, Nat.zero_le _, Or.inl rfl⟩
        | some q =>
          obtain ⟨t, c⟩ := q
          rw [hrep] at hr
          obtain ⟨h1', h2', h3', h4'⟩ := hr
          show _ = (if t = r.a.toNat then c else 0) ∧ (if t = r.a.toNat then c else 0) ≤ _ ∧ ((if t = r.a.toNat then c else 0) = 0 ∨ 3 ≤ (if t = r.a.toNat then c else 0))
          by_cases he : t = r.a.toNat
          · have hne : st.repCount ≠ 0 := by
              intro e
              rw [e] at h2'
              have h00 : (0 : UInt64).toNat = 0 := rfl
              omega
            have hc1 : st.repCount ≠ 0 ∧ st.repSym = r.a := ⟨hne, UInt64.toNat_inj.mp (by rw [h1', he])⟩
            rw [ite_eq_left hc1, ite_eq_left he]
            exact ⟨h2', h4', Or.inr h3'⟩
          · have hc1 : ¬ (st.repCount ≠ 0 ∧ st.repSym = r.a) := fun h => he (by rw [← h1', h.2])
            rw [ite_eq_right hc1, ite_eq_right he]
            exact ⟨rfl, Nat.zero_le _, Or.inl rfl⟩
      obtain ⟨hOu, hOle, hO3⟩ := hOU
      generalize hNn : (if On = 0 then 3 + r.b.toNat else Mn * (On - 2) + (3 + r.b.toNat)) = Nn
      have hgrow : On < Nn ∧ Nn ≤ 8 * 704 + 10 ∧ 3 ≤ Nn := by
        rw [← hNn]
        rcases hO3 with h | h
        · rw [ite_eq_left h]
          omega
        · rw [ite_eq_right (by omega)]
          rcases hMc with hm | hm <;> rw [hm] <;> omega
      have happly : applyCodeLength ls r.a.toNat r.b.toNat = ⟨ls.lens ++ List.replicate (Nn - On) Ln, ls.prev, some (r.a.toNat, Nn)⟩ := by
        subst hL hM hO hNn
        simp only [applyCodeLength, hhigh, ↓reduceIte]
        rfl
      have hNU : (if (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = 0 then 3 + r.b
          else (if r.a = 16 then (4 : UInt64) else 8) * ((if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) - 2) + (3 + r.b)).toNat = Nn := by
        generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hOu
        generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hMU
        rw [← hNn]
        have h3b : (3 + r.b).toNat = 3 + r.b.toNat := by
          rw [UInt64.toNat_add, show (3 : UInt64).toNat = 3 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        by_cases hz : old = 0
        · have hz' : On = 0 := by rw [← hOu, hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz', h3b]
        · have hz' : ¬ On = 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [hOu, e]; rfl))
          have h3O : 3 ≤ On := by omega
          rw [ite_eq_right hz, ite_eq_right hz']
          have hsub : (old - 2).toNat = On - 2 := by
            rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hOu, show (2 : UInt64).toNat = 2 from rfl]; omega)), hOu]
            rfl
          have hmul : (mult * (old - 2)).toNat = Mn * (On - 2) := by
            rw [UInt64.toNat_mul, hMU, hsub]
            refine Nat.mod_eq_of_lt ?_
            rcases hMc with hm | hm <;> rw [hm] <;> omega
          rw [UInt64.toNat_add, hmul, h3b]
          refine Nat.mod_eq_of_lt ?_
          rcases hMc with hm | hm <;> rw [hm] <;> omega
      generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hOu hNU ⊢
      generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hNU ⊢
      generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at hNU ⊢
      unfold symsRep
      dsimp only
      have hdU : (new - old).toNat = Nn - On := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hNU, hOu]
      have hln2 : (st.ln + (new - old)).toNat = ls.lens.length + (Nn - On) := by
        rw [UInt64.toNat_add, hln, hdU]
        exact Nat.mod_eq_of_lt (by omega)
      have hlen2 : (ls.lens ++ List.replicate (Nn - On) Ln).length = ls.lens.length + (Nn - On) := by simp
      by_cases hover : st.size < st.ln + (new - old)
      · rw [dite_eq_left hover]
        have hover' : size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
          rw [happly]
          show size < (ls.lens ++ List.replicate (Nn - On) Ln).length
          rw [hlen2, ← hln2, ← hs1]
          exact UInt64.lt_iff_toNat_lt.mp hover
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hover', ↓reduceIte]
      rw [dite_eq_right hover]
      have hover' : ¬ size < (applyCodeLength ls r.a.toNat r.b.toNat).lens.length := by
        rw [happly]
        show ¬ size < (ls.lens ++ List.replicate (Nn - On) Ln).length
        rw [hlen2, ← hln2, ← hs1]
        exact fun e => hover (UInt64.lt_iff_toNat_lt.mpr e)
      have hroom : ls.lens.length + (Nn - On) ≤ size := by
        rw [happly] at hover'
        have : ¬ size < (ls.lens ++ List.replicate (Nn - On) Ln).length := hover'
        rw [hlen2] at this
        omega
      have hsumP : lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) = lengthSum ls.lens + (Nn - On) * (if Ln = 0 then 0 else 32768 >>> Ln) := by
        rw [lengthSum_append, lengthSum_replicate]
      have hsumU : (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
          else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))).toNat =
          lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) := by
        generalize (if r.a = 16 then st.prevLen else 0) = lenU at hLU
        rw [hsumP, ← hy.sumOk]
        by_cases hz : lenU = 0
        · have hz' : Ln = 0 := by rw [← hLU, hz]; rfl
          rw [ite_eq_left hz, ite_eq_left hz']
          simp
        · have hz' : ¬ Ln = 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [hLU, e]; rfl))
          rw [ite_eq_right hz, ite_eq_right hz']
          have hsh : ((32768 : UInt64) >>> lenU).toNat = 32768 >>> Ln := by
            rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show lenU.toNat < 64 by omega), hLU]
            rfl
          have hshLe : 32768 >>> Ln ≤ 32768 := by
            rw [Nat.shiftRight_eq_div_pow]
            exact Nat.div_le_self _ _
          have hprod : (Nn - On) * (32768 >>> Ln) ≤ 704 * 32768 := Nat.mul_le_mul (by omega) hshLe
          have hmul : ((new - old) * ((32768 : UInt64) >>> lenU)).toNat = (Nn - On) * (32768 >>> Ln) := by
            rw [UInt64.toNat_mul, hdU, hsh]
            exact Nat.mod_eq_of_lt (by omega)
          have hsl := hy.sumOk
          have hsl2 := hy.sumLe
          rw [UInt64.toNat_add, hmul]
          exact Nat.mod_eq_of_lt (by omega)
      generalize hlenU : (if r.a = 16 then st.prevLen else 0) = lenU at hLU hsumU ⊢
      generalize (if lenU = 0 then st.symSum else st.symSum + (new - old) * ((32768 : UInt64) >>> lenU)) = sum at hsumU ⊢
      by_cases hbig : 32768 < sum
      · rw [ite_eq_left hbig]
        have hbig' : 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          show 32768 < lengthSum (ls.lens ++ List.replicate (Nn - On) Ln)
          rw [← hsumU]
          exact UInt64.lt_iff_toNat_lt.mp hbig
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hN]
        simp only [hover', hbig', ↓reduceIte]
      · rw [ite_eq_right hbig]
        have hbigN : ¬ 32768 < lengthSum (ls.lens ++ List.replicate (Nn - On) Ln) := by
          rw [← hsumU]
          exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
        have hbig' : ¬ 32768 < lengthSum (applyCodeLength ls r.a.toNat r.b.toNat).lens := by
          rw [happly]
          exact hbigN
        have hshorter : size + 1 - (applyCodeLength ls r.a.toNat r.b.toNat).lens.length < size + 1 - ls.lens.length := by
          rw [happly]
          simp only [List.length_append, List.length_replicate]
          omega
        have hsmallR : ∀ l ∈ ls.lens ++ List.replicate (Nn - On) Ln, l ≤ 15 := by
          intro l hl
          rcases List.mem_append.mp hl with h | h
          · exact hy.small l h
          · rw [(List.mem_replicate.mp h).2]
            exact hLle
        have hrep : Nn ≤ (ls.lens ++ List.replicate (Nn - On) Ln).length := by
          rw [hlen2]
          omega
        by_cases hz : lenU = 0
        · rw [ite_eq_left hz]
          have hz' : Ln = 0 := by rw [← hLU, hz]; rfl
          have hnew : SymRel { st with
              word := r.word, count := r.count, pos := pos, status := .next, ln := st.ln + (new - old), repSym := r.a
              repCount := new, symSum := sum } size clc (applyCodeLength ls r.a.toNat r.b.toNat) := by
            rw [happly]
            exact {
              table := hy.table
              complete := hy.complete
              symbols := hy.symbols
              ln := by
                show (st.ln + (new - old)).toNat = _
                rw [hln2, hlen2]
              le := by
                show (ls.lens ++ List.replicate (Nn - On) Ln).length ≤ size
                rw [hlen2]
                exact hroom
              lists := by
                show ListsIs st.head st.next (ls.lens ++ List.replicate (Nn - On) Ln)
                rw [hz']
                exact hy.lists.zeros _
              small := hsmallR
              prev := hy.prev
              prevOk := hy.prevOk
              rep := ⟨rfl, hNU, hgrow.2.2, hrep⟩
              sumOk := hsumU
              sumLe := Nat.le_of_not_lt hbigN }
          refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
            (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hshorter⟩⟩)
            (hm := HMove.ofD rfl (fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase,
              h.work⟩) (Nat.le_refl _)) rfl
            ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
          · rw [avail_mk, hN]
            simp only [hover', hbig', ↓reduceIte]
            rfl
          · rw [avail_mk, hStep_syms_step _ hlenLt hsumNe, readIn_some ((hval hsr).2 _)]
            simp only [hover', hbig', ↓reduceIte]
            rfl
        · rw [ite_eq_right hz]
          have hz' : ¬ Ln = 0 := fun e => hz (UInt64.toNat_inj.mp (by rw [hLU, e]; rfl))
          have hLU' : (if r.a = 16 then st.prevLen else 0).toNat = Ln := by rw [hlenU]; exact hLU
          have hl1 : (st.ln + 1).toNat = ls.lens.length + 1 := by rw [u64_succ (by omega), hln]
          have hold : (getHead st.head st.headSz (if r.a = 16 then st.prevLen else 0) (syms_lenLt hH hT r.a)).toNat =
              u16At st.head Ln := by rw [getHead_toNat, hLU']
          have hnew : SymRel (pushRun st r pos hH hT (st.ln + (new - old)) new sum (syms_lnLt hH hT h1) (syms_eLe hH hT hover)) size clc
              (applyCodeLength ls r.a.toNat r.b.toNat) := by
            rw [happly]
            exact {
              table := hy.table
              complete := hy.complete
              symbols := hy.symbols
              ln := by
                show (st.ln + (new - old)).toNat = _
                rw [hln2, hlen2]
              le := by
                show (ls.lens ++ List.replicate (Nn - On) Ln).length ≤ size
                rw [hlen2]
                exact hroom
              lists := ListsIs.run (L := ls.lens) (l := Ln) (n := Nn - On) hy.lists
                (head' := setHead st.head st.headSz (if r.a = 16 then st.prevLen else 0) (st.ln + (new - old)) (syms_lenLt hH hT r.a))
                (next' := linkRun (setNext st.next st.nextSz st.ln
                  (getHead st.head st.headSz (if r.a = 16 then st.prevLen else 0) (syms_lenLt hH hT r.a)) (syms_lnLt hH hT h1))
                  setNext_size (st.ln + 1) (st.ln + (new - old)) (syms_eLe hH hT hover))
                (by rw [linkRun_size]; omega)
                (fun j hj => by
                  rw [(linkRun_spec _ _ _ _ rfl).2 j, hl1, ite_eq_right (by omega), u16At_setNext, ite_eq_right (by omega)])
                (fun j hj1 hj2 => by
                  rw [(linkRun_spec _ _ _ _ rfl).2 j, hl1, hln2]
                  by_cases hj : j = ls.lens.length
                  · rw [ite_eq_right (by omega), u16At_setNext, ite_eq_left (show j = st.ln.toNat by omega), ite_eq_left hj, hold,
                      Nat.mod_eq_of_lt (u16At_lt _ _)]
                  · rw [ite_eq_left (by omega), ite_eq_right hj])
                (fun j hj => by rw [u16At_setHead, ite_eq_right (by rw [hLU']; exact hj)])
                (by
                  rw [u16At_setHead, ite_eq_left hLU'.symm, ite_eq_right (by omega), hln2]
                  exact Nat.mod_eq_of_lt (by omega))
                (by rw [setHead_size]; omega)
              small := hsmallR
              prev := hy.prev
              prevOk := hy.prevOk
              rep := ⟨rfl, hNU, hgrow.2.2, hrep⟩
              sumOk := hsumU
              sumLe := Nat.le_of_not_lt hbigN }
          refine HStepOk.ofNext (g' := g) (p' := .syms o size clc (applyCodeLength ls r.a.toNat r.b.toNat))
            (hd := Or.inr ⟨rfl, Or.inr ⟨rfl, hshorter⟩⟩)
            (hm := HMove.ofD rfl (fun h => ⟨h.fill, ⟨Nat.le_of_eq (Hd.headSz _), Nat.le_of_eq (Hd.nextSz _)⟩, h.clLens, h.clt, h.mapT,
              h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩) (Nat.le_refl _)) rfl
            ⟨hw2, hu, ht, hs, ho, hnew⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
          · rw [avail_mk, hN]
            simp only [hover', hbig', ↓reduceIte]
            rfl
          · rw [avail_mk, hStep_syms_step _ hlenLt hsumNe, readIn_some ((hval hsr).2 _)]
            simp only [hover', hbig', ↓reduceIte]
            rfl

end

end Brotli.Decoder
