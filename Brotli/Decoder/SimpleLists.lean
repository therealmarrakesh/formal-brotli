module

public import Brotli.Decoder.HeaderBuild

@[expose] public section

/-!
# A simple prefix code's lists

The lists of each length's symbols (`ListsIs`) of a simple prefix code with two symbols or more, written straight from
its symbols: each length's symbols in decreasing order, sorted by comparisons.
-/

namespace Brotli.Decoder
open Brotli.Spec

/-- Two increasing lists with the same members are equal. -/
theorem eq_of_lt_mem : ∀ {a b : List Nat}, a.Pairwise (· < ·) → b.Pairwise (· < ·) → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).mpr List.mem_cons_self) (by simp)
  | x :: _, [], _, _, h => absurd ((h x).mp List.mem_cons_self) (by simp)
  | x :: a, y :: b, ha, hb, h => by
    have hxy : x = y := by
      rcases List.mem_cons.mp ((h x).mp List.mem_cons_self) with e | e
      · exact e
      · rcases List.mem_cons.mp ((h y).mpr List.mem_cons_self) with e' | e'
        · exact e'.symm
        · have h1 := List.rel_of_pairwise_cons hb e
          have h2 := List.rel_of_pairwise_cons ha e'
          omega
    subst hxy
    refine congrArg _ (eq_of_lt_mem (List.pairwise_cons.mp ha).2 (List.pairwise_cons.mp hb).2 fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with e | e
      · have := List.rel_of_pairwise_cons ha hz
        omega
      · exact e
    · rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with e | e
      · have := List.rel_of_pairwise_cons hb hz
        omega
      · exact e

/-- A length's symbols are the increasing list of the symbols that have it. -/
theorem symsOf_eq {L ss : List Nat} {l : Nat} (hs : ss.Pairwise (· < ·)) (hm : ∀ s, s ∈ ss ↔ L[s]? = some l) :
    symsOf L l = ss :=
  eq_of_lt_mem (List.pairwise_lt_range.filter _) hs fun s => by rw [mem_symsOf, hm]

/-- The length `lengthsOf` gives a symbol from its pairs. -/
def lookupL (P : List (Nat × Nat)) (s : Nat) : Nat := ((P.find? (·.1 == s)).map (·.2)).getD 0

theorem lookupL_nil (s : Nat) : lookupL [] s = 0 := rfl

theorem lookupL_cons (s0 v : Nat) (P : List (Nat × Nat)) (s : Nat) :
    lookupL ((s0, v) :: P) s = if s = s0 then v else lookupL P s := by
  unfold lookupL
  rw [List.find?_cons]
  by_cases e : s = s0
  · subst e
    simp
  · have : ((s0, v).1 == s) = false := by simp; omega
    rw [this, ite_eq_right e]

/-- `lengthsOf`'s length at a symbol. -/
theorem lengthsOf_some (size : Nat) (P : List (Nat × Nat)) (s l : Nat) :
    (lengthsOf size P)[s]? = some l ↔ s < size ∧ lookupL P s = l := by
  unfold lengthsOf
  rw [List.getElem?_map]
  by_cases hs : s < size
  · rw [List.getElem?_range hs]
    simp [hs, lookupL]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp [hs]

private theorem pw1 (a : Nat) : [a].Pairwise (· < ·) := List.pairwise_singleton _ _

private theorem pw2 {a b : Nat} (h : a < b) : [a, b].Pairwise (· < ·) :=
  List.Pairwise.cons (fun x hx => by rw [List.mem_singleton.mp hx]; exact h) (pw1 b)

private theorem pw4 {a b c d : Nat} (h1 : a < b) (h2 : b < c) (h3 : c < d) : [a, b, c, d].Pairwise (· < ·) := by
  refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_) (pw2 h3))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

/-- Settles a membership goal over a few symbols by cases. -/
macro "mem_cases" : tactic => `(tactic| (
  repeat' split
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals constructor
  all_goals intro h
  all_goals first | omega | exact h.elim))

theorem syms_e1 {size a b : Nat} (ha : a < size) (hb : b < size) (hab : a ≠ b) {l : Nat} (hl0 : l ≠ 0) :
    symsOf (lengthsOf size [(a, 1), (b, 1)]) l = if l = 1 then [min a b, max a b] else [] := by
  refine symsOf_eq ?_ fun s => ?_
  · split
    · exact pw2 (by omega)
    · exact List.Pairwise.nil
  · rw [lengthsOf_some, lookupL_cons, lookupL_cons, lookupL_nil]
    mem_cases

theorem syms_e2 {size a b c : Nat} (ha : a < size) (hb : b < size) (hc : c < size) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {l : Nat} (hl0 : l ≠ 0) :
    symsOf (lengthsOf size [(a, 1), (b, 2), (c, 2)]) l = if l = 1 then [a] else if l = 2 then [min b c, max b c] else [] := by
  refine symsOf_eq ?_ fun s => ?_
  · split
    · exact pw1 a
    · split
      · exact pw2 (by omega)
      · exact List.Pairwise.nil
  · rw [lengthsOf_some, lookupL_cons, lookupL_cons, lookupL_cons, lookupL_nil]
    mem_cases

theorem syms_e3 {size a b c d : Nat} (ha : a < size) (hb : b < size) (hc : c < size) (hd : d < size) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {l : Nat} (hl0 : l ≠ 0) :
    symsOf (lengthsOf size [(a, 2), (b, 2), (c, 2), (d, 2)]) l = if l = 2 then
      [min (min a b) (min c d), min (min (max a b) (max c d)) (max (min a b) (min c d)),
        max (min (max a b) (max c d)) (max (min a b) (min c d)), max (max a b) (max c d)] else [] := by
  refine symsOf_eq ?_ fun s => ?_
  · split
    · exact pw4 (by omega) (by omega) (by omega)
    · exact List.Pairwise.nil
  · rw [lengthsOf_some, lookupL_cons, lookupL_cons, lookupL_cons, lookupL_cons, lookupL_nil]
    mem_cases

theorem syms_e7 {size a b c d : Nat} (ha : a < size) (hb : b < size) (hc : c < size) (hd : d < size) (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {l : Nat} (hl0 : l ≠ 0) :
    symsOf (lengthsOf size [(a, 1), (b, 2), (c, 3), (d, 3)]) l =
      if l = 1 then [a] else if l = 2 then [b] else if l = 3 then [min c d, max c d] else [] := by
  refine symsOf_eq ?_ fun s => ?_
  · split
    · exact pw1 a
    · split
      · exact pw1 b
      · split
        · exact pw2 (by omega)
        · exact List.Pairwise.nil
  · rw [lengthsOf_some, lookupL_cons, lookupL_cons, lookupL_cons, lookupL_cons, lookupL_nil]
    mem_cases

/-- What a simple code's read gives when it finishes: the shape `e`, and symbols below `size`, different from each other
where the shape has them, and 0 where it doesn't. -/
structure SimpleOk (size : UInt64) (r : Rd) : Prop where
  shape : r.e.toNat = 0 ∨ r.e.toNat = 1 ∨ r.e.toNat = 2 ∨ r.e.toNat = 3 ∨ r.e.toNat = 7
  lt : r.a.toNat < size.toNat ∧ r.b.toNat < size.toNat ∧ r.c.toNat < size.toNat ∧ r.d.toNat < size.toNat
  ab : r.e.toNat ≠ 0 → r.a.toNat ≠ r.b.toNat
  c : r.e.toNat ≠ 0 → r.e.toNat ≠ 1 → r.a.toNat ≠ r.c.toNat ∧ r.b.toNat ≠ r.c.toNat
  d : r.e.toNat = 3 ∨ r.e.toNat = 7 → r.a.toNat ≠ r.d.toNat ∧ r.b.toNat ≠ r.d.toNat ∧ r.c.toNat ≠ r.d.toNat

theorem simpleFast_simpleOk (size bits : UInt64) (b0 : BitBuffer) (h : (simpleFast size bits b0).status = .ok) :
    SimpleOk size (simpleFast size bits b0) := by
  have hite : ∀ {c : Prop} [Decidable c] {x y : Rd}, (c → x.status = .ok → SimpleOk size x) →
      (¬ c → y.status = .ok → SimpleOk size y) → (if c then x else y).status = .ok → SimpleOk size (if c then x else y) := by
    intro c _ x y hx hy
    by_cases h : c
    · rw [ite_eq_left h]
      exact hx h
    · rw [ite_eq_right h]
      exact hy h
  revert h
  unfold simpleFast
  dsimp only
  repeat' refine hite (fun _ => ?_) (fun _ => ?_)
  all_goals intro h
  all_goals first | exact absurd h (fun e => ReadStatus.noConfusion e) | skip
  all_goals simp only [Rd.ok, UInt64.le_iff_toNat_le, ← UInt64.toNat_inj, not_or, Nat.not_le, UInt64.reduceToNat] at *
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals dsimp only
  all_goals try simp only [UInt64.reduceToNat]
  all_goals first | omega | simp

/-- The larger of two values. -/
@[inline] def hiU (a b : UInt64) : UInt64 := if a < b then b else a

/-- The smaller of two values. -/
@[inline] def loU (a b : UInt64) : UInt64 := if a < b then a else b

theorem hiU_toNat (a b : UInt64) : (hiU a b).toNat = max a.toNat b.toNat := by
  unfold hiU
  by_cases h : a < b
  · rw [ite_eq_left h]
    have := UInt64.lt_iff_toNat_lt.mp h
    omega
  · rw [ite_eq_right h]
    have : ¬ a.toNat < b.toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr e)
    omega

theorem loU_toNat (a b : UInt64) : (loU a b).toNat = min a.toNat b.toNat := by
  unfold loU
  by_cases h : a < b
  · rw [ite_eq_left h]
    have := UInt64.lt_iff_toNat_lt.mp h
    omega
  · rw [ite_eq_right h]
    have : ¬ a.toNat < b.toNat := fun e => h (UInt64.lt_iff_toNat_lt.mpr e)
    omega

/-- Sets length `l`'s link in `head`. -/
@[inline] def setHead (t : ByteArray) (ht : t.size = 32) (l v : UInt64) (hl : l.toNat < 16) : ByteArray :=
  putSlot t l v (by omega) (by omega)

theorem setHead_size {t : ByteArray} {ht : t.size = 32} {l v : UInt64} {hl : l.toNat < 16} : (setHead t ht l v hl).size = 32 := by
  unfold setHead
  rw [size_putSlot, ht]

theorem u16At_setHead {t : ByteArray} {ht : t.size = 32} {l v : UInt64} {hl : l.toNat < 16} (j : Nat) :
    u16At (setHead t ht l v hl) j = if j = l.toNat then v.toNat % 65536 else u16At t j := u16At_putSlot' j

/-- Sets symbol `s`'s link in `next`. -/
@[inline] def setNext (t : ByteArray) (ht : t.size = 1408) (s v : UInt64) (hs : s.toNat < 704) : ByteArray :=
  putSlot t s v (by omega) (by omega)

theorem setNext_size {t : ByteArray} {ht : t.size = 1408} {s v : UInt64} {hs : s.toNat < 704} : (setNext t ht s v hs).size = 1408 := by
  unfold setNext
  rw [size_putSlot, ht]

theorem u16At_setNext {t : ByteArray} {ht : t.size = 1408} {s v : UInt64} {hs : s.toNat < 704} (j : Nat) :
    u16At (setNext t ht s v hs) j = if j = s.toNat then v.toNat % 65536 else u16At t j := u16At_putSlot' j

theorem u16At_resetHead {t : ByteArray} (ht : t.size = 32) (j : Nat) : u16At (resetHead t) j = 0 := by
  unfold u16At
  rw [resetHead_data ht, Array.getElem?_replicate, Array.getElem?_replicate]
  split <;> split <;> rfl

/-- Links one symbol, the last of its length's list. -/
@[inline] def next1 (t : ByteArray) (ht : t.size = 1408) (s : UInt64) (hs : s.toNat < 704) : ByteArray :=
  setNext t ht s 0 hs

/-- Links two symbols, `a` above `b`. -/
@[inline] def next2 (t : ByteArray) (ht : t.size = 1408) (a b : UInt64) (h : a.toNat < 704 ∧ b.toNat < 704) : ByteArray :=
  next1 (setNext t ht a (b + 1) h.1) setNext_size b h.2

/-- Links four symbols, from `a` down to `d`. -/
@[inline] def next4 (t : ByteArray) (ht : t.size = 1408) (a b c d : UInt64)
    (h : a.toNat < 704 ∧ b.toNat < 704 ∧ c.toNat < 704 ∧ d.toNat < 704) : ByteArray :=
  next2 (setNext (setNext t ht a (b + 1) h.1) setNext_size b (c + 1) h.2.1) setNext_size c d h.2.2

theorem next1_size {t : ByteArray} {ht : t.size = 1408} {s : UInt64} {hs : s.toNat < 704} : (next1 t ht s hs).size = 1408 :=
  setNext_size

theorem next2_size {t : ByteArray} {ht : t.size = 1408} {a b : UInt64} {h : a.toNat < 704 ∧ b.toNat < 704} :
    (next2 t ht a b h).size = 1408 := next1_size

/-- A simple code's symbols, below 704. -/
def SimpleFits (r : Rd) : Prop := r.a.toNat < 704 ∧ r.b.toNat < 704 ∧ r.c.toNat < 704 ∧ r.d.toNat < 704

/-- The four symbols of the first shape of four, from the largest down. -/
@[inline] def top4 (a b c d : UInt64) : UInt64 := hiU (hiU a b) (hiU c d)
@[inline] def sec4 (a b c d : UInt64) : UInt64 := hiU (loU (hiU a b) (hiU c d)) (hiU (loU a b) (loU c d))
@[inline] def thd4 (a b c d : UInt64) : UInt64 := loU (loU (hiU a b) (hiU c d)) (hiU (loU a b) (loU c d))
@[inline] def bot4 (a b c d : UInt64) : UInt64 := loU (loU a b) (loU c d)

theorem sort4_fits {r : Rd} (h : SimpleFits r) :
    (top4 r.a r.b r.c r.d).toNat < 704 ∧ (sec4 r.a r.b r.c r.d).toNat < 704 ∧ (thd4 r.a r.b r.c r.d).toNat < 704 ∧
      (bot4 r.a r.b r.c r.d).toNat < 704 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [top4, sec4, thd4, bot4, hiU_toNat, loU_toNat]
  omega

theorem hilo_fits {a b : UInt64} (ha : a.toNat < 704) (hb : b.toNat < 704) : (hiU a b).toNat < 704 ∧ (loU a b).toNat < 704 := by
  rw [hiU_toNat, loU_toNat]
  omega

/-- The links of a simple code with two symbols or more, in `next`. -/
def simpleNext (t : ByteArray) (ht : t.size = 1408) (r : Rd) (hf : SimpleFits r) : ByteArray :=
  if r.e = 1 then next2 t ht (hiU r.a r.b) (loU r.a r.b) (hilo_fits hf.1 hf.2.1)
  else if r.e = 2 then next2 (next1 t ht r.a hf.1) next1_size (hiU r.b r.c) (loU r.b r.c) (hilo_fits hf.2.1 hf.2.2.1)
  else if r.e = 3 then next4 t ht (top4 r.a r.b r.c r.d) (sec4 r.a r.b r.c r.d) (thd4 r.a r.b r.c r.d) (bot4 r.a r.b r.c r.d)
    (sort4_fits hf)
  else next2 (next1 (next1 t ht r.a hf.1) next1_size r.b hf.2.1) next1_size (hiU r.c r.d) (loU r.c r.d)
    (hilo_fits hf.2.2.1 hf.2.2.2)

/-- The links to each length's list of a simple code with two symbols or more, in `head`. -/
def simpleHead (t : ByteArray) (ht : t.size = 32) (r : Rd) : ByteArray :=
  if r.e = 1 then setHead (resetHead t) (resetHead_size ht) 1 (hiU r.a r.b + 1) (by decide)
  else if r.e = 2 then
    setHead (setHead (resetHead t) (resetHead_size ht) 1 (r.a + 1) (by decide)) setHead_size 2 (hiU r.b r.c + 1) (by decide)
  else if r.e = 3 then setHead (resetHead t) (resetHead_size ht) 2 (top4 r.a r.b r.c r.d + 1) (by decide)
  else setHead (setHead (setHead (resetHead t) (resetHead_size ht) 1 (r.a + 1) (by decide)) setHead_size 2 (r.b + 1) (by decide))
    setHead_size 3 (hiU r.c r.d + 1) (by decide)

theorem simpleHead_size {t : ByteArray} {ht : t.size = 32} {r : Rd} : (simpleHead t ht r).size = 32 := by
  unfold simpleHead
  split
  · exact setHead_size
  · split
    · exact setHead_size
    · split
      · exact setHead_size
      · exact setHead_size

theorem simpleNext_size {t : ByteArray} {ht : t.size = 1408} {r : Rd} {hf : SimpleFits r} : (simpleNext t ht r hf).size = 1408 := by
  unfold simpleNext
  split
  · exact next2_size
  · split
    · exact next2_size
    · split
      · exact next2_size
      · exact next2_size

theorem u64_succ {x : UInt64} (h : x.toNat < 704) : (x + 1).toNat = x.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt (by omega)

theorem simple_lists_e1 {t n : ByteArray} {ht : t.size = 32} {hn : n.size = 1408} {size : UInt64} {r : Rd}
    (hok : SimpleOk size r) (hs : size.toNat ≤ 704) {hf : SimpleFits r} (he : r.e = 1) :
    ListsIs (simpleHead t ht r) (simpleNext n hn r hf) (lengthsOf size.toNat [(r.a.toNat, 1), (r.b.toNat, 1)]) := by
  have he' : r.e.toNat = 1 := by rw [he]; rfl
  have hab := hok.ab (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := hok.lt
  refine ⟨by rw [simpleHead_size]; omega, fun l hl1 hl2 => ?_⟩
  rw [syms_e1 h1 h2 hab (by omega)]
  have fM := hiU_toNat r.a r.b
  have fm := loU_toNat r.a r.b
  have e1 : (hiU r.a r.b + 1).toNat = (hiU r.a r.b).toNat + 1 := u64_succ (by omega)
  have e2 : (loU r.a r.b + 1).toNat = (loU r.a r.b).toNat + 1 := u64_succ (by omega)
  by_cases hl : l = 1
  · subst hl
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    simp only [he, ChainIs, simpleHead, simpleNext, next1, next2, u16At_setHead, u16At_setNext,
      setNext_size, ↓reduceIte, e1, e2, UInt64.reduceToNat]
    generalize (hiU r.a r.b).toNat = M at *
    generalize (loU r.a r.b).toNat = m at *
    repeat' split
    all_goals omega
  · simp only [hl, ↓reduceIte, List.reverse_nil]
    simp only [he, ChainIs, simpleHead, u16At_setHead, u16At_resetHead ht, ↓reduceIte, e1, UInt64.reduceToNat]
    split <;> omega

theorem simple_lists_e2 {t n : ByteArray} {ht : t.size = 32} {hn : n.size = 1408} {size : UInt64} {r : Rd}
    (hok : SimpleOk size r) (hs : size.toNat ≤ 704) {hf : SimpleFits r} (he : r.e = 2) :
    ListsIs (simpleHead t ht r) (simpleNext n hn r hf) (lengthsOf size.toNat [(r.a.toNat, 1), (r.b.toNat, 2), (r.c.toNat, 2)]) := by
  have he' : r.e.toNat = 2 := by rw [he]; rfl
  have hab := hok.ab (by omega)
  obtain ⟨hac, hbc⟩ := hok.c (by omega) (by omega)
  have he1 : ¬ r.e = 1 := by rw [he]; decide
  obtain ⟨h1, h2, h3, h4⟩ := hok.lt
  refine ⟨by rw [simpleHead_size]; omega, fun l hl1 hl2 => ?_⟩
  rw [syms_e2 h1 h2 h3 hab hac hbc (by omega)]
  have fM := hiU_toNat r.b r.c
  have fm := loU_toNat r.b r.c
  have e0 : (r.a + 1).toNat = r.a.toNat + 1 := u64_succ (by omega)
  have e1 : (hiU r.b r.c + 1).toNat = (hiU r.b r.c).toNat + 1 := u64_succ (by omega)
  have e2 : (loU r.b r.c + 1).toNat = (loU r.b r.c).toNat + 1 := u64_succ (by omega)
  simp only [simpleHead, simpleNext, ite_eq_right he1, ite_eq_left he]
  by_cases hl : l = 1
  · subst hl
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append]
    simp only [ChainIs, next1, next2, u16At_setHead, u16At_setNext, u16At_resetHead ht, setNext_size, e0, UInt64.reduceToNat]
    generalize (hiU r.b r.c).toNat = M at *
    generalize (loU r.b r.c).toNat = m at *
    repeat' split
    all_goals first | omega | exact absurd trivial ‹¬True›
  by_cases hl' : l = 2
  · subst hl'
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, hl]
    simp only [ChainIs, next1, next2, u16At_setHead, u16At_setNext, u16At_resetHead ht, setNext_size, e1, e2,
      UInt64.reduceToNat]
    generalize (hiU r.b r.c).toNat = M at *
    generalize (loU r.b r.c).toNat = m at *
    repeat' split
    all_goals first | omega | exact absurd trivial ‹¬True›
  · simp only [hl, hl', ↓reduceIte, List.reverse_nil]
    simp only [ChainIs, u16At_setHead, u16At_resetHead ht, e0, e1, UInt64.reduceToNat]
    repeat' split
    all_goals omega

theorem simple_lists_e7 {t n : ByteArray} {ht : t.size = 32} {hn : n.size = 1408} {size : UInt64} {r : Rd}
    (hok : SimpleOk size r) (hs : size.toNat ≤ 704) {hf : SimpleFits r} (he : r.e = 7) :
    ListsIs (simpleHead t ht r) (simpleNext n hn r hf)
      (lengthsOf size.toNat [(r.a.toNat, 1), (r.b.toNat, 2), (r.c.toNat, 3), (r.d.toNat, 3)]) := by
  have he' : r.e.toNat = 7 := by rw [he]; rfl
  have hab := hok.ab (by omega)
  obtain ⟨hac, hbc⟩ := hok.c (by omega) (by omega)
  obtain ⟨had, hbd, hcd⟩ := hok.d (by omega)
  have he1 : ¬ r.e = 1 := by rw [he]; decide
  have he2 : ¬ r.e = 2 := by rw [he]; decide
  have he3 : ¬ r.e = 3 := by rw [he]; decide
  obtain ⟨h1, h2, h3, h4⟩ := hok.lt
  refine ⟨by rw [simpleHead_size]; omega, fun l hl1 hl2 => ?_⟩
  rw [syms_e7 h1 h2 h3 h4 hab hac had hbc hbd hcd (by omega)]
  have fM := hiU_toNat r.c r.d
  have fm := loU_toNat r.c r.d
  have e0 : (r.a + 1).toNat = r.a.toNat + 1 := u64_succ (by omega)
  have e0' : (r.b + 1).toNat = r.b.toNat + 1 := u64_succ (by omega)
  have e1 : (hiU r.c r.d + 1).toNat = (hiU r.c r.d).toNat + 1 := u64_succ (by omega)
  have e2 : (loU r.c r.d + 1).toNat = (loU r.c r.d).toNat + 1 := u64_succ (by omega)
  simp only [simpleHead, simpleNext, ite_eq_right he1, ite_eq_right he2, ite_eq_right he3]
  by_cases hl : l = 1
  · subst hl
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append]
    simp only [ChainIs, next1, next2, u16At_setHead, u16At_setNext, setNext_size, ↓reduceIte, e0, UInt64.reduceToNat]
    generalize (hiU r.c r.d).toNat = M at *
    generalize (loU r.c r.d).toNat = m at *
    repeat' split
    all_goals omega
  by_cases hl' : l = 2
  · subst hl'
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, hl]
    simp only [ChainIs, next1, next2, u16At_setHead, u16At_setNext, setNext_size, ↓reduceIte, e0', UInt64.reduceToNat]
    generalize (hiU r.c r.d).toNat = M at *
    generalize (loU r.c r.d).toNat = m at *
    repeat' split
    all_goals omega
  by_cases hl'' : l = 3
  · subst hl''
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, hl, hl']
    simp only [ChainIs, next1, next2, u16At_setHead, u16At_setNext, setNext_size, ↓reduceIte, e1, e2, UInt64.reduceToNat]
    generalize (hiU r.c r.d).toNat = M at *
    generalize (loU r.c r.d).toNat = m at *
    repeat' split
    all_goals omega
  · simp only [hl, hl', hl'', ↓reduceIte, List.reverse_nil]
    simp only [ChainIs, u16At_setHead, u16At_resetHead ht, e0, e0', e1, UInt64.reduceToNat]
    repeat' split
    all_goals omega

theorem simple_lists_e3 {t n : ByteArray} {ht : t.size = 32} {hn : n.size = 1408} {size : UInt64} {r : Rd}
    (hok : SimpleOk size r) (hs : size.toNat ≤ 704) {hf : SimpleFits r} (he : r.e = 3) :
    ListsIs (simpleHead t ht r) (simpleNext n hn r hf)
      (lengthsOf size.toNat [(r.a.toNat, 2), (r.b.toNat, 2), (r.c.toNat, 2), (r.d.toNat, 2)]) := by
  have he' : r.e.toNat = 3 := by rw [he]; rfl
  have hab := hok.ab (by omega)
  obtain ⟨hac, hbc⟩ := hok.c (by omega) (by omega)
  obtain ⟨had, hbd, hcd⟩ := hok.d (by omega)
  have he1 : ¬ r.e = 1 := by rw [he]; decide
  have he2 : ¬ r.e = 2 := by rw [he]; decide
  obtain ⟨h1, h2, h3, h4⟩ := hok.lt
  refine ⟨by rw [simpleHead_size]; omega, fun l hl1 hl2 => ?_⟩
  rw [syms_e3 h1 h2 h3 h4 hab hac had hbc hbd hcd (by omega)]
  have f1 : (top4 r.a r.b r.c r.d).toNat = max (max r.a.toNat r.b.toNat) (max r.c.toNat r.d.toNat) := by
    simp only [top4, hiU_toNat]
  have f2 : (sec4 r.a r.b r.c r.d).toNat =
      max (min (max r.a.toNat r.b.toNat) (max r.c.toNat r.d.toNat)) (max (min r.a.toNat r.b.toNat) (min r.c.toNat r.d.toNat)) := by
    simp only [sec4, hiU_toNat, loU_toNat]
  have f3 : (thd4 r.a r.b r.c r.d).toNat =
      min (min (max r.a.toNat r.b.toNat) (max r.c.toNat r.d.toNat)) (max (min r.a.toNat r.b.toNat) (min r.c.toNat r.d.toNat)) := by
    simp only [thd4, hiU_toNat, loU_toNat]
  have f4 : (bot4 r.a r.b r.c r.d).toNat = min (min r.a.toNat r.b.toNat) (min r.c.toNat r.d.toNat) := by
    simp only [bot4, loU_toNat]
  have hw : (bot4 r.a r.b r.c r.d).toNat < (thd4 r.a r.b r.c r.d).toNat ∧ (thd4 r.a r.b r.c r.d).toNat < (sec4 r.a r.b r.c r.d).toNat ∧
      (sec4 r.a r.b r.c r.d).toNat < (top4 r.a r.b r.c r.d).toNat ∧ (top4 r.a r.b r.c r.d).toNat < 704 := by
    rw [f1, f2, f3, f4]
    omega
  have e1 : (top4 r.a r.b r.c r.d + 1).toNat = (top4 r.a r.b r.c r.d).toNat + 1 := u64_succ (by omega)
  have e2 : (sec4 r.a r.b r.c r.d + 1).toNat = (sec4 r.a r.b r.c r.d).toNat + 1 := u64_succ (by omega)
  have e3 : (thd4 r.a r.b r.c r.d + 1).toNat = (thd4 r.a r.b r.c r.d).toNat + 1 := u64_succ (by omega)
  have e4 : (bot4 r.a r.b r.c r.d + 1).toNat = (bot4 r.a r.b r.c r.d).toNat + 1 := u64_succ (by omega)
  rw [← f1, ← f2, ← f3, ← f4]
  clear f1 f2 f3 f4
  simp only [simpleHead, simpleNext, ite_eq_right he1, ite_eq_right he2, ite_eq_left he]
  by_cases hl : l = 2
  · subst hl
    simp only [↓reduceIte, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    simp only [ChainIs, next1, next2, next4, u16At_setHead, u16At_setNext, setNext_size, ↓reduceIte, e1, e2, e3, e4,
      UInt64.reduceToNat]
    generalize (top4 r.a r.b r.c r.d).toNat = W1 at *
    generalize (sec4 r.a r.b r.c r.d).toNat = W2 at *
    generalize (thd4 r.a r.b r.c r.d).toNat = W3 at *
    generalize (bot4 r.a r.b r.c r.d).toNat = W4 at *
    simp only [and_true]
    repeat' split
    all_goals first | omega | exact absurd trivial ‹¬True›
  · simp only [hl, ↓reduceIte, List.reverse_nil]
    simp only [ChainIs, u16At_setHead, u16At_resetHead ht, e1, UInt64.reduceToNat]
    split <;> omega

private theorem e_of {r : Rd} {k : Nat} (h : r.e.toNat = k) (hk : k < 2 ^ 64) : r.e = UInt64.ofNat k :=
  UInt64.toNat_inj.mp (by rw [h, UInt64.toNat_ofNat']; exact (Nat.mod_eq_of_lt hk).symm)

/-- A simple code with two symbols or more has canonical lengths over its alphabet, and `simpleHead` and `simpleNext` write
their lists. -/
theorem simple_lists {t n : ByteArray} {ht : t.size = 32} {hn : n.size = 1408} {size : UInt64} {r : Rd}
    (hok : SimpleOk size r) (hs : size.toNat ≤ 704) {hf : SimpleFits r} (he : r.e.toNat ≠ 0) :
    ∃ L, simpleCode size.toNat r.a.toNat r.b.toNat r.c.toNat r.d.toNat r.e.toNat = .canonical L ∧ L.length = size.toNat ∧
      ListsIs (simpleHead t ht r) (simpleNext n hn r hf) L := by
  have hlen : ∀ P, (lengthsOf size.toNat P).length = size.toNat := fun P => by simp [lengthsOf]
  unfold simpleCode
  rw [ite_eq_right he]
  rcases hok.shape with h | h | h | h | h
  · exact absurd h he
  · rw [ite_eq_left h]
    exact ⟨_, rfl, hlen _, simple_lists_e1 hok hs (e_of h (by decide))⟩
  · rw [ite_eq_right (by omega), ite_eq_left h]
    exact ⟨_, rfl, hlen _, simple_lists_e2 hok hs (e_of h (by decide))⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h]
    exact ⟨_, rfl, hlen _, simple_lists_e3 hok hs (e_of h (by decide))⟩
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    exact ⟨_, rfl, hlen _, simple_lists_e7 hok hs (e_of h (by decide))⟩

attribute [irreducible] simpleHead simpleNext

end Brotli.Decoder
