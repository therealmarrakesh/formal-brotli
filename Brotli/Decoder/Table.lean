module

public import Brotli.Decoder.Slots
public import Brotli.Decoder.Codes

@[expose] public section

/-!
# The two-level table

A code's table is 256 root slots, indexed by the next 8 bits, followed by sub-tables for the code words longer than
that. A root slot holds a code word's length and symbol, or, with a bit count above 8, that bit count and where its
sub-table starts, counted from the table's start. `TableOk` says what a table guarantees: lookup gives every bit pattern
its hit. This module holds what a table is and what it takes; `buildTable` (`TableDown`) builds one.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### What a table has to do -/

/-- The slot a lookup ends at: the root slot, or a sub-table slot if the root slot's bit count is above 8. -/
def lookupSlots (t : ByteArray) (base w : Nat) : Nat × Nat :=
  let e := slotAt t (base + w % 256)
  if e.1 ≤ 8 then e else slotAt t (base + e.2 + (w / 256) % 2 ^ (e.1 - 8))

/-- The table at `base` is in the array and stays within it. This is all a lookup needs to be safe, and it says
nothing about the spec, so the decoder's state can carry it. -/
structure TableFits (t : ByteArray) (base : Nat) : Prop where
  root : 2 * (base + 256) ≤ t.size
  sub : ∀ r, r < 256 → 8 < (slotAt t (base + r)).1 →
    (slotAt t (base + r)).1 ≤ 15 ∧ 2 * (base + (slotAt t (base + r)).2 + 2 ^ ((slotAt t (base + r)).1 - 8)) ≤ t.size

/-- The table at `base` also gives every bit pattern its hit. -/
structure TableOk (t : ByteArray) (base : Nat) (c : PrefixCode) : Prop extends TableFits t base where
  hit : ∀ w, Hit c w (lookupSlots t base w).1 (lookupSlots t base w).2

/-! ### Writing runs of slots -/

/-- Writes `count` slots from `pos`, every `step`. -/
def writeRange (bits val step : Nat) : Nat → ByteArray → Nat → ByteArray
  | 0, t, _ => t
  | count + 1, t, pos => writeRange bits val step count (writeSlot t pos bits val) (pos + step)

theorem size_writeRange (bits val step : Nat) : ∀ (count : Nat) (t : ByteArray) (pos : Nat),
    (writeRange bits val step count t pos).size = t.size
  | 0, _, _ => rfl
  | count + 1, t, pos => by
    rw [writeRange, size_writeRange bits val step count, size_writeSlot]

/-- The slots written hold what was written, and the others are unchanged. -/
theorem slotAt_writeRange {bits val step : Nat} (hb : bits < 16) (hv : val < 4096) : ∀ (count : Nat) (t : ByteArray)
    (pos q : Nat), (∀ k, k < count → 2 * (pos + k * step) + 1 < t.size) →
    slotAt (writeRange bits val step count t pos) q =
      if ∃ k, k < count ∧ q = pos + k * step then (bits, val) else slotAt t q
  | 0, _, _, q, _ => by simp [writeRange]
  | count + 1, t, pos, q, h => by
    have hin := h 0 (by omega)
    have hsz := size_writeSlot t pos bits val
    have ih := slotAt_writeRange hb hv count (writeSlot t pos bits val) (pos + step) q (by
      intro k hk
      rw [hsz]
      have := h (k + 1) (by omega)
      have e : pos + (k + 1) * step = pos + step + k * step := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rwa [e] at this)
    rw [writeRange, ih]
    by_cases hq : ∃ k, k < count ∧ q = pos + step + k * step
    · obtain ⟨k, hk, e⟩ := hq
      rw [ite_eq_left ⟨k, hk, e⟩, ite_eq_left ⟨k + 1, by omega, by rw [e, Nat.add_mul, Nat.one_mul]; omega⟩]
    · rw [ite_eq_right hq]
      by_cases hp : q = pos
      · subst hp
        rw [ite_eq_left ⟨0, by omega, by simp⟩]
        exact slotAt_writeSlot_same (by simpa using hin) hb hv
      · rw [slotAt_writeSlot_ne hp, ite_eq_right]
        rintro ⟨k, hk, e⟩
        cases k with
        | zero => exact hp (by simpa using e)
        | succ k =>
          exact hq ⟨k, by omega, by rw [e, Nat.add_mul, Nat.one_mul]; omega⟩

/-! ### Sub-table depths -/

/-- The root slot of a code word: its first 8 bits, as the buffer holds them. -/
def rootOf (l c : Nat) : Nat := revBits l c % 256

/-- A long code word's sub-table needs at least its bits past the root. -/
def recordDepth (D : Array Nat) (_ l c : Nat) : Array Nat :=
  if l ≤ 8 then D else D.setIfInBounds (rootOf l c) (max (D.getD (rootOf l c) 0) (l - 8))

/-- Each root slot's sub-table depth, 0 if it has none. -/
def depths (lens : List Nat) : Array Nat :=
  foldCodes recordDepth lens 0 (nextCodes lens) (Array.replicate 256 0)

private theorem getD_set' {cs : Array Nat} {l n v : Nat} (hl : l < cs.size) :
    (cs.setIfInBounds l v).getD n 0 = if n = l then v else cs.getD n 0 := by
  by_cases h : n = l
  · subst h
    simp [Array.getD_eq_getD_getElem?, hl]
  · simp [Array.getD_eq_getD_getElem?, h, Ne.symm h]

/-- Symbol `s` has a code word longer than the root. -/
def Long (lens : List Nat) (s l c : Nat) : Prop :=
  lens[s]? = some l ∧ 8 < l ∧ code lens s = some c

private theorem code_some {lens : List Nat} {s l : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0) :
    ∃ c, code lens s = some c := by
  simp [code, hs, h0]

theorem rootOf_lt (l c : Nat) : rootOf l c < 256 := Nat.mod_lt _ (by decide)

/-- What `depths` gives. -/
theorem depths_spec {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) :
    (depths lens).size = 256 ∧ (∀ r, (depths lens).getD r 0 ≤ 7) ∧
      (∀ r, (depths lens).getD r 0 ≠ 0 → ∃ s l c, Long lens s l c ∧ rootOf l c = r) ∧
      (∀ s l c, Long lens s l c → l - 8 ≤ (depths lens).getD (rootOf l c) 0) := by
  have key := foldCodes_ind (f := recordDepth) hl
    (fun s D => D.size = 256 ∧ (∀ r, D.getD r 0 ≤ 7) ∧
      (∀ r, D.getD r 0 ≠ 0 → ∃ s' l c, s' < s ∧ Long lens s' l c ∧ rootOf l c = r) ∧
      (∀ s' l c, s' < s → Long lens s' l c → l - 8 ≤ D.getD (rootOf l c) 0))
    (by
      rintro s D ⟨h1, h2, h3, h4⟩ hz
      refine ⟨h1, h2, ?_, ?_⟩
      · intro r hr
        obtain ⟨s', l, c, hs, hL, he⟩ := h3 r hr
        exact ⟨s', l, c, by omega, hL, he⟩
      · intro s' l c hs hL
        by_cases he : s' = s
        · subst he
          have := hL.1
          rw [hz] at this
          simp only [Option.some.injEq] at this
          have := hL.2.1
          omega
        · exact h4 s' l c (by omega) hL)
    (by
      rintro s l D ⟨h1, h2, h3, h4⟩ hg h0
      obtain ⟨c, hc⟩ := code_some hg h0
      have hl15 : l ≤ 15 := hl l (List.mem_of_getElem? hg)
      simp only [hc, Option.getD_some]
      unfold recordDepth
      split
      · rename_i hs8
        refine ⟨h1, h2, ?_, ?_⟩
        · intro r hr
          obtain ⟨s', l', c', hs, hL, he⟩ := h3 r hr
          exact ⟨s', l', c', by omega, hL, he⟩
        · intro s' l' c' hs hL
          by_cases he : s' = s
          · subst he
            have := hL.1
            rw [hg] at this
            simp only [Option.some.injEq] at this
            have := hL.2.1
            omega
          · exact h4 s' l' c' (by omega) hL
      · rename_i hs8
        have hroot : rootOf l c < D.size := by
          have := rootOf_lt l c
          omega
        refine ⟨by simpa using h1, ?_, ?_, ?_⟩
        · intro r
          rw [getD_set' hroot]
          by_cases he : r = rootOf l c
          · simp only [he, ↓reduceIte]
            have := h2 (rootOf l c)
            omega
          · simp only [he, ↓reduceIte]
            exact h2 r
        · intro r hr
          rw [getD_set' hroot] at hr
          by_cases he : r = rootOf l c
          · exact ⟨s, l, c, by omega, ⟨hg, by omega, hc⟩, he.symm⟩
          · simp only [he, ↓reduceIte] at hr
            obtain ⟨s', l', c', hs, hL, e⟩ := h3 r hr
            exact ⟨s', l', c', by omega, hL, e⟩
        · intro s' l' c' hs hL
          rw [getD_set' hroot]
          by_cases hes : s' = s
          · subst hes
            have e1 := hL.1
            rw [hg] at e1
            simp only [Option.some.injEq] at e1
            have e2 := hL.2.2
            rw [hc] at e2
            simp only [Option.some.injEq] at e2
            subst e1
            subst e2
            simp only [↓reduceIte]
            omega
          · have := h4 s' l' c' (by omega) hL
            by_cases he : rootOf l' c' = rootOf l c
            · simp only [he, ↓reduceIte]
              rw [he] at this
              omega
            · simp only [he, ↓reduceIte]
              exact this)
    (acc := Array.replicate 256 0)
    (by
      refine ⟨by simp, ?_, ?_, ?_⟩
      · intro r
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
        split <;> simp
      · intro r hr
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hr
        split at hr <;> simp at hr
      · intro s' l c hs
        omega)
  obtain ⟨h1, h2, h3, h4⟩ := key
  refine ⟨h1, h2, ?_, ?_⟩
  · intro r hr
    obtain ⟨s, l, c, _, hL, he⟩ := h3 r hr
    exact ⟨s, l, c, hL, he⟩
  · intro s l c hL
    refine h4 s l c ?_ hL
    exact (List.getElem?_eq_some_iff.mp hL.1).1

/-- A sub-table's slots, 0 if it has none. -/
def subSize (d : Nat) : Nat := if d = 0 then 0 else 2 ^ d

/-- The slots of the sub-tables of the root slots below `i`. -/
def offSum (D : Array Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => offSum D i + subSize (D.getD i 0)

/-! ### Bit patterns and code words -/

theorem pow_split (w d : Nat) : w % 2 ^ (8 + d) = w % 256 + 256 * ((w / 256) % 2 ^ d) := by
  rw [Nat.pow_add]
  exact Nat.mod_mul

theorem pow_split' {l : Nat} (h : 8 ≤ l) (w : Nat) :
    w % 2 ^ l = w % 256 + 256 * ((w / 256) % 2 ^ (l - 8)) := by
  have := pow_split w (l - 8)
  rwa [show 8 + (l - 8) = l by omega] at this

/-- A hit looks only at the bits it needs. -/
theorem Hit.transfer {c : PrefixCode} {w w' l s n : Nat} (h : Hit c w l s) (hl : l ≤ n)
    (he : w' % 2 ^ n = w % 2 ^ n) : Hit c w' l s := by
  cases c with
  | single sym => exact h
  | canonical lens =>
    obtain ⟨hs, h0, hc⟩ := h
    refine ⟨hs, h0, ?_⟩
    rw [hc, ← revBits_mod_of_le hl w, ← revBits_mod_of_le hl w', he]

/-- A range of slots, as its slot numbers. -/
theorem range_iff {l W st : Nat} (hl : l ≤ W) (hst : st < 2 ^ l) (i : Nat) :
    (i < 2 ^ W ∧ i % 2 ^ l = st) ↔ ∃ k, k < 2 ^ (W - l) ∧ i = st + k * 2 ^ l := by
  have hpos : 0 < 2 ^ l := Nat.two_pow_pos _
  have hp : 2 ^ W = 2 ^ (W - l) * 2 ^ l := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hl]
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨i / 2 ^ l, ?_, ?_⟩
    · rw [hp] at hi
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hi)
    · have := Nat.mod_add_div i (2 ^ l)
      rw [hm, Nat.mul_comm] at this
      exact this.symm
  · rintro ⟨k, hk, rfl⟩
    constructor
    · rw [hp]
      calc st + k * 2 ^ l
          < 2 ^ l + k * 2 ^ l := by omega
        _ = (k + 1) * 2 ^ l := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        _ ≤ 2 ^ (W - l) * 2 ^ l := Nat.mul_le_mul_right _ hk
    · rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hst]

/-- Reversing a reverse gives the low bits. -/
theorem revBits_twice (l w : Nat) : revBits l (revBits l w) = w % 2 ^ l := by
  rw [← revBits_mod l w]
  exact revBits_revBits (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem mod_256_of_le {l : Nat} (hl : 8 ≤ l) (w : Nat) : w % 2 ^ l % 256 = w % 256 :=
  Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 hl)

section Build

variable {lens : List Nat}

/-- A short code word's root slot has no sub-table. -/
theorem hit_short_zero (hC : Complete (.canonical lens)) {w l s : Nat} (h : Hit (.canonical lens) w l s)
    (hl : l ≤ 8) : (depths lens).getD (w % 256) 0 = 0 := by
  refine Classical.byContradiction fun hz => ?_
  obtain ⟨s', l', c', hL, hr⟩ := (depths_spec hC.1).2.2.1 _ hz
  have hl15 : l' ≤ 15 := hC.1 l' (List.mem_of_getElem? hL.1)
  have hlt : c' < 2 ^ l' :=
    code_lt_two_pow (Nat.le_of_eq hC.2) hL.1 (by have := hL.2.1; omega) hl15 hL.2.2
  have hh : Hit (.canonical lens) (revBits l' c') l' s' :=
    ⟨hL.1, by have := hL.2.1; omega, by rw [hL.2.2, revBits_revBits hlt]⟩
  have he : revBits l' c' % 2 ^ 8 = w % 2 ^ 8 := hr
  have h2 := Hit.transfer h hl he
  have := (h2.unique hh hC).1
  have := hL.2.1
  omega

/-- A long code word has a sub-table deep enough, at its root slot. -/
theorem hit_long (hC : Complete (.canonical lens)) {w l s : Nat} (h : Hit (.canonical lens) w l s)
    (hl : 8 < l) : l - 8 ≤ (depths lens).getD (w % 256) 0 ∧ rootOf l (revBits l w) = w % 256 := by
  have hroot : rootOf l (revBits l w) = w % 256 := by
    unfold rootOf
    rw [revBits_twice, mod_256_of_le (by omega)]
  refine ⟨?_, hroot⟩
  rw [← hroot]
  exact (depths_spec hC.1).2.2.2 s l _ ⟨h.1, hl, h.2.2⟩

end Build

/-- A slot is unchanged by adding bytes after the array. -/
theorem slotAt_append {t z : ByteArray} {q : Nat} (h : 2 * q + 1 < t.size) : slotAt (t ++ z) q = slotAt t q := by
  have key : ∀ i, i < t.size → (t ++ z).data[i]? = t.data[i]? := by
    intro i hi
    rw [← Array.getElem?_toList, ByteArray.toList_data_append, List.getElem?_append_left (by simpa using hi),
      Array.getElem?_toList]
  simp only [slotAt, slotNum]
  rw [key _ (by omega), key _ (by omega)]

/-- The slots a code's table takes: the size `buildTable` adds to the arena, in slots. -/
def tableSlots : PrefixCode → Nat
  | .single _ => 256
  | .canonical lens => 256 + offSum (depths lens) 256

/-- A table stays correct when the array changes only after it. -/
theorem TableOk.frame {t t' : ByteArray} {base : Nat} {c : PrefixCode} (h : TableOk t base c) (ht : t.size % 2 = 0)
    (hsize : t.size ≤ t'.size) (hframe : ∀ q, q < t.size / 2 → slotAt t' q = slotAt t q) : TableOk t' base c := by
  have hrootSlot : ∀ r, r < 256 → slotAt t' (base + r) = slotAt t (base + r) := by
    intro r hr
    have := h.root
    exact hframe _ (by omega)
  refine ⟨⟨by have := h.root; omega, ?_⟩, ?_⟩
  · intro r hr hb
    rw [hrootSlot r hr] at hb ⊢
    obtain ⟨h1, h2⟩ := h.sub r hr hb
    exact ⟨h1, by omega⟩
  · intro w
    have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
    have heq : lookupSlots t' base w = lookupSlots t base w := by
      unfold lookupSlots
      dsimp only
      rw [hrootSlot _ hr]
      split
      · rfl
      · rename_i hb
        have hb' : 8 < (slotAt t (base + w % 256)).1 := by omega
        obtain ⟨_, h2⟩ := h.sub _ hr hb'
        have hj : (w / 256) % 2 ^ ((slotAt t (base + w % 256)).1 - 8) < 2 ^ ((slotAt t (base + w % 256)).1 - 8) :=
          Nat.mod_lt _ (Nat.two_pow_pos _)
        exact hframe _ (by omega)
    rw [heq]
    exact h.hit w

end Brotli.Decoder
