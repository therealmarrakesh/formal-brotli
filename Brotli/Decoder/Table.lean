import Brotli.Decoder.Slots
import Brotli.Decoder.Codes

/-!
# The two-level table

A code's table is 256 root slots, indexed by the next 8 bits, followed by sub-tables for the code words longer than
that. A root slot holds a code word's length and symbol, or, with a bit count above 8, that bit count and where its
sub-table starts. `buildTable` appends a code's table to the arena, and `TableOk` says what it guarantees: lookup
gives every bit pattern its hit.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### What a table has to do -/

/-- The slot a lookup ends at: the root slot, or a sub-table slot if the root slot's bit count is above 8. -/
def lookupSlots (t : ByteArray) (base w : Nat) : Nat × Nat :=
  let e := slotAt t (base + w % 256)
  if e.1 ≤ 8 then e else slotAt t (base + 256 + e.2 + (w / 256) % 2 ^ (e.1 - 8))

/-- The table at `base` is in the array and stays within it. This is all a lookup needs to be safe, and it says
nothing about the spec, so the decoder's state can carry it. -/
structure TableFits (t : ByteArray) (base : Nat) : Prop where
  root : 4 * (base + 256) ≤ t.size
  sub : ∀ r, r < 256 → 8 < (slotAt t (base + r)).1 →
    (slotAt t (base + r)).1 ≤ 15 ∧
      4 * (base + 256 + (slotAt t (base + r)).2 + 2 ^ ((slotAt t (base + r)).1 - 8)) ≤ t.size

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
theorem slotAt_writeRange {bits val step : Nat} (hb : bits < 256) (hv : val < 65536) : ∀ (count : Nat) (t : ByteArray)
    (pos q : Nat), (∀ k, k < count → 4 * (pos + k * step) + 2 < t.size) →
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

/-! ### Sub-table depths and offsets -/

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

/-- Where the sub-table of root slot `r` starts, after the root. -/
def offSum (D : Array Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => offSum D i + subSize (D.getD i 0)

/-- Assigns the sub-tables' offsets, and their total. -/
def offsetsFrom (D : Array Nat) : Nat → Nat → Nat → Array Nat → Array Nat × Nat
  | 0, _, next, acc => (acc, next)
  | n + 1, r, next, acc => offsetsFrom D n (r + 1) (next + subSize (D.getD r 0)) (acc.push next)

private theorem offsetsFrom_spec (D : Array Nat) : ∀ (n r : Nat) (acc : Array Nat), acc.size = r →
    (∀ i, i < r → acc.getD i 0 = offSum D i) →
    (offsetsFrom D n r (offSum D r) acc).2 = offSum D (r + n) ∧
      ∀ i, i < r + n → (offsetsFrom D n r (offSum D r) acc).1.getD i 0 = offSum D i
  | 0, r, acc, _, h => ⟨rfl, h⟩
  | n + 1, r, acc, hs, h => by
    simp only [offsetsFrom]
    have e : offSum D r + subSize (D.getD r 0) = offSum D (r + 1) := rfl
    rw [e]
    obtain ⟨h1, h2⟩ := offsetsFrom_spec D n (r + 1) (acc.push (offSum D r)) (by simp [hs]) (by
      intro i hi
      by_cases he : i = r
      · subst he
        subst hs
        simp [Array.getD_eq_getD_getElem?]
      · have hlt : i < r := by omega
        have := h i hlt
        simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push] at this ⊢
        simp [show i ≠ acc.size by omega, this])
    rw [show r + 1 + n = r + (n + 1) by omega] at h1 h2
    exact ⟨h1, h2⟩

/-- The offsets of a table's 256 root slots, and their total. -/
def offsets (D : Array Nat) : Array Nat × Nat := offsetsFrom D 256 0 0 #[]

theorem offsets_spec (D : Array Nat) :
    (offsets D).2 = offSum D 256 ∧ ∀ i, i < 256 → (offsets D).1.getD i 0 = offSum D i := by
  have := offsetsFrom_spec D 256 0 #[] rfl (by intro i hi; omega)
  rw [Nat.zero_add] at this
  exact this

private theorem offSum_le (D : Array Nat) : ∀ {a b : Nat}, a < b → offSum D a + subSize (D.getD a 0) ≤ offSum D b := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
    show _ ≤ offSum D b + subSize (D.getD b 0)
    by_cases he : a = b
    · subst he
      omega
    · have := ih (by omega)
      omega

private theorem subSize_le {d : Nat} (h : d ≤ 7) : subSize d ≤ 128 := by
  unfold subSize
  split
  · omega
  · exact Nat.pow_le_pow_right (by decide) h

theorem offSum_bound {D : Array Nat} (hD : ∀ r, D.getD r 0 ≤ 7) : ∀ i, offSum D i ≤ 128 * i
  | 0 => by simp [offSum]
  | i + 1 => by
    have := offSum_bound hD i
    have := subSize_le (hD i)
    simp only [offSum]
    omega

/-! ### Where each bit pattern's slot is -/

/-- The slot a bit pattern's lookup ends at, relative to the table's start. -/
def slotPos (D : Array Nat) (w : Nat) : Nat :=
  if D.getD (w % 256) 0 = 0 then w % 256
  else 256 + offSum D (w % 256) + (w / 256) % 2 ^ D.getD (w % 256) 0

private theorem pow_split (w d : Nat) : w % 2 ^ (8 + d) = w % 256 + 256 * ((w / 256) % 2 ^ d) := by
  rw [Nat.pow_add]
  exact Nat.mod_mul

private theorem pow_split' {l : Nat} (h : 8 ≤ l) (w : Nat) :
    w % 2 ^ l = w % 256 + 256 * ((w / 256) % 2 ^ (l - 8)) := by
  have := pow_split w (l - 8)
  rwa [show 8 + (l - 8) = l by omega] at this

/-- Bit patterns with the same slot agree on the bits their lookup looks at. -/
private theorem slotPos_low {D : Array Nat} {w w' : Nat} (h : slotPos D w = slotPos D w') :
    D.getD (w' % 256) 0 = D.getD (w % 256) 0 ∧ w' % 2 ^ (8 + D.getD (w % 256) 0) = w % 2 ^ (8 + D.getD (w % 256) 0) := by
  have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
  have hr' : w' % 256 < 256 := Nat.mod_lt _ (by decide)
  have hrr : w' % 256 = w % 256 ∧ (D.getD (w % 256) 0 = 0 ∨
      (w / 256) % 2 ^ D.getD (w % 256) 0 = (w' / 256) % 2 ^ D.getD (w % 256) 0) := by
    unfold slotPos at h
    by_cases hz : D.getD (w % 256) 0 = 0
    · by_cases hz' : D.getD (w' % 256) 0 = 0
      · simp only [hz, hz', ↓reduceIte] at h
        exact ⟨h.symm, Or.inl hz⟩
      · simp only [hz, hz', ↓reduceIte] at h
        omega
    · by_cases hz' : D.getD (w' % 256) 0 = 0
      · simp only [hz, hz', ↓reduceIte] at h
        omega
      · simp only [hz, hz', ↓reduceIte] at h
        have hlt1 : (w / 256) % 2 ^ D.getD (w % 256) 0 < 2 ^ D.getD (w % 256) 0 := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hlt2 : (w' / 256) % 2 ^ D.getD (w' % 256) 0 < 2 ^ D.getD (w' % 256) 0 := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hs1 : subSize (D.getD (w % 256) 0) = 2 ^ D.getD (w % 256) 0 := by
          unfold subSize
          rw [ite_eq_right hz]
        have hs2 : subSize (D.getD (w' % 256) 0) = 2 ^ D.getD (w' % 256) 0 := by
          unfold subSize
          rw [ite_eq_right hz']
        have heq : w' % 256 = w % 256 := by
          refine Nat.le_antisymm (Nat.le_of_not_lt fun hl => ?_) (Nat.le_of_not_lt fun hl => ?_)
          · have := offSum_le D hl
            omega
          · have := offSum_le D hl
            omega
        rw [heq] at h
        exact ⟨heq, Or.inr (by omega)⟩
  obtain ⟨e, hj⟩ := hrr
  refine ⟨by rw [e], ?_⟩
  rw [pow_split, pow_split, e]
  rcases hj with hz | hj
  · simp [hz, Nat.mod_one]
  · rw [hj]

/-- A hit looks only at the bits it needs. -/
private theorem Hit.transfer {c : PrefixCode} {w w' l s n : Nat} (h : Hit c w l s) (hl : l ≤ n)
    (he : w' % 2 ^ n = w % 2 ^ n) : Hit c w' l s := by
  cases c with
  | single sym => exact h
  | canonical lens =>
    obtain ⟨hs, h0, hc⟩ := h
    refine ⟨hs, h0, ?_⟩
    rw [hc, ← revBits_mod_of_le hl w, ← revBits_mod_of_le hl w', he]

/-- A range of slots, as its slot numbers. -/
private theorem range_iff {l W st : Nat} (hl : l ≤ W) (hst : st < 2 ^ l) (i : Nat) :
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
private theorem revBits_twice (l w : Nat) : revBits l (revBits l w) = w % 2 ^ l := by
  rw [← revBits_mod l w]
  exact revBits_revBits (Nat.mod_lt _ (Nat.two_pow_pos _))

private theorem mod_256_of_le {l : Nat} (hl : 8 ≤ l) (w : Nat) : w % 2 ^ l % 256 = w % 256 :=
  Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 hl)

section Build

variable {lens : List Nat}

/-- A short code word's root slot has no sub-table. -/
private theorem hit_short_zero (hC : Complete (.canonical lens)) {w l s : Nat} (h : Hit (.canonical lens) w l s)
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
private theorem hit_long (hC : Complete (.canonical lens)) {w l s : Nat} (h : Hit (.canonical lens) w l s)
    (hl : 8 < l) : l - 8 ≤ (depths lens).getD (w % 256) 0 ∧ rootOf l (revBits l w) = w % 256 := by
  have hroot : rootOf l (revBits l w) = w % 256 := by
    unfold rootOf
    rw [revBits_twice, mod_256_of_le (by omega)]
  refine ⟨?_, hroot⟩
  rw [← hroot]
  exact (depths_spec hC.1).2.2.2 s l _ ⟨h.1, hl, h.2.2⟩

/-- Every position a bit pattern can end at is within the table. -/
private theorem slotPos_lt {D : Array Nat} (w : Nat) : slotPos D w < 256 + offSum D 256 := by
  have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold slotPos
  split
  · omega
  · rename_i hz
    have h1 := offSum_le D hr
    have h2 : (w / 256) % 2 ^ D.getD (w % 256) 0 < 2 ^ D.getD (w % 256) 0 := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h3 : subSize (D.getD (w % 256) 0) = 2 ^ D.getD (w % 256) 0 := by
      unfold subSize
      rw [ite_eq_right hz]
    omega

/-- Writes a code word's slots: those of every bit pattern that begins with it. -/
def writeCode (base : Nat) (D off : Array Nat) (t : ByteArray) (s l c : Nat) : ByteArray :=
  if l ≤ 8 then writeRange l s (2 ^ l) (2 ^ (8 - l)) t (base + revBits l c)
  else
    writeRange l s (2 ^ (l - 8)) (2 ^ (D.getD (rootOf l c) 0 - (l - 8))) t
      (base + 256 + off.getD (rootOf l c) 0 + revBits l c / 256)

/-- A position written by a code word is the slot of a bit pattern that begins with it. -/
private theorem written_hit (hC : Complete (.canonical lens)) {off : Array Nat}
    (hoff : ∀ i, i < 256 → off.getD i 0 = offSum (depths lens) i) {s l c : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0)
    (hc : code lens s = some c) {base k : Nat}
    (hk : k < (if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD (rootOf l c) 0 - (l - 8)))) :
    ∃ w, revBits l w = c ∧
      (if l ≤ 8 then base + revBits l c + k * 2 ^ l
       else base + 256 + off.getD (rootOf l c) 0 + revBits l c / 256 + k * 2 ^ (l - 8)) =
        base + slotPos (depths lens) w := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hlt : c < 2 ^ l := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte] at hk ⊢
    have hi := (range_iff hl hst (revBits l c + k * 2 ^ l)).mpr ⟨k, hk, rfl⟩
    have hrev : revBits l (revBits l c + k * 2 ^ l) = c := (revBits_eq_iff hlt).mpr hi.2
    refine ⟨_, hrev, ?_⟩
    have hhit : Hit (.canonical lens) (revBits l c + k * 2 ^ l) l s := ⟨hs, h0, by rw [hc, hrev]⟩
    have hz := hit_short_zero hC hhit hl
    have hmod : (revBits l c + k * 2 ^ l) % 256 = revBits l c + k * 2 ^ l := Nat.mod_eq_of_lt hi.1
    unfold slotPos
    rw [ite_eq_left hz, hmod, Nat.add_assoc]
  · simp only [hl, ↓reduceIte] at hk ⊢
    have hl8 : 8 < l := by omega
    have hd := (depths_spec hC.1).2.2.2 s l c ⟨hs, hl8, hc⟩
    generalize hdd : (depths lens).getD (rootOf l c) 0 = d at hk hd ⊢
    have hle : l - 8 ≤ d := hd
    have hst8 : 2 ^ l = 256 * 2 ^ (l - 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      congr 1
      omega
    have hj0 : revBits l c / 256 < 2 ^ (l - 8) := Nat.div_lt_of_lt_mul (by rw [← hst8]; exact hst)
    have hj := (range_iff hle hj0 (revBits l c / 256 + k * 2 ^ (l - 8))).mpr ⟨k, hk, rfl⟩
    generalize hjd : revBits l c / 256 + k * 2 ^ (l - 8) = j at hj
    have hr : rootOf l c < 256 := rootOf_lt l c
    have hwm : (rootOf l c + 256 * j) % 256 = rootOf l c := by omega
    have hwd : (rootOf l c + 256 * j) / 256 = j := by omega
    have hwl : (rootOf l c + 256 * j) % 2 ^ l = revBits l c := by
      rw [pow_split' (by omega), hwm, hwd, hj.2]
      unfold rootOf
      omega
    have hrev : revBits l (rootOf l c + 256 * j) = c := (revBits_eq_iff hlt).mpr hwl
    refine ⟨_, hrev, ?_⟩
    have hpos : d ≠ 0 := by omega
    unfold slotPos
    rw [hwm, hdd, ite_eq_right hpos, hwd, Nat.mod_eq_of_lt hj.1, hoff _ hr, ← hjd]
    omega

/-- The slot of a bit pattern that begins with a code word is a position that code word writes. -/
private theorem hit_written (hC : Complete (.canonical lens)) {off : Array Nat}
    (hoff : ∀ i, i < 256 → off.getD i 0 = offSum (depths lens) i) {s l c w : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0)
    (hc : code lens s = some c) (hw : revBits l w = c) (base : Nat) :
    ∃ k, k < (if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD (rootOf l c) 0 - (l - 8))) ∧
      base + slotPos (depths lens) w =
        (if l ≤ 8 then base + revBits l c + k * 2 ^ l
         else base + 256 + off.getD (rootOf l c) 0 + revBits l c / 256 + k * 2 ^ (l - 8)) := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hlt : c < 2 ^ l := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  have hm : w % 2 ^ l = revBits l c := (revBits_eq_iff hlt).mp hw
  have hhit : Hit (.canonical lens) w l s := ⟨hs, h0, by rw [hc, hw]⟩
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte]
    have hz := hit_short_zero hC hhit hl
    have hi : w % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    have hmm : w % 256 % 2 ^ l = revBits l c := by
      rw [← hm]
      exact Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 hl)
    obtain ⟨k, hk, e⟩ := (range_iff hl hst (w % 256)).mp ⟨hi, hmm⟩
    refine ⟨k, hk, ?_⟩
    unfold slotPos
    rw [ite_eq_left hz, e, Nat.add_assoc]
  · simp only [hl, ↓reduceIte]
    have hl8 : 8 < l := by omega
    obtain ⟨hd, hroot⟩ := hit_long hC hhit hl8
    rw [hw] at hroot
    rw [hroot, hoff _ (Nat.mod_lt _ (by decide))]
    generalize hdd : (depths lens).getD (w % 256) 0 = d at hd ⊢
    have hst8 : 2 ^ l = 256 * 2 ^ (l - 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      congr 1
      omega
    have hj0 : revBits l c / 256 < 2 ^ (l - 8) := Nat.div_lt_of_lt_mul (by rw [← hst8]; exact hst)
    have hsplit : w % 2 ^ l = w % 256 + 256 * ((w / 256) % 2 ^ (l - 8)) := pow_split' (by omega) w
    have hjm : (w / 256) % 2 ^ (l - 8) = revBits l c / 256 := by
      have h256 : w % 256 < 256 := Nat.mod_lt _ (by decide)
      omega
    have hj : (w / 256) % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hjj : (w / 256) % 2 ^ d % 2 ^ (l - 8) = revBits l c / 256 := by
      rw [← hjm]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hd)
    obtain ⟨k, hk, e⟩ := (range_iff hd hj0 ((w / 256) % 2 ^ d)).mp ⟨hj, hjj⟩
    refine ⟨k, hk, ?_⟩
    have hpos : d ≠ 0 := by omega
    unfold slotPos
    rw [hdd, ite_eq_right hpos, e]
    omega

/-- What a code word's write does to the slots. -/
private theorem slotAt_writeCode (hC : Complete (.canonical lens)) {off : Array Nat}
    (hoff : ∀ i, i < 256 → off.getD i 0 = offSum (depths lens) i) {s l c base : Nat} {t : ByteArray}
    (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c) (hval : s < 65536)
    (hsize : 4 * (base + 256 + offSum (depths lens) 256) ≤ t.size) (q : Nat) :
    ((∃ w, revBits l w = c ∧ q = base + slotPos (depths lens) w) →
        slotAt (writeCode base (depths lens) off t s l c) q = (l, s)) ∧
      ((¬ ∃ w, revBits l w = c ∧ q = base + slotPos (depths lens) w) →
        slotAt (writeCode base (depths lens) off t s l c) q = slotAt t q) := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hbits : l < 256 := by omega
  unfold writeCode
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte]
    rw [slotAt_writeRange hbits hval]
    · constructor
      · rintro ⟨w, hw, e⟩
        obtain ⟨k, hk, ew⟩ := hit_written hC hoff hs h0 hc hw base
        simp only [hl, ↓reduceIte] at hk ew
        rw [ite_eq_left ⟨k, hk, by rw [e, ew]⟩]
      · intro hn
        rw [ite_eq_right]
        rintro ⟨k, hk, e⟩
        have := written_hit hC hoff (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
        simp only [hl, ↓reduceIte] at this
        obtain ⟨w, hw, ew⟩ := this
        exact hn ⟨w, hw, by rw [e, ew]⟩
    · intro k hk
      have := written_hit hC hoff (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
      simp only [hl, ↓reduceIte] at this
      obtain ⟨w, _, ew⟩ := this
      have := slotPos_lt (D := depths lens) w
      omega
  · simp only [hl, ↓reduceIte]
    rw [slotAt_writeRange hbits hval]
    · constructor
      · rintro ⟨w, hw, e⟩
        obtain ⟨k, hk, ew⟩ := hit_written hC hoff hs h0 hc hw base
        simp only [hl, ↓reduceIte] at hk ew
        rw [ite_eq_left ⟨k, hk, by rw [e, ew]⟩]
      · intro hn
        rw [ite_eq_right]
        rintro ⟨k, hk, e⟩
        have := written_hit hC hoff (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
        simp only [hl, ↓reduceIte] at this
        obtain ⟨w, hw, ew⟩ := this
        exact hn ⟨w, hw, by rw [e, ew]⟩
    · intro k hk
      have := written_hit hC hoff (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
      simp only [hl, ↓reduceIte] at this
      obtain ⟨w, _, ew⟩ := this
      have := slotPos_lt (D := depths lens) w
      omega

/-- A code word's slots are in the array. -/
theorem written_in (hC : Complete (.canonical lens)) {off : Array Nat}
    (hoff : ∀ i, i < 256 → off.getD i 0 = offSum (depths lens) i) {s l c base : Nat} {t : ByteArray}
    (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c)
    (hsize : 4 * (base + 256 + offSum (depths lens) 256) ≤ t.size) {k : Nat}
    (hk : k < (if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD (rootOf l c) 0 - (l - 8)))) :
    4 * (if l ≤ 8 then base + revBits l c + k * 2 ^ l
         else base + 256 + off.getD (rootOf l c) 0 + revBits l c / 256 + k * 2 ^ (l - 8)) + 2 < t.size := by
  obtain ⟨w, _, ew⟩ := written_hit hC hoff (base := base) hs h0 hc hk
  rw [ew]
  have := slotPos_lt (D := depths lens) w
  omega

theorem size_writeCode' (base : Nat) (D off : Array Nat) (t : ByteArray) (s l c : Nat) :
    (writeCode base D off t s l c).size = t.size := by
  unfold writeCode
  split <;> exact size_writeRange ..

/-- Writes each root slot with a sub-table, from `r`. -/
def writeRoots (base : Nat) (D off : Array Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, t => t
  | n + 1, r, t =>
    writeRoots base D off n (r + 1)
      (if D.getD r 0 = 0 then t else writeSlot t (base + r) (8 + D.getD r 0) (off.getD r 0))

private theorem size_writeRoots (base : Nat) (D off : Array Nat) : ∀ (n r : Nat) (t : ByteArray),
    (writeRoots base D off n r t).size = t.size
  | 0, _, _ => rfl
  | n + 1, r, t => by
    rw [writeRoots, size_writeRoots base D off n]
    split
    · rfl
    · exact size_writeSlot ..

/-- What the root writes do: a root slot with a sub-table holds its depth and offset, and the rest is unchanged. -/
private theorem slotAt_writeRoots {base : Nat} {D off : Array Nat} (hD : ∀ r, D.getD r 0 ≤ 7)
    (hoff : ∀ r, r < 256 → off.getD r 0 < 65536) : ∀ (n r : Nat) (t : ByteArray), r + n ≤ 256 →
    4 * (base + 256) ≤ t.size → ∀ q,
    ((∃ r', r ≤ r' ∧ r' < r + n ∧ D.getD r' 0 ≠ 0 ∧ q = base + r') →
        slotAt (writeRoots base D off n r t) q = (8 + D.getD (q - base) 0, off.getD (q - base) 0)) ∧
      ((¬ ∃ r', r ≤ r' ∧ r' < r + n ∧ D.getD r' 0 ≠ 0 ∧ q = base + r') →
        slotAt (writeRoots base D off n r t) q = slotAt t q)
  | 0, r, t, _, _, q => by
    refine ⟨?_, fun _ => rfl⟩
    rintro ⟨r', h1, h2, _⟩
    omega
  | n + 1, r, t, hn, hsize, q => by
    have hsz : (if D.getD r 0 = 0 then t else writeSlot t (base + r) (8 + D.getD r 0) (off.getD r 0)).size = t.size := by
      split
      · rfl
      · exact size_writeSlot ..
    obtain ⟨ih1, ih2⟩ := slotAt_writeRoots (base := base) (off := off) hD hoff n (r + 1) _ (by omega)
      (by rw [hsz]; exact hsize) q
    rw [writeRoots]
    constructor
    · rintro ⟨r', h1, h2, h3, h4⟩
      by_cases he : r' = r
      · subst he
        by_cases hq : ∃ r'', r' + 1 ≤ r'' ∧ r'' < r' + 1 + n ∧ D.getD r'' 0 ≠ 0 ∧ q = base + r''
        · exact ih1 hq
        · rw [ih2 hq]
          simp only [h3, ↓reduceIte]
          rw [h4, Nat.add_sub_cancel_left]
          exact slotAt_writeSlot_same (by omega) (by have := hD r'; omega) (hoff r' (by omega))
      · exact ih1 ⟨r', by omega, by omega, h3, h4⟩
    · intro hnot
      rw [ih2 (fun ⟨r', h1, h2, h3, h4⟩ => hnot ⟨r', by omega, by omega, h3, h4⟩)]
      by_cases hz : D.getD r 0 = 0
      · simp only [hz, ↓reduceIte]
      · simp only [hz, ↓reduceIte]
        refine slotAt_writeSlot_ne fun hp => hnot ⟨r, by omega, by omega, hz, hp⟩

/-- A slot is unchanged by adding bytes after the array. -/
private theorem slotAt_append {t z : ByteArray} {q : Nat} (h : 4 * q + 2 < t.size) : slotAt (t ++ z) q = slotAt t q := by
  have key : ∀ i, i < t.size → (t ++ z).data[i]? = t.data[i]? := by
    intro i hi
    rw [← Array.getElem?_toList, ByteArray.toList_data_append, List.getElem?_append_left (by simpa using hi),
      Array.getElem?_toList]
  simp only [slotAt]
  rw [key _ (by omega), key _ (by omega), key _ (by omega)]

/-- Appends a canonical code's table to the arena. Its slots start at `t.size / 4`. -/
def buildCanonical (t : ByteArray) (lens : List Nat) : ByteArray :=
  let base := t.size / 4
  let D := depths lens
  let o := offsets D
  let t1 := t ++ ByteArray.mk (Array.replicate (4 * (256 + o.2)) 0)
  let t2 := foldCodes (fun t s l c => writeCode base D o.1 t s l c) lens 0 (nextCodes lens) t1
  writeRoots base D o.1 256 0 t2

/-- A canonical code's table does its job, and leaves the tables before it alone. -/
theorem buildCanonical_spec {t : ByteArray} (hC : Complete (.canonical lens)) (ht : t.size % 4 = 0)
    (hlen : lens.length ≤ 65536) :
    TableOk (buildCanonical t lens) (t.size / 4) (.canonical lens) ∧
      (buildCanonical t lens).size % 4 = 0 ∧ (∀ q, q < t.size / 4 → slotAt (buildCanonical t lens) q = slotAt t q) ∧
      (buildCanonical t lens).size = t.size + 4 * (256 + offSum (depths lens) 256) := by
  obtain ⟨dS, dLe, dEx, dDeep⟩ := depths_spec hC.1
  obtain ⟨oTot, oAt⟩ := offsets_spec (depths lens)
  have hoffb : ∀ r, r < 256 → (offsets (depths lens)).1.getD r 0 < 65536 := by
    intro r hr
    rw [oAt r hr]
    have := offSum_bound dLe r
    omega
  unfold buildCanonical
  dsimp only
  rw [oTot]
  generalize hbase : t.size / 4 = base
  have hsz4 : t.size = 4 * base := by omega
  have hmk : (ByteArray.mk (Array.replicate (4 * (256 + offSum (depths lens) 256)) 0)).size =
      4 * (256 + offSum (depths lens) 256) := by
    show (Array.replicate _ _).size = _
    simp
  generalize ht1 : t ++ ByteArray.mk (Array.replicate (4 * (256 + offSum (depths lens) 256)) 0) = t1
  have hs1 : t1.size = t.size + 4 * (256 + offSum (depths lens) 256) := by
    rw [← ht1, ByteArray.size_append, hmk]
  have hframe1 : ∀ q, q < base → slotAt t1 q = slotAt t q := by
    intro q hq
    rw [← ht1]
    exact slotAt_append (by omega)
  have key := foldCodes_ind (f := fun t s l c => writeCode base (depths lens) (offsets (depths lens)).1 t s l c) hC.1
    (fun s t' => t'.size = t1.size ∧ (∀ q, q < base → slotAt t' q = slotAt t1 q) ∧
      ∀ s' l w, s' < s → Hit (.canonical lens) w l s' → slotAt t' (base + slotPos (depths lens) w) = (l, s'))
    (by
      rintro s t' ⟨h1, h2, h3⟩ hz
      refine ⟨h1, h2, ?_⟩
      intro s' l w hlt hh
      by_cases he : s' = s
      · subst he
        have e := hh.1
        rw [hz] at e
        simp only [Option.some.injEq] at e
        exact absurd e.symm hh.2.1
      · exact h3 s' l w (by omega) hh)
    (by
      rintro s l t' ⟨h1, h2, h3⟩ hg h0
      obtain ⟨c, hc⟩ : ∃ c, code lens s = some c := by simp [code, hg, h0]
      simp only [hc, Option.getD_some]
      have hslt : s < 65536 := by
        have := (List.getElem?_eq_some_iff.mp hg).1
        omega
      have hsize : 4 * (base + 256 + offSum (depths lens) 256) ≤ t'.size := by
        rw [h1, hs1]
        omega
      refine ⟨by rw [size_writeCode', h1], ?_, ?_⟩
      · intro q hq
        rw [(slotAt_writeCode hC oAt hg h0 hc hslt hsize q).2 (by
          rintro ⟨w, _, e⟩
          omega), h2 q hq]
      · intro s' l' w hlt hh
        have hw := slotAt_writeCode hC oAt hg h0 hc hslt hsize (base + slotPos (depths lens) w)
        by_cases hes : s' = s
        · subst hes
          have e := hh.1
          rw [hg] at e
          simp only [Option.some.injEq] at e
          subst e
          have hwc : revBits l w = c := by
            have e2 := hh.2.2
            rw [hc] at e2
            simp only [Option.some.injEq] at e2
            exact e2.symm
          exact hw.1 ⟨w, hwc, rfl⟩
        · by_cases hq : ∃ w', revBits l w' = c ∧ base + slotPos (depths lens) w = base + slotPos (depths lens) w'
          · exfalso
            obtain ⟨w', hw', e⟩ := hq
            have hpos : slotPos (depths lens) w = slotPos (depths lens) w' := by omega
            obtain ⟨hd, hlow⟩ := slotPos_low hpos
            have hhit' : Hit (.canonical lens) w' l s := ⟨hg, h0, by rw [hc, hw']⟩
            have hle : l ≤ 8 + (depths lens).getD (w % 256) 0 := by
              by_cases hl8 : l ≤ 8
              · omega
              · have := (hit_long hC hhit' (by omega)).1
                rw [hd] at this
                omega
            have hh2 := Hit.transfer hhit' hle hlow.symm
            exact hes (hh.unique hh2 hC).2
          · rw [hw.2 hq]
            exact h3 s' l' w (by omega) hh)
    (acc := t1)
    (by exact ⟨rfl, fun _ _ => rfl, by intro s' l w h; omega⟩)
  obtain ⟨k1, k2, k3⟩ := key
  generalize ht2 : foldCodes (fun t s l c => writeCode base (depths lens) (offsets (depths lens)).1 t s l c) lens 0
    (nextCodes lens) t1 = t2 at k1 k2 k3
  have hroots := slotAt_writeRoots (base := base) (D := depths lens) (off := (offsets (depths lens)).1) dLe hoffb 256 0 t2
    (by omega) (by rw [k1, hs1]; omega)
  simp only [Nat.zero_add] at hroots
  have hsize3 : (writeRoots base (depths lens) (offsets (depths lens)).1 256 0 t2).size =
      t.size + 4 * (256 + offSum (depths lens) 256) := by
    rw [size_writeRoots, k1, hs1]
  -- A slot that a bit pattern ends at keeps its value through the root writes.
  have hkeep : ∀ s l w, Hit (.canonical lens) w l s →
      slotAt (writeRoots base (depths lens) (offsets (depths lens)).1 256 0 t2) (base + slotPos (depths lens) w) = (l, s) := by
    intro s l w hh
    rw [(hroots _).2 (by
      rintro ⟨r', _, h2, h3, h4⟩
      have hpos : slotPos (depths lens) w = r' := by omega
      unfold slotPos at hpos
      split at hpos
      · rename_i hz
        subst hpos
        exact h3 hz
      · omega), k3 s l w ((List.getElem?_eq_some_iff.mp hh.1).1) hh]
  -- A root slot with a sub-table holds its depth and offset.
  have hroot : ∀ r, r < 256 → (depths lens).getD r 0 ≠ 0 →
      slotAt (writeRoots base (depths lens) (offsets (depths lens)).1 256 0 t2) (base + r) =
        (8 + (depths lens).getD r 0, offSum (depths lens) r) := by
    intro r hr hz
    rw [(hroots _).1 ⟨r, by omega, by omega, hz, rfl⟩, Nat.add_sub_cancel_left, oAt r hr]
  generalize writeRoots base (depths lens) (offsets (depths lens)).1 256 0 t2 = t3 at hsize3 hroots hkeep hroot
  refine ⟨⟨⟨by rw [hsize3]; omega, ?_⟩, ?_⟩, by rw [hsize3]; omega, ?_, hsize3⟩
  · intro r hr hbig
    by_cases hz : (depths lens).getD r 0 = 0
    · exfalso
      obtain ⟨l, s, hh⟩ := hit_exists hC r
      have hk := hkeep s l r hh
      have hmod : r % 256 = r := Nat.mod_eq_of_lt hr
      have hp : slotPos (depths lens) r = r := by
        unfold slotPos
        rw [hmod, ite_eq_left hz]
      rw [hp] at hk
      rw [hk] at hbig
      have := hit_long hC hh hbig
      rw [hmod, hz] at this
      have := this.1
      simp only at hbig
      omega
    · rw [hroot r hr hz]
      have hle := dLe r
      refine ⟨by simp only; omega, ?_⟩
      simp only [Nat.add_sub_cancel_left]
      have h1 := offSum_le (depths lens) hr
      have h3 : subSize ((depths lens).getD r 0) = 2 ^ (depths lens).getD r 0 := by
        unfold subSize
        rw [ite_eq_right hz]
      rw [hsize3]
      omega
  · intro w
    obtain ⟨l, s, hh⟩ := hit_exists hC w
    have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
    have hk := hkeep s l w hh
    unfold slotPos at hk
    unfold lookupSlots
    dsimp only
    by_cases hz : (depths lens).getD (w % 256) 0 = 0
    · rw [ite_eq_left hz] at hk
      have hl8 : l ≤ 8 := by
        refine Nat.le_of_not_lt fun hg => ?_
        have := (hit_long hC hh hg).1
        omega
      rw [hk]
      simp only [hl8, ↓reduceIte]
      exact hh
    · rw [ite_eq_right hz] at hk
      rw [hroot _ hr hz]
      have hpos : (8 + (depths lens).getD (w % 256) 0) > 8 := by omega
      simp only [show ¬ 8 + (depths lens).getD (w % 256) 0 ≤ 8 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
      have e : base + 256 + offSum (depths lens) (w % 256) + (w / 256) % 2 ^ (depths lens).getD (w % 256) 0 =
          base + (256 + offSum (depths lens) (w % 256) + (w / 256) % 2 ^ (depths lens).getD (w % 256) 0) := by omega
      rw [e, hk]
      exact hh
  · intro q hq
    rw [(hroots _).2 (by
      rintro ⟨r', _, _, _, h⟩
      omega), k2 q hq, hframe1 q hq]

end Build

/-- Appends a single-symbol code's table: all 256 root slots hold the symbol, with no bits to read. -/
def buildSingle (t : ByteArray) (sym : Nat) : ByteArray :=
  writeRange 0 sym 1 256 (t ++ ByteArray.mk (Array.replicate (4 * 256) 0)) (t.size / 4)

theorem buildSingle_spec {t : ByteArray} {sym : Nat} (ht : t.size % 4 = 0) (hsym : sym < 65536) :
    TableOk (buildSingle t sym) (t.size / 4) (.single sym) ∧ (buildSingle t sym).size % 4 = 0 ∧
      (∀ q, q < t.size / 4 → slotAt (buildSingle t sym) q = slotAt t q) ∧
      (buildSingle t sym).size = t.size + 4 * 256 := by
  have hmk : (ByteArray.mk (Array.replicate (4 * 256) 0)).size = 4 * 256 := by
    show (Array.replicate _ _).size = _
    simp
  generalize ht1 : t ++ ByteArray.mk (Array.replicate (4 * 256) 0) = t1 at *
  have hs1 : t1.size = t.size + 4 * 256 := by
    rw [← ht1, ByteArray.size_append, hmk]
  unfold buildSingle
  rw [ht1]
  have hsz := size_writeRange 0 sym 1 256 t1 (t.size / 4)
  have hin : ∀ k, k < 256 → 4 * (t.size / 4 + k * 1) + 2 < t1.size := by
    intro k hk
    omega
  have hat := slotAt_writeRange (bits := 0) (val := sym) (step := 1) (by decide) hsym 256 t1 (t.size / 4)
  have hroot : ∀ r, r < 256 → slotAt (writeRange 0 sym 1 256 t1 (t.size / 4)) (t.size / 4 + r) = (0, sym) := by
    intro r hr
    rw [hat _ hin, ite_eq_left ⟨r, hr, by omega⟩]
  refine ⟨⟨⟨by rw [hsz, hs1]; omega, ?_⟩, ?_⟩, by rw [hsz, hs1]; omega, ?_, by rw [hsz, hs1]⟩
  · intro r hr hb
    rw [hroot r hr] at hb
    simp at hb
  · intro w
    unfold lookupSlots
    dsimp only
    rw [hroot _ (Nat.mod_lt _ (by decide))]
    exact ⟨rfl, rfl⟩
  · intro q hq
    rw [hat _ hin, ite_eq_right (by
      rintro ⟨k, _, e⟩
      omega), ← ht1]
    exact slotAt_append (by omega)

/-- The slots a code's table takes: the exact size `buildTable` adds to the arena. -/
def tableSlots : PrefixCode → Nat
  | .single _ => 256
  | .canonical lens => 256 + offSum (depths lens) 256

/-- Appends a code's table to the arena. Its slots start at `t.size / 4`. -/
def buildTable (t : ByteArray) : PrefixCode → ByteArray
  | .single sym => buildSingle t sym
  | .canonical lens => buildCanonical t lens

/-- The symbols of a code fit in a slot. -/
def SlotFits : PrefixCode → Prop
  | .single sym => sym < 65536
  | .canonical lens => lens.length ≤ 65536

/-- A built table does its job, takes exactly `tableSlots`, and leaves the tables before it alone. -/
theorem buildTable_spec {t : ByteArray} {c : PrefixCode} (hC : Complete c) (ht : t.size % 4 = 0) (hf : SlotFits c) :
    TableOk (buildTable t c) (t.size / 4) c ∧ (buildTable t c).size % 4 = 0 ∧
      (∀ q, q < t.size / 4 → slotAt (buildTable t c) q = slotAt t q) ∧
      (buildTable t c).size = t.size + 4 * tableSlots c := by
  cases c with
  | single sym =>
    simp only [buildTable, tableSlots]
    exact buildSingle_spec ht hf
  | canonical lens =>
    simp only [buildTable, tableSlots]
    exact buildCanonical_spec hC ht hf

/-- One root slot stays within the array. -/
def rootFits (t : ByteArray) (base r : Nat) : Bool :=
  let e := slotAt t (base + r)
  decide (e.1 ≤ 8) || (decide (e.1 ≤ 15) && decide (4 * (base + 256 + e.2 + 2 ^ (e.1 - 8)) ≤ t.size))

/-- Checks once, when a table is built, what a lookup needs to be safe. Each symbol's lookup then needs no check. -/
def checkFits (t : ByteArray) (base : Nat) : Bool :=
  decide (4 * (base + 256) ≤ t.size) && (List.range 256).all (rootFits t base)

/-- The check says exactly that the table fits, so it never fails on a table `buildTable` built. -/
theorem checkFits_iff (t : ByteArray) (base : Nat) : checkFits t base = true ↔ TableFits t base := by
  unfold checkFits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro r hr hb
    have := h2 r hr
    simp only [rootFits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
    rcases this with h | h
    · omega
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro r hr
    simp only [rootFits, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    by_cases hb : (slotAt t (base + r)).1 ≤ 8
    · exact Or.inl hb
    · exact Or.inr (h2 r hr (by omega))

/-- A table stays correct when the array changes only after it. -/
theorem TableOk.frame {t t' : ByteArray} {base : Nat} {c : PrefixCode} (h : TableOk t base c) (ht : t.size % 4 = 0)
    (hsize : t.size ≤ t'.size) (hframe : ∀ q, q < t.size / 4 → slotAt t' q = slotAt t q) : TableOk t' base c := by
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
