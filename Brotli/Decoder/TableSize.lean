import Brotli.Decoder.Table

/-!
# How big a table is

A complete code's table has 256 root slots and, for each root slot with code words longer than 8 bits, a sub-table as
big as the longest of them needs. The code words of each length lie together, in order, through the code space, so the
code words under a root slot all have one length and fill its sub-table one slot each, except at the at most six root
slots where one length gives way to the next. So a table has at most `1024` slots and one more for each code word longer
than 8 bits, and the builder writes at most that many slots for those code words.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Sums over a range -/

/-- `f 0 + … + f (n - 1)`. -/
def sumR (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumR f n + f n

theorem sumR_zero : ∀ n, sumR (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp only [sumR, sumR_zero n]

theorem sumR_le {f g : Nat → Nat} : ∀ {n : Nat}, (∀ i, i < n → f i ≤ g i) → sumR f n ≤ sumR g n
  | 0, _ => Nat.le_refl _
  | n + 1, h => Nat.add_le_add (sumR_le fun i hi => h i (by omega)) (h n (by omega))

theorem sumR_ge {f : Nat → Nat} : ∀ {n i : Nat}, i < n → f i ≤ sumR f n
  | 0, _, h => absurd h (by omega)
  | n + 1, i, h => by
    simp only [sumR]
    by_cases e : i = n
    · subst e
      omega
    · have := sumR_ge (f := f) (show i < n by omega)
      omega

theorem sumR_add (f g : Nat → Nat) : ∀ n, sumR (fun i => f i + g i) n = sumR f n + sumR g n
  | 0 => rfl
  | n + 1 => by
    simp only [sumR, sumR_add f g n]
    omega

theorem sumR_mul (f : Nat → Nat) (k : Nat) : ∀ n, sumR (fun i => k * f i) n = k * sumR f n
  | 0 => rfl
  | n + 1 => by simp only [sumR, sumR_mul f k n, Nat.mul_add]

theorem sumR_comm (f : Nat → Nat → Nat) (n : Nat) : ∀ m, sumR (fun r => sumR (fun j => f r j) n) m = sumR (fun j => sumR (fun r => f r j) m) n
  | 0 => (sumR_zero n).symm
  | m + 1 => by
    simp only [sumR]
    rw [sumR_comm f n m, ← sumR_add]

theorem sumR_one (k : Nat) : ∀ m, sumR (fun r => if r = k then 1 else 0) m = if k < m then 1 else 0
  | 0 => by simp [sumR]
  | m + 1 => by
    simp only [sumR, sumR_one k m]
    by_cases h1 : k < m
    · rw [ite_eq_left h1, ite_eq_left (show k < m + 1 by omega), ite_eq_right (show ¬m = k by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : m = k
      · rw [ite_eq_left h2, ite_eq_left (show k < m + 1 by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬k < m + 1 by omega)]

/-- Counting by a key below `m`: the count is the sum of the counts for each key. -/
theorem countP_split {α : Type} (P : α → Bool) (key : α → Nat) (m : Nat) :
    ∀ (L : List α), (∀ a ∈ L, P a = true → key a < m) →
      L.countP P = sumR (fun r => L.countP (fun a => P a && key a == r)) m
  | [], _ => (sumR_zero m).symm
  | a :: L, h => by
    rw [List.countP_cons, countP_split P key m L (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    simp only [List.countP_cons]
    rw [sumR_add]
    by_cases hp : P a = true
    · have e : (fun r => if (P a && key a == r) = true then 1 else 0) = fun r => if r = key a then 1 else 0 := by
        funext r
        simp only [hp, Bool.true_and, beq_iff_eq]
        by_cases hr : key a = r
        · rw [ite_eq_left hr, ite_eq_left hr.symm]
        · rw [ite_eq_right hr, ite_eq_right (fun e => hr e.symm)]
      rw [e, sumR_one, ite_eq_left (h a (by simp) hp), ite_eq_left hp]
    · have e : (fun r => if (P a && key a == r) = true then 1 else 0) = fun _ => 0 := by
        funext r
        simp [hp]
      rw [e, ite_eq_right hp, sumR_zero]

/-! ### Where code words lie -/

/-- A symbol's place among the symbols of its length. -/
def idxOf (lens : List Nat) (s l : Nat) : Nat := ((lens.take s).filter (· == l)).length

theorem code_eq {lens : List Nat} {s l : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0) :
    code lens s = some (nextCode lens l + idxOf lens s l) := by
  simp [code, hs, h0, idxOf]

theorem idxOf_lt {lens : List Nat} {s l : Nat} (hs : lens[s]? = some l) (h0 : l ≠ 0) : idxOf lens s l < blCount lens l := by
  unfold idxOf blCount
  rw [ite_eq_right h0]
  conv => rhs; rw [← List.take_append_drop s lens]
  rw [List.filter_append, List.length_append]
  have h0' : (lens.drop s)[0]? = some l := by rw [List.getElem?_drop, Nat.add_zero]; exact hs
  have hmem : l ∈ (lens.drop s).filter (· == l) := List.mem_filter.mpr ⟨List.mem_of_getElem? h0', by simp⟩
  have := List.length_pos_of_mem hmem
  omega

theorem idxOf_succ (lens : List Nat) (k l : Nat) :
    idxOf lens (k + 1) l = idxOf lens k l + (if lens[k]? = some l then 1 else 0) := by
  unfold idxOf
  rw [List.take_add_one, List.filter_append, List.length_append]
  cases h : lens[k]? with
  | none => simp
  | some v =>
    by_cases hv : v = l
    · subst hv
      simp
    · simp [hv]

theorem idxOf_length (lens : List Nat) {l : Nat} (h0 : l ≠ 0) : idxOf lens lens.length l = blCount lens l := by
  unfold idxOf blCount
  rw [List.take_length, ite_eq_right h0]

/-- The symbols of length `l` with their places among that length in a set are as many as the places in it below the
number of symbols of that length. -/
theorem countP_idx (lens : List Nat) (l : Nat) (P : Nat → Bool) : ∀ k, k ≤ lens.length →
    (List.range k).countP (fun s => lens[s]? == some l && P (idxOf lens s l)) = (List.range (idxOf lens k l)).countP P
  | 0, _ => by simp [idxOf]
  | k + 1, hk => by
    rw [List.range_succ, List.countP_append, countP_idx lens l P k (by omega), idxOf_succ]
    cases h : lens[k]? with
    | none => simp [h]
    | some v =>
      by_cases hv : v = l
      · subst hv
        rw [ite_eq_left rfl, List.range_succ, List.countP_append]
        simp [h]
      · simp [h, hv]

/-- The code words of lengths up to `l - 1` take the code space before the first code word of length `l`. -/
theorem nextCode_pos (lens : List Nat) : ∀ l, 1 ≤ l → l ≤ 15 → nextCode lens l * 2 ^ (15 - l) = sumUpTo lens (l - 1)
  | 0, h, _ => by omega
  | 1, _, _ => by simp [nextCode, blCount, sumUpTo]
  | l + 2, _, h => by
    rw [show nextCode lens (l + 2) = (nextCode lens (l + 1) + blCount lens (l + 1)) <<< 1 from rfl, Nat.shiftLeft_eq,
      show l + 2 - 1 = l + 1 by omega, ← nextCode_sum lens (l + 1) (by omega) (by omega),
      show 15 - (l + 1) = (15 - (l + 2)) + 1 by omega, Nat.pow_succ]
    grind

theorem sumUpTo_succ (lens : List Nat) (l : Nat) : sumUpTo lens (l + 1) = sumUpTo lens l + blCount lens (l + 1) * 2 ^ (15 - (l + 1)) :=
  rfl

theorem sumUpTo_mono (lens : List Nat) : ∀ {a b : Nat}, a ≤ b → sumUpTo lens a ≤ sumUpTo lens b
  | a, b, h => by
    induction b with
    | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
    | succ b ih =>
      by_cases hab : a = b + 1
      · rw [hab]; exact Nat.le_refl _
      · have := ih (by omega)
        rw [sumUpTo_succ]
        omega

/-- The code space before the code words of length `l` is whole blocks of `2 ^ (15 - (l - 1))`. -/
theorem sumUpTo_dvd (lens : List Nat) : ∀ k, k ≤ 15 → 2 ^ (15 - k) ∣ sumUpTo lens k
  | 0, _ => ⟨0, rfl⟩
  | k + 1, h => by
    rw [sumUpTo_succ]
    have ih := sumUpTo_dvd lens k (by omega)
    have h1 : 2 ^ (15 - (k + 1)) ∣ 2 ^ (15 - k) := Nat.pow_dvd_pow 2 (by omega)
    exact Nat.dvd_add (Nat.dvd_trans h1 ih) (Nat.dvd_mul_left _ _)

/-- A code word's place in the code space: its value, left-aligned to 15 bits. -/
def posOf (lens : List Nat) (s l : Nat) : Nat := sumUpTo lens (l - 1) + idxOf lens s l * 2 ^ (15 - l)

/-- A long code word's root slot, from its place. -/
theorem revBits_mod256 : ∀ (k c : Nat), revBits (8 + k) c % 256 = revBits 8 (c / 2 ^ k)
  | 0, c => by
    rw [Nat.add_zero, Nat.pow_zero, Nat.div_one]
    exact Nat.mod_eq_of_lt (revBits_lt 8 c)
  | k + 1, c => by
    rw [show 8 + (k + 1) = (8 + k) + 1 by omega, revBits, show c / 2 ^ (k + 1) = c / 2 / 2 ^ k by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm], ← revBits_mod256 k (c / 2)]
    rw [show c % 2 * 2 ^ (8 + k) = 256 * (c % 2 * 2 ^ k) by rw [Nat.pow_add]; grind]
    omega

theorem rootOf_pos {lens : List Nat} {s l : Nat} (h8 : 9 ≤ l) (h15 : l ≤ 15) :
    rootOf l (nextCode lens l + idxOf lens s l) = revBits 8 (posOf lens s l / 128) := by
  unfold rootOf posOf
  have hk : l = 8 + (l - 8) := by omega
  rw [hk, revBits_mod256, ← hk]
  congr 1
  rw [← nextCode_pos lens l (by omega) h15, ← Nat.add_mul, show (128 : Nat) = 2 ^ (15 - l) * 2 ^ (l - 8) by
    rw [← Nat.pow_add, show 15 - l + (l - 8) = 7 by omega], Nat.mul_comm (nextCode lens l + idxOf lens s l),
    Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]

theorem revBits8_inv {x : Nat} (h : x < 256) : revBits 8 (revBits 8 x) = x := revBits_revBits h

/-! ### Depths, attained -/

/-- A root slot's depth is that of a code word under it. -/
theorem depths_attain {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) :
    ∀ r, (depths lens).getD r 0 ≠ 0 → ∃ s l c, Long lens s l c ∧ rootOf l c = r ∧ (depths lens).getD r 0 = l - 8 := by
  have key := foldCodes_ind (f := recordDepth) hl
    (fun s D => D.size = 256 ∧ ∀ r, D.getD r 0 ≠ 0 → ∃ s' l c, s' < s ∧ Long lens s' l c ∧ rootOf l c = r ∧ D.getD r 0 = l - 8)
    (by
      rintro s D ⟨h1, h3⟩ _
      refine ⟨h1, fun r hr => ?_⟩
      obtain ⟨s', l, c, hs, hL, he, hd⟩ := h3 r hr
      exact ⟨s', l, c, by omega, hL, he, hd⟩)
    (by
      rintro s l D ⟨h1, h3⟩ hg h0
      have hc : code lens s = some (nextCode lens l + idxOf lens s l) := code_eq hg h0
      simp only [hc, Option.getD_some]
      unfold recordDepth
      split
      · refine ⟨h1, fun r hr => ?_⟩
        obtain ⟨s', l', c', hs, hL, he, hd⟩ := h3 r hr
        exact ⟨s', l', c', by omega, hL, he, hd⟩
      · rename_i hs8
        have hroot : rootOf l (nextCode lens l + idxOf lens s l) < D.size := by
          have := rootOf_lt l (nextCode lens l + idxOf lens s l)
          omega
        refine ⟨by simpa using h1, fun r hr => ?_⟩
        have hg' : ∀ {v : Nat}, (D.setIfInBounds (rootOf l (nextCode lens l + idxOf lens s l)) v).getD r 0 =
            if r = rootOf l (nextCode lens l + idxOf lens s l) then v else D.getD r 0 := by
          intro v
          by_cases h : r = rootOf l (nextCode lens l + idxOf lens s l)
          · subst h
            simp [Array.getD_eq_getD_getElem?, hroot]
          · simp [Array.getD_eq_getD_getElem?, h, Ne.symm h]
        rw [hg'] at hr ⊢
        by_cases he : r = rootOf l (nextCode lens l + idxOf lens s l)
        · rw [ite_eq_left he] at hr ⊢
          by_cases hm : D.getD (rootOf l (nextCode lens l + idxOf lens s l)) 0 ≤ l - 8
          · exact ⟨s, l, _, by omega, ⟨hg, by omega, hc⟩, he.symm, by rw [Nat.max_eq_right hm]⟩
          · have hne : D.getD (rootOf l (nextCode lens l + idxOf lens s l)) 0 ≠ 0 := by omega
            obtain ⟨s', l', c', hs, hL, he', hd⟩ := h3 _ hne
            exact ⟨s', l', c', by omega, hL, by rw [he', he], by rw [Nat.max_eq_left (by omega), hd]⟩
        · rw [ite_eq_right he] at hr ⊢
          obtain ⟨s', l', c', hs, hL, he', hd⟩ := h3 r hr
          exact ⟨s', l', c', by omega, hL, he', hd⟩)
    (acc := Array.replicate 256 0)
    (by
      refine ⟨by simp, fun r hr => ?_⟩
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate] at hr
      split at hr <;> simp at hr)
  intro r hr
  obtain ⟨s, l, c, _, hL, he, hd⟩ := key.2 r hr
  exact ⟨s, l, c, hL, he, hd⟩

/-! ### Counting code words in a block of the code space -/

/-- Of `cnt` places `a, a + w, …`, those in the block of 128 from `x`, each worth `w`, are the block's overlap with them,
when `w` divides `a`, `x` and 128. -/
theorem count_block {w a x : Nat} (hw : 0 < w) (ha : w ∣ a) (hx : w ∣ x) (h128 : w ∣ 128) : ∀ cnt,
    (List.range cnt).countP (fun j => x ≤ a + j * w && a + j * w < x + 128) * w = min (a + cnt * w) (x + 128) - max a x
  | 0 => by simp; omega
  | cnt + 1 => by
    rw [List.range_succ, List.countP_append, Nat.add_mul (List.countP _ (List.range cnt)), count_block hw ha hx h128 cnt,
      show a + (cnt + 1) * w = a + cnt * w + w by rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]]
    obtain ⟨e, he⟩ : w ∣ a + cnt * w := Nat.dvd_add ha (Nat.dvd_mul_left _ _)
    obtain ⟨f, hf⟩ : w ∣ x + 128 := Nat.dvd_add hx h128
    obtain ⟨g, hg⟩ := hx
    simp only [List.countP_singleton]
    by_cases hin : x ≤ a + cnt * w ∧ a + cnt * w < x + 128
    · have hle : e + 1 ≤ f := by
        have : w * e < w * f := by rw [← he, ← hf]; exact hin.2
        exact Nat.lt_of_mul_lt_mul_left this
      have : w * (e + 1) ≤ w * f := Nat.mul_le_mul_left _ hle
      rw [Nat.mul_add, Nat.mul_one, ← he, ← hf] at this
      simp only [hin, decide_true, Bool.and_self, ↓reduceIte, Nat.one_mul]
      omega
    · by_cases hlo : a + cnt * w < x
      · have hle : e + 1 ≤ g := by
          have : w * e < w * g := by rw [← he, ← hg]; exact hlo
          exact Nat.lt_of_mul_lt_mul_left this
        have : w * (e + 1) ≤ w * g := Nat.mul_le_mul_left _ hle
        rw [Nat.mul_add, Nat.mul_one, ← he, ← hg] at this
        have hf : ¬(x ≤ a + cnt * w) := by omega
        simp only [hf, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
        omega
      · have hhi : ¬(a + cnt * w < x + 128) := by omega
        simp only [hhi, decide_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
        omega

/-- The code words of length `l` whose root slot is `r`. -/
def cntL (lens : List Nat) (l r : Nat) : Nat :=
  (List.range lens.length).countP (fun s => lens[s]? == some l && revBits 8 (posOf lens s l / 128) == r)

/-- A place in the code space below its end is in the block of its root slot. -/
theorem block_iff {y r : Nat} (hy : y < 32768) (hr : r < 256) :
    revBits 8 (y / 128) = r ↔ 128 * revBits 8 r ≤ y ∧ y < 128 * revBits 8 r + 128 := by
  have hb : y / 128 < 256 := by omega
  constructor
  · intro e
    have : y / 128 = revBits 8 r := by rw [← e, revBits8_inv hb]
    omega
  · intro h
    have : y / 128 = revBits 8 r := by omega
    rw [this, revBits8_inv hr]

theorem cntL_eq (lens : List Nat) {l r : Nat} (h9 : 9 ≤ l) (h15 : l ≤ 15) (hr : r < 256) (hS : sumUpTo lens l ≤ 32768) :
    cntL lens l r * 2 ^ (15 - l) =
      min (sumUpTo lens l) (128 * revBits 8 r + 128) - max (sumUpTo lens (l - 1)) (128 * revBits 8 r) := by
  unfold cntL posOf
  rw [countP_idx lens l (fun j => revBits 8 ((sumUpTo lens (l - 1) + j * 2 ^ (15 - l)) / 128) == r) lens.length (Nat.le_refl _),
    idxOf_length lens (by omega)]
  have hsu : sumUpTo lens l = sumUpTo lens (l - 1) + blCount lens l * 2 ^ (15 - l) := by
    have := sumUpTo_succ lens (l - 1)
    rw [show l - 1 + 1 = l by omega] at this
    exact this
  have e : (List.range (blCount lens l)).countP (fun j => revBits 8 ((sumUpTo lens (l - 1) + j * 2 ^ (15 - l)) / 128) == r) =
      (List.range (blCount lens l)).countP (fun j => 128 * revBits 8 r ≤ sumUpTo lens (l - 1) + j * 2 ^ (15 - l) &&
        sumUpTo lens (l - 1) + j * 2 ^ (15 - l) < 128 * revBits 8 r + 128) := by
    apply List.countP_congr
    intro j hj
    have hj' : j < blCount lens l := List.mem_range.mp hj
    have hlt : j * 2 ^ (15 - l) + 2 ^ (15 - l) ≤ blCount lens l * 2 ^ (15 - l) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hj'
    have hpos : 0 < 2 ^ (15 - l) := Nat.two_pow_pos _
    have hy : sumUpTo lens (l - 1) + j * 2 ^ (15 - l) < 32768 := by omega
    simp only [beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    exact block_iff hy hr
  rw [e, count_block (Nat.two_pow_pos _) (sumUpTo_dvd lens (l - 1) (by omega) |> Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)))
    (Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 (show 15 - l ≤ 7 by omega)) _)
    (show 2 ^ (15 - l) ∣ 128 from Nat.pow_dvd_pow 2 (show 15 - l ≤ 7 by omega)), ← hsu]

/-- How many places where one length gives way to the next lie inside root slot `r`'s block. -/
def mixC (lens : List Nat) (r : Nat) : Nat :=
  sumR (fun j => if 128 * revBits 8 r < sumUpTo lens (j + 9) ∧ sumUpTo lens (j + 9) < 128 * revBits 8 r + 128 then 1 else 0) 6

/-- The code words longer than 8 bits under root slot `r`. -/
def cntR (lens : List Nat) (r : Nat) : Nat := sumR (fun j => cntL lens (j + 9) r) 7

/-- A root slot's sub-table is as big as its code words, unless a place where one length gives way to the next lies
inside it. -/
theorem subSize_root {lens : List Nat} (hC : Complete (.canonical lens)) {r : Nat} (hr : r < 256) :
    subSize ((depths lens).getD r 0) ≤ cntR lens r + 128 * mixC lens r := by
  obtain ⟨hl, hsum⟩ := hC
  have h15 : sumUpTo lens 15 = 32768 := by rw [sumUpTo_eq lens hl, hsum]
  have hmono : ∀ k, sumUpTo lens k ≤ 32768 ∨ 15 < k := fun k => by
    by_cases hk : k ≤ 15
    · exact Or.inl (h15 ▸ sumUpTo_mono lens hk)
    · exact Or.inr (by omega)
  by_cases hD : (depths lens).getD r 0 = 0
  · rw [hD]
    simp [subSize]
  obtain ⟨s0, l0, c0, ⟨hs0, h8, hc0⟩, hroot, hd⟩ := depths_attain hl r hD
  have hl15 : l0 ≤ 15 := hl l0 (List.mem_of_getElem? hs0)
  have h7 := (depths_spec hl).2.1 r
  by_cases hm : 1 ≤ mixC lens r
  · have : subSize ((depths lens).getD r 0) ≤ 128 := by
      unfold subSize
      rw [ite_eq_right hD]
      have : 2 ^ (depths lens).getD r 0 ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) h7
      exact this
    have : 128 ≤ 128 * mixC lens r := by omega
    omega
  · have hm0 : mixC lens r = 0 := by omega
    have hno : ∀ j, j < 6 → ¬(128 * revBits 8 r < sumUpTo lens (j + 9) ∧ sumUpTo lens (j + 9) < 128 * revBits 8 r + 128) := by
      intro j hj hin
      have : 1 ≤ mixC lens r := by
        unfold mixC
        have h1 : ∀ i, i < 6 → (if i = j then 1 else 0) ≤
            (if 128 * revBits 8 r < sumUpTo lens (i + 9) ∧ sumUpTo lens (i + 9) < 128 * revBits 8 r + 128 then 1 else 0) := by
          intro i _
          by_cases e : i = j
          · subst e
            rw [ite_eq_left rfl, ite_eq_left hin]
            exact Nat.le_refl _
          · rw [ite_eq_right e]
            exact Nat.zero_le _
        have := sumR_le h1
        rw [sumR_one, ite_eq_left hj] at this
        exact this
      omega
    -- The place of the deepest code word under the root slot.
    rw [code_eq hs0 (by omega)] at hc0
    have hc0' := Option.some.inj hc0
    rw [← hc0', rootOf_pos h8 hl15] at hroot
    have hi := idxOf_lt hs0 (by omega)
    have hsu : sumUpTo lens l0 = sumUpTo lens (l0 - 1) + blCount lens l0 * 2 ^ (15 - l0) := by
      have := sumUpTo_succ lens (l0 - 1)
      rw [show l0 - 1 + 1 = l0 by omega] at this
      exact this
    have hlt : idxOf lens s0 l0 * 2 ^ (15 - l0) + 2 ^ (15 - l0) ≤ blCount lens l0 * 2 ^ (15 - l0) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hi
    have hSl0 : sumUpTo lens l0 ≤ 32768 := h15 ▸ sumUpTo_mono lens hl15
    have hw : 0 < 2 ^ (15 - l0) := Nat.two_pow_pos _
    have hpos : posOf lens s0 l0 < 32768 := by unfold posOf; omega
    obtain ⟨hb1, hb2⟩ := (block_iff hpos hr).mp hroot
    unfold posOf at hb1 hb2
    have hB : revBits 8 r < 256 := revBits_lt 8 r
    -- The block lies within the code words of length `l0`.
    have hA : sumUpTo lens (l0 - 1) ≤ 128 * revBits 8 r := by
      by_cases h9 : l0 = 9
      · subst h9
        obtain ⟨q, hq⟩ := sumUpTo_dvd lens 8 (by decide)
        rw [show (2 : Nat) ^ (15 - 8) = 128 from rfl] at hq
        rw [show 9 - 1 = 8 from rfl] at hb1 hb2 ⊢
        omega
      · have := hno (l0 - 10) (by omega)
        rw [show l0 - 10 + 9 = l0 - 1 by omega] at this
        omega
    have hB2 : 128 * revBits 8 r + 128 ≤ sumUpTo lens l0 := by
      by_cases h15' : l0 = 15
      · subst h15'
        omega
      · have := hno (l0 - 9) (by omega)
        rw [show l0 - 9 + 9 = l0 by omega] at this
        omega
    have hcnt := cntL_eq lens (r := r) h8 hl15 hr hSl0
    rw [Nat.min_eq_right hB2, Nat.max_eq_right hA, Nat.add_sub_cancel_left] at hcnt
    have hpow : (128 : Nat) = 2 ^ (l0 - 8) * 2 ^ (15 - l0) := by
      rw [← Nat.pow_add, show l0 - 8 + (15 - l0) = 7 by omega]
    rw [hpow] at hcnt
    have hc := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hcnt
    unfold subSize
    rw [ite_eq_right hD, hd, ← hc]
    have := sumR_ge (f := fun j => cntL lens (j + 9) r) (show l0 - 9 < 7 by omega)
    rw [show l0 - 9 + 9 = l0 by omega] at this
    unfold cntR
    omega

/-- The code words longer than 8 bits. -/
def longCount (lens : List Nat) : Nat := sumR (fun j => blCount lens (j + 9)) 7

theorem offSum_eq (D : Array Nat) : ∀ n, offSum D n = sumR (fun i => subSize (D.getD i 0)) n
  | 0 => rfl
  | n + 1 => by simp only [offSum, sumR, offSum_eq D n]

/-- Each code word of a length is under one root slot. -/
theorem cntL_sum (lens : List Nat) {l : Nat} (h0 : l ≠ 0) : sumR (fun r => cntL lens l r) 256 = blCount lens l := by
  have hs := countP_split (fun s => lens[s]? == some l) (fun s => revBits 8 (posOf lens s l / 128)) 256 (List.range lens.length)
    (fun s _ _ => revBits_lt 8 _)
  have hc := countP_idx lens l (fun _ => true) lens.length (Nat.le_refl _)
  simp only [Bool.and_true, List.countP_true, List.length_range] at hc
  rw [idxOf_length lens h0] at hc
  unfold cntL
  rw [← hs, hc]

/-- At most six root slots hold a place where one length gives way to the next. -/
theorem mixC_sum (lens : List Nat) : sumR (fun r => mixC lens r) 256 ≤ 6 := by
  unfold mixC
  rw [sumR_comm]
  have h : ∀ j, j < 6 → sumR (fun r => if 128 * revBits 8 r < sumUpTo lens (j + 9) ∧ sumUpTo lens (j + 9) < 128 * revBits 8 r + 128 then 1 else 0) 256 ≤ 1 := by
    intro j _
    have hle : ∀ r, r < 256 → (if 128 * revBits 8 r < sumUpTo lens (j + 9) ∧ sumUpTo lens (j + 9) < 128 * revBits 8 r + 128 then 1 else 0) ≤
        (if r = revBits 8 (sumUpTo lens (j + 9) / 128) then 1 else 0) := by
      intro r hr
      by_cases hc : 128 * revBits 8 r < sumUpTo lens (j + 9) ∧ sumUpTo lens (j + 9) < 128 * revBits 8 r + 128
      · have e : sumUpTo lens (j + 9) / 128 = revBits 8 r := by omega
        rw [ite_eq_left hc, ite_eq_left (by rw [e, revBits8_inv hr])]
        exact Nat.le_refl _
      · rw [ite_eq_right hc]
        exact Nat.zero_le _
    have := sumR_le hle
    rw [sumR_one] at this
    split at this <;> omega
  have := sumR_le h
  have h6 : sumR (fun _ => 1) 6 = 6 := rfl
  omega

/-- A complete code's sub-tables take at most one slot for each code word longer than 8 bits, and 768 more. -/
theorem offSum_le {lens : List Nat} (hC : Complete (.canonical lens)) : offSum (depths lens) 256 ≤ longCount lens + 768 := by
  rw [offSum_eq]
  have h1 := sumR_le (n := 256) (f := fun r => subSize ((depths lens).getD r 0)) (g := fun r => cntR lens r + 128 * mixC lens r)
    (fun r hr => subSize_root hC hr)
  rw [sumR_add, sumR_mul] at h1
  have h2 : sumR (cntR lens) 256 = longCount lens := by
    show sumR (fun r => sumR (fun j => cntL lens (j + 9) r) 7) 256 = _
    unfold longCount
    rw [sumR_comm]
    congr 1
    funext j
    exact cntL_sum lens (by omega)
  have h3 : sumR (mixC lens) 256 ≤ 6 := mixC_sum lens
  have h4 : sumR (fun r => subSize ((depths lens).getD r 0)) 256 ≤ sumR (cntR lens) 256 + 128 * sumR (mixC lens) 256 := h1
  omega

/-! ### The slots the builder writes -/

/-- How many slots the builder writes for a code word of length `l` under root slot `r`: its root slots for a short one,
its share of its sub-table for a long one. -/
def fillCnt (lens : List Nat) (l r : Nat) : Nat := if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD r 0 - (l - 8))

theorem sumR_oneG (g : Nat → Nat) (k : Nat) : ∀ n, sumR (fun r => if r = k then g r else 0) n = if k < n then g k else 0
  | 0 => by simp [sumR]
  | n + 1 => by
    simp only [sumR, sumR_oneG g k n]
    by_cases h1 : k < n
    · rw [ite_eq_left h1, ite_eq_left (show k < n + 1 by omega), ite_eq_right (show ¬n = k by omega)]
      omega
    · rw [ite_eq_right h1]
      by_cases h2 : n = k
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left (show n < n + 1 by omega)]
        omega
      · rw [ite_eq_right h2, ite_eq_right (show ¬k < n + 1 by omega)]

/-- A sum over a list, of a value that depends only on a key below `m`, is a sum over the keys. -/
theorem sum_split {α : Type} (P : α → Bool) (key : α → Nat) (g : Nat → Nat) (m : Nat) :
    ∀ (L : List α), (∀ a ∈ L, P a = true → key a < m) →
      (L.map fun a => if P a then g (key a) else 0).sum = sumR (fun r => L.countP (fun a => P a && key a == r) * g r) m
  | [], _ => by simp only [List.map_nil, List.sum_nil, List.countP_nil, Nat.zero_mul]; exact (sumR_zero m).symm
  | a :: L, h => by
    rw [List.map_cons, List.sum_cons, sum_split P key g m L (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    have e : ∀ r, (a :: L).countP (fun a => P a && key a == r) * g r =
        (if r = key a ∧ P a = true then g r else 0) + L.countP (fun a => P a && key a == r) * g r := by
      intro r
      rw [List.countP_cons, Nat.add_mul]
      by_cases hp : P a = true
      · by_cases hr : r = key a
        · subst hr
          simp [hp]
          omega
        · simp [hp, hr, Ne.symm hr]
      · simp [hp]
    simp only [e]
    rw [sumR_add]
    by_cases hp : P a = true
    · have : sumR (fun r => if r = key a ∧ P a = true then g r else 0) m = g (key a) := by
        have hk := h a (by simp) hp
        have hf : (fun r => if r = key a ∧ P a = true then g r else 0) = fun r => if r = key a then g r else 0 := by
          funext r
          simp [hp]
        rw [hf, sumR_oneG, ite_eq_left hk]
      rw [this, ite_eq_left hp]
    · have : sumR (fun r => if r = key a ∧ P a = true then g r else 0) m = 0 := by
        have : (fun r => if r = key a ∧ P a = true then g r else 0) = fun _ => 0 := by
          funext r
          simp [hp]
        rw [this, sumR_zero]
      rw [this, ite_eq_right hp]

/-- The code words of a length under a root slot are no deeper than its sub-table. -/
theorem cntL_deep {lens : List Nat} (hl : ∀ l ∈ lens, l ≤ 15) {l r : Nat} (h9 : 9 ≤ l) (h15 : l ≤ 15)
    (h : cntL lens l r ≠ 0) : l - 8 ≤ (depths lens).getD r 0 := by
  unfold cntL at h
  obtain ⟨s, hs, hp⟩ := List.countP_pos_iff.mp (Nat.pos_of_ne_zero h)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨hs1, hs2⟩ := hp
  have hc := code_eq hs1 (by omega)
  have := (depths_spec hl).2.2.2 s l _ ⟨hs1, by omega, hc⟩
  rw [rootOf_pos h9 h15, hs2] at this
  exact this

/-- The code words of the lengths from 9 under a root slot take at most its block of the code space. -/
theorem mass_root {lens : List Nat} (hC : Complete (.canonical lens)) {r : Nat} (hr : r < 256) :
    sumR (fun j => cntL lens (j + 9) r * 2 ^ (15 - (j + 9))) 7 ≤ 128 := by
  obtain ⟨hl, hsum⟩ := hC
  have h15 : sumUpTo lens 15 = 32768 := by rw [sumUpTo_eq lens hl, hsum]
  have key : ∀ k, k ≤ 7 → sumR (fun j => cntL lens (j + 9) r * 2 ^ (15 - (j + 9))) k ≤
      min (sumUpTo lens (k + 8)) (128 * revBits 8 r + 128) - 128 * revBits 8 r := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have e := cntL_eq lens (l := k + 9) (r := r) (by omega) (by omega) hr (h15 ▸ sumUpTo_mono lens (by omega))
      rw [show k + 9 - 1 = k + 8 by omega] at e
      have hm := sumUpTo_mono lens (show k + 8 ≤ k + 9 by omega)
      simp only [sumR]
      have := ih (by omega)
      rw [show k + 1 + 8 = k + 9 by omega]
      omega
  have := key 7 (Nat.le_refl _)
  omega

/-- A root slot's code words longer than 8 bits fill at most its sub-table. -/
theorem fill_root {lens : List Nat} (hC : Complete (.canonical lens)) {r : Nat} (hr : r < 256) :
    sumR (fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) 7 ≤ subSize ((depths lens).getD r 0) := by
  have hl := hC.1
  have hm := mass_root hC hr
  have h7 := (depths_spec hl).2.1 r
  generalize hD : (depths lens).getD r 0 = D at h7
  have hdeep : ∀ j, j < 7 → cntL lens (j + 9) r ≠ 0 → j + 1 ≤ D := by
    intro j hj h
    have := cntL_deep hl (l := j + 9) (r := r) (by omega) (by omega) h
    omega
  -- Each term, scaled to the code space, is that length's share of the block.
  have hscale : ∀ j, j < 7 → 2 ^ (7 - D) * (cntL lens (j + 9) r * fillCnt lens (j + 9) r) = cntL lens (j + 9) r * 2 ^ (15 - (j + 9)) := by
    intro j hj
    by_cases h0 : cntL lens (j + 9) r = 0
    · rw [h0]
      simp
    · have hjD := hdeep j hj h0
      unfold fillCnt
      rw [ite_eq_right (by omega), hD, Nat.mul_left_comm, ← Nat.pow_add, show 7 - D + (D - (j + 9 - 8)) = 15 - (j + 9) by omega]
  have hsum : 2 ^ (7 - D) * sumR (fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) 7 =
      sumR (fun j => cntL lens (j + 9) r * 2 ^ (15 - (j + 9))) 7 := by
    rw [← sumR_mul]
    have : ∀ (f g : Nat → Nat) (n : Nat), (∀ i, i < n → f i = g i) → sumR f n = sumR g n := by
      intro f g n h
      induction n with
      | zero => rfl
      | succ n ih => simp only [sumR, ih (fun i hi => h i (by omega)), h n (by omega)]
    exact this _ _ 7 hscale
  by_cases hD0 : D = 0
  · subst hD0
    have : ∀ j, j < 7 → cntL lens (j + 9) r * fillCnt lens (j + 9) r = 0 := by
      intro j hj
      by_cases h0 : cntL lens (j + 9) r = 0
      · rw [h0, Nat.zero_mul]
      · exact absurd (hdeep j hj h0) (by omega)
    have hz : sumR (fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) 7 = 0 := by
      have := sumR_le (n := 7) (f := fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) (g := fun _ => 0)
        (fun i hi => Nat.le_of_eq (this i hi))
      rw [sumR_zero] at this
      omega
    rw [hz]
    exact Nat.zero_le _
  · unfold subSize
    rw [ite_eq_right hD0]
    have h128 : (128 : Nat) = 2 ^ (7 - D) * 2 ^ D := by rw [← Nat.pow_add, show 7 - D + D = 7 by omega]
    rw [hsum.symm, h128] at hm
    exact Nat.le_of_mul_le_mul_left hm (Nat.two_pow_pos _)

/-- The builder writes at most one slot for each code word longer than 8 bits, and 1024 more. -/
theorem fill_le {lens : List Nat} (hC : Complete (.canonical lens)) :
    sumR (fun j => blCount lens (j + 1) * 2 ^ (8 - (j + 1))) 8 +
      sumR (fun r => sumR (fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) 7) 256 ≤ longCount lens + 1024 := by
  have hl := hC.1
  -- The short code words fill the root at most once.
  have hshort : sumR (fun j => blCount lens (j + 1) * 2 ^ (8 - (j + 1))) 8 ≤ 256 := by
    have h8 : 128 * sumR (fun j => blCount lens (j + 1) * 2 ^ (8 - (j + 1))) 8 = sumUpTo lens 8 := by
      have : ∀ k, k ≤ 8 → 128 * sumR (fun j => blCount lens (j + 1) * 2 ^ (8 - (j + 1))) k = sumUpTo lens k := by
        intro k
        induction k with
        | zero => intro _; rfl
        | succ k ih =>
          intro hk
          simp only [sumR, Nat.mul_add, ih (by omega), sumUpTo_succ]
          rw [Nat.mul_left_comm, show (128 : Nat) * 2 ^ (8 - (k + 1)) = 2 ^ (15 - (k + 1)) by
            rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add, show 7 + (8 - (k + 1)) = 15 - (k + 1) by omega]]
      exact this 8 (Nat.le_refl _)
    have h15 : sumUpTo lens 15 = 32768 := by rw [sumUpTo_eq lens hl, hC.2]
    have := sumUpTo_mono lens (show 8 ≤ 15 by omega)
    omega
  have hlong := sumR_le (n := 256) (f := fun r => sumR (fun j => cntL lens (j + 9) r * fillCnt lens (j + 9) r) 7)
    (g := fun r => subSize ((depths lens).getD r 0)) (fun r hr => fill_root hC hr)
  rw [← offSum_eq] at hlong
  have := offSum_le hC
  omega

/-- A complete code's table has at most 1024 slots and one for each code word longer than 8 bits. -/
theorem tableSlots_le {lens : List Nat} (hC : Complete (.canonical lens)) : tableSlots (.canonical lens) ≤ longCount lens + 1024 := by
  have := offSum_le hC
  show 256 + offSum (depths lens) 256 ≤ _
  omega

end Brotli.Decoder
