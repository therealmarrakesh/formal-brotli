module

public import Brotli.Decoder.Copy
public import Brotli.Decoder.CmdLut
public import Brotli.Decoder.FastTab

@[expose] public section

/-!
# Dictionary words in byte arrays

The spec keeps the dictionary as one number per line of the RFC and its transforms as a list of strings. Here the same
data is in byte arrays built once, and a word is built in a byte array from fixed-width values. `dictBuild_spec` proves
that word is the spec's `dictionaryWord`. The code takes the arrays as parameters, so that no proof mentions a constant
the kernel would try to evaluate.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The dictionary's bytes -/

/-- A line's 32 bytes, first the most significant. -/
def lineBytes (line : Nat) : List UInt8 :=
  (List.range 32).map fun j => ((line >>> (8 * (31 - j))) &&& 255).toUInt8

/-- The dictionary's bytes. -/
def dictBytes : ByteArray :=
  (dictLines.flatMap lineBytes).toByteArray

private theorem length_lineBytes (line : Nat) : (lineBytes line).length = 32 := by
  simp [lineBytes]

private theorem flatMap_length : ∀ l : List Nat, (l.flatMap lineBytes).length = l.length * 32
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, length_lineBytes, flatMap_length xs, List.length_cons]
    omega

private theorem flatMap_get : ∀ (l : List Nat) (i : Nat), i / 32 < l.length →
    (l.flatMap lineBytes)[i]? = some ((l.getD (i / 32) 0 >>> (8 * (31 - i % 32))) &&& 255).toUInt8
  | [], _, h => by simp at h
  | x :: xs, i, h => by
    rw [List.flatMap_cons]
    by_cases hi : i < 32
    · rw [List.getElem?_append_left (by rw [length_lineBytes]; exact hi)]
      have h1 : i / 32 = 0 := by omega
      have h2 : i % 32 = i := by omega
      rw [h1, h2]
      simp [lineBytes, hi]
    · rw [List.getElem?_append_right (by rw [length_lineBytes]; omega), length_lineBytes,
        flatMap_get xs (i - 32) (by simp only [List.length_cons] at h; omega)]
      have h1 : i / 32 = (i - 32) / 32 + 1 := by omega
      have h2 : (i - 32) % 32 = i % 32 := by omega
      rw [h1, h2, List.getD_cons_succ]

private theorem dictBytes_list : dictBytes.data.toList = dictLines.flatMap lineBytes := by
  simp [dictBytes, List.data_toByteArray]

theorem dictBytes_size : dictBytes.size = 122784 := by
  simp only [dictBytes, List.size_toByteArray, flatMap_length]
  exact DICTSIZE_eq.2

private theorem dict_toNat_get {i : Nat} (h : i < 122784) :
    (dictLines.flatMap lineBytes)[i]? = some (DICT i).toUInt8 := by
  have hl := DICTSIZE_eq.2
  rw [flatMap_get _ _ (by omega)]
  rfl

private theorem dict_lt (i : Nat) : DICT i < 256 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem toUInt8_toNat {x : Nat} (h : x < 256) : x.toUInt8.toNat = x := by
  simp only [Nat.toUInt8, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

/-- Values that are bytes survive `Nat.toUInt8` and back. -/
private theorem map_toUInt8 : ∀ l : List Nat, (∀ b ∈ l, b < 256) →
    (l.map Nat.toUInt8).map UInt8.toNat = l
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons]
    rw [toUInt8_toNat (h x (by simp)), map_toUInt8 l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- A run of bytes from a byte array. -/
def slice (t : ByteArray) (p n : Nat) : List Nat :=
  ((t.data.toList.drop p).take n).map UInt8.toNat

/-- A run of the dictionary's bytes is the spec's. -/
theorem dict_slice {p n : Nat} (h : p + n ≤ 122784) :
    slice dictBytes p n = (List.range n).map fun k => DICT (p + k) := by
  have hl := DICTSIZE_eq.2
  have hlen : (dictLines.flatMap lineBytes).length = 122784 := by
    rw [flatMap_length]
    exact hl
  unfold slice
  rw [dictBytes_list]
  apply List.ext_getElem
  · simp [hlen]
    omega
  · intro i h1 h2
    have hi : i < n := by simpa using h2
    have hg := dict_toNat_get (i := p + i) (by omega)
    obtain ⟨_, hv⟩ := List.getElem?_eq_some_iff.mp hg
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
    rw [hv, toUInt8_toNat (dict_lt _)]

/-! ### Slices -/

theorem slice_length {t : ByteArray} {p n : Nat} (h : p + n ≤ t.size) : (slice t p n).length = n := by
  have : t.size = t.data.size := rfl
  simp [slice]
  omega

/-- A run's first byte, then the rest of the run. -/
theorem slice_cons {t : ByteArray} {i : USize} {p n : Nat} (hp : i.toNat = p) (h : p + n + 1 ≤ t.size) (hb : i.toNat < t.size) :
    slice t p (n + 1) = (t.uget i hb).toNat :: slice t (p + 1) n := by
  subst hp
  have hl : i.toNat < t.data.toList.length := by
    have : t.size = t.data.size := rfl
    simp only [Array.length_toList]
    omega
  have huget : t.uget i hb = t.data.toList[i.toNat] := by
    cases t with
    | mk bs => simp [ByteArray.uget]
  unfold slice
  rw [List.drop_eq_getElem_cons hl, List.take_succ_cons, List.map_cons, huget]

theorem slice_zero (t : ByteArray) (p : Nat) : slice t p 0 = [] := by
  simp [slice]

/-- Part of a run. -/
theorem slice_drop (t : ByteArray) (p n k : Nat) : (slice t p n).drop k = slice t (p + k) (n - k) := by
  simp only [slice, ← List.map_drop, List.drop_take, List.drop_drop]

theorem slice_take (t : ByteArray) (p n k : Nat) (h : k ≤ n) : (slice t p n).take k = slice t p k := by
  simp only [slice, ← List.map_take, List.take_take]
  rw [Nat.min_eq_left h]

/-- Adding a run of bytes to a buffer. -/
theorem emit_slice (t buf : ByteArray) {p n : Nat} (h : p + n ≤ t.size) :
    (emitRun t buf p n).data.toList.map UInt8.toNat = buf.data.toList.map UInt8.toNat ++ slice t p n := by
  rw [emitRun_data _ _ h, List.map_append]
  rfl

private theorem data_push (b : ByteArray) (x : UInt8) : (b.push x).data.toList = b.data.toList ++ [x] := by
  cases b
  simp [ByteArray.push]

private theorem push_map (b : ByteArray) (x : UInt8) :
    (b.push x).data.toList.map UInt8.toNat = b.data.toList.map UInt8.toNat ++ [x.toNat] := by
  rw [data_push, List.map_append]
  rfl

private theorem usize_add_small {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) : (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_lit {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

private theorem usize_plus {a : USize} {n : Nat} (hn : n < 2 ^ 16) (h : a.toNat < 2 ^ 24) :
    (a + USize.ofNat n).toNat = a.toNat + n := by
  rw [usize_add_small (by rw [usize_lit (by omega)]; omega), usize_lit (by omega)]

/-! ### Ferment -/

/-- Adds the bytes `ferment` gives for a word starting at `pos`, with `n` bytes in it. -/
def fermentPush (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (buf : ByteArray) (h : pos.toNat + n.toNat ≤ t.size)
    (hn : n.toNat ≠ 0) : ByteArray :=
  have h1 : (pos + USize.ofNat 1).toNat = pos.toNat + 1 := by exact usize_plus (by decide) (by omega)
  have h2 : (pos + USize.ofNat 2).toNat = pos.toNat + 2 := by exact usize_plus (by decide) (by omega)
  let b := t.uget pos (by omega)
  if b < 192 then buf.push (if 97 ≤ b ∧ b ≤ 122 then b ^^^ 32 else b)
  else if b < 224 then
    if hn1 : n.toNat = 1 then buf.push b
    else (buf.push b).push (t.uget (pos + USize.ofNat 1) (by omega) ^^^ 32)
  else
    if hn1 : n.toNat = 1 then buf.push b
    else if hn2 : n.toNat = 2 then (buf.push b).push (t.uget (pos + USize.ofNat 1) (by omega))
    else
      ((buf.push b).push (t.uget (pos + USize.ofNat 1) (by omega))).push
        (t.uget (pos + USize.ofNat 2) (by omega) ^^^ 5)

/-- How many bytes `ferment` uses of a word starting with `b`, with `n` bytes in it. -/
@[inline] def fermentUsed (b : UInt8) (n : USize) : USize :=
  if b < 192 then USize.ofNat 1
  else if b < 224 then usmin n (USize.ofNat 2)
  else usmin n (USize.ofNat 3)

private theorem u8_xor (x : UInt8) (c : UInt8) : (x ^^^ c).toNat = x.toNat ^^^ c.toNat := UInt8.toNat_xor _ _

/-- What `fermentPush` and `fermentUsed` do, in the spec's terms. -/
theorem ferment_step {t : ByteArray} {hs : t.size < 2 ^ 24} {pos n : USize} {buf : ByteArray}
    (h : pos.toNat + n.toNat ≤ t.size) (hn : n.toNat ≠ 0) :
    let u := fermentUsed (t.uget pos (by omega)) n
    (fermentPush t hs pos n buf h hn).data.toList.map UInt8.toNat =
        buf.data.toList.map UInt8.toNat ++ (ferment (slice t pos.toNat n.toNat)).1 ∧
      (ferment (slice t pos.toNat n.toNat)).2 = slice t (pos.toNat + u.toNat) (n.toNat - u.toNat) ∧
      1 ≤ u.toNat ∧ u.toNat ≤ n.toNat := by
  have h1 : (pos + USize.ofNat 1).toNat = pos.toNat + 1 := usize_plus (by decide) (by omega)
  have h2 : (pos + USize.ofNat 2).toNat = pos.toNat + 2 := usize_plus (by decide) (by omega)
  have one : (USize.ofNat 1).toNat = 1 := usize_lit (by decide)
  have two : (USize.ofNat 2).toNat = 2 := usize_lit (by decide)
  have three : (USize.ofNat 3).toNat = 3 := usize_lit (by decide)
  obtain ⟨N, hN⟩ : ∃ N, n.toNat = N + 1 := ⟨n.toNat - 1, by omega⟩
  have hb0 : pos.toNat < t.size := by omega
  have hb : slice t pos.toNat n.toNat = (t.uget pos hb0).toNat :: slice t (pos.toNat + 1) N := by
    rw [hN]
    exact slice_cons rfl (by omega) hb0
  dsimp only
  unfold fermentPush fermentUsed
  dsimp only
  rw [hb]
  generalize t.uget pos _ = b
  by_cases h192 : b < 192
  · have h192' : b.toNat < 192 := UInt8.lt_iff_toNat_lt.mp h192
    rw [ite_eq_left h192, ite_eq_left h192, one]
    have hf : ferment (b.toNat :: slice t (pos.toNat + 1) N) =
        ([if 97 ≤ b.toNat ∧ b.toNat ≤ 122 then b.toNat ^^^ 32 else b.toNat], slice t (pos.toNat + 1) N) := by
      simp only [ferment, h192', ↓reduceIte]
    rw [hf]
    refine ⟨?_, by rw [show n.toNat - 1 = N by omega], by omega, by omega⟩
    rw [push_map]
    congr 2
    by_cases hc : 97 ≤ b ∧ b ≤ 122
    · have hc' : 97 ≤ b.toNat ∧ b.toNat ≤ 122 :=
        ⟨UInt8.le_iff_toNat_le.mp hc.1, UInt8.le_iff_toNat_le.mp hc.2⟩
      rw [ite_eq_left hc, ite_eq_left hc', u8_xor]
      rfl
    · have hc' : ¬ (97 ≤ b.toNat ∧ b.toNat ≤ 122) := fun e =>
        hc ⟨UInt8.le_iff_toNat_le.mpr e.1, UInt8.le_iff_toNat_le.mpr e.2⟩
      rw [ite_eq_right hc, ite_eq_right hc']
  · have h192' : ¬ b.toNat < 192 := fun e => h192 (UInt8.lt_iff_toNat_lt.mpr e)
    rw [ite_eq_right h192, ite_eq_right h192]
    by_cases h224 : b < 224
    · have h224' : b.toNat < 224 := UInt8.lt_iff_toNat_lt.mp h224
      rw [ite_eq_left h224, ite_eq_left h224, usmin_toNat, two]
      cases N with
      | zero =>
        have hf : ferment (b.toNat :: slice t (pos.toNat + 1) 0) = ([b.toNat], []) := by
          simp only [slice_zero, ferment, h192', h224', ↓reduceIte]
        rw [dite_eq_left (by omega), hf, push_map, show n.toNat - min n.toNat 2 = 0 by omega, slice_zero]
        exact ⟨rfl, rfl, by omega, by omega⟩
      | succ M =>
        have hc := slice_cons (t := t) (i := pos + USize.ofNat 1) (n := M) h1 (by omega) (by omega)
        have hf : ferment (b.toNat :: slice t (pos.toNat + 1) (M + 1)) =
            ([b.toNat, (t.uget (pos + USize.ofNat 1) (by omega)).toNat ^^^ 32], slice t (pos.toNat + 1 + 1) M) := by
          rw [hc]
          simp only [ferment, h192', h224', ↓reduceIte]
        rw [dite_eq_right (by omega), hf, push_map, push_map, u8_xor]
        refine ⟨?_, ?_, by omega, by omega⟩
        · rw [List.append_assoc]
          rfl
        · show slice t (pos.toNat + 1 + 1) M = _
          rw [show pos.toNat + min n.toNat 2 = pos.toNat + 1 + 1 by omega, show n.toNat - min n.toNat 2 = M by omega]
    · have h224' : ¬ b.toNat < 224 := fun e => h224 (UInt8.lt_iff_toNat_lt.mpr e)
      rw [ite_eq_right h224, ite_eq_right h224, usmin_toNat, three]
      cases N with
      | zero =>
        have hf : ferment (b.toNat :: slice t (pos.toNat + 1) 0) = ([b.toNat], []) := by
          simp only [slice_zero, ferment, h192', h224', ↓reduceIte]
        rw [dite_eq_left (by omega), hf, push_map, show n.toNat - min n.toNat 3 = 0 by omega, slice_zero]
        exact ⟨rfl, rfl, by omega, by omega⟩
      | succ M =>
        have hc := slice_cons (t := t) (i := pos + USize.ofNat 1) (n := M) h1 (by omega) (by omega)
        cases M with
        | zero =>
          have hf : ferment (b.toNat :: slice t (pos.toNat + 1) (0 + 1)) =
              ([b.toNat, (t.uget (pos + USize.ofNat 1) (by omega)).toNat], []) := by
            rw [hc]
            simp only [slice_zero, ferment, h192', h224', ↓reduceIte]
          rw [dite_eq_right (by omega), dite_eq_left (by omega), hf, push_map, push_map,
            show n.toNat - min n.toNat 3 = 0 by omega, slice_zero]
          refine ⟨?_, rfl, by omega, by omega⟩
          rw [List.append_assoc]
          rfl
        | succ L =>
          have hd := slice_cons (t := t) (i := pos + USize.ofNat 2) (n := L) (p := pos.toNat + 1 + 1) (by omega) (by omega) (by omega)
          have hf : ferment (b.toNat :: slice t (pos.toNat + 1) (L + 1 + 1)) =
              ([b.toNat, (t.uget (pos + USize.ofNat 1) (by omega)).toNat, (t.uget (pos + USize.ofNat 2) (by omega)).toNat ^^^ 5],
                slice t (pos.toNat + 1 + 1 + 1) L) := by
            rw [hc, hd]
            simp only [ferment, h192', h224', ↓reduceIte]
          rw [dite_eq_right (by omega), dite_eq_right (by omega), hf, push_map, push_map, push_map, u8_xor]
          refine ⟨?_, ?_, by omega, by omega⟩
          · rw [List.append_assoc, List.append_assoc]
            rfl
          · show slice t (pos.toNat + 1 + 1 + 1) L = _
            rw [show pos.toNat + min n.toNat 3 = pos.toNat + 1 + 1 + 1 by omega, show n.toNat - min n.toNat 3 = L by omega]

theorem fermentUsed_bounds (b : UInt8) {n : USize} (hn : n.toNat ≠ 0) :
    1 ≤ (fermentUsed b n).toNat ∧ (fermentUsed b n).toNat ≤ n.toNat := by
  have one : (USize.ofNat 1).toNat = 1 := usize_lit (by decide)
  have two : (USize.ofNat 2).toNat = 2 := usize_lit (by decide)
  have three : (USize.ofNat 3).toNat = 3 := usize_lit (by decide)
  unfold fermentUsed
  split
  · rw [one]
    omega
  · split
    · rw [usmin_toNat, two]
      omega
    · rw [usmin_toNat, three]
      omega

/-- `FermentAll` on a run of an array. -/
def fermentRun (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (buf : ByteArray) (h : pos.toNat + n.toNat ≤ t.size) : ByteArray :=
  if hn : n = 0 then buf
  else
    have hnz := usize_ne hn
    have hu := fermentUsed_bounds (t.uget pos (by omega)) hnz
    have hp : (pos + fermentUsed (t.uget pos (by omega)) n).toNat =
        pos.toNat + (fermentUsed (t.uget pos (by omega)) n).toNat := by exact usize_add_small (by omega)
    have hm : (n - fermentUsed (t.uget pos (by omega)) n).toNat =
        n.toNat - (fermentUsed (t.uget pos (by omega)) n).toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
    fermentRun t hs (pos + fermentUsed (t.uget pos (by omega)) n) (n - fermentUsed (t.uget pos (by omega)) n)
      (fermentPush t hs pos n buf h hnz) (by rw [hp, hm]; omega)
termination_by n.toNat
decreasing_by
  rw [hm]
  omega

private theorem fermentAllWith_fuel : ∀ (f g : Nat) (word : List Nat), word.length ≤ f → word.length ≤ g →
    fermentAllWith [] f word = fermentAllWith [] g word
  | _, _, [], _, _ => by simp [fermentAllWith]
  | 0, _, _ :: _, h, _ => by simp at h
  | _, 0, _ :: _, _, h => by simp at h
  | f + 1, g + 1, b :: word, h1, h2 => by
    have hl := ferment_length (b :: word)
    have hp := ferment_pos b word
    simp only [List.length_cons] at h1 h2 hl
    simp only [fermentAllWith]
    rw [fermentAllWith_fuel f g _ (by omega) (by omega)]

private theorem fermentAll_cons (b : Nat) (word : List Nat) :
    fermentAll (b :: word) = (ferment (b :: word)).1 ++ fermentAll (ferment (b :: word)).2 := by
  have hl := ferment_length (b :: word)
  have hp := ferment_pos b word
  simp only [List.length_cons] at hl
  unfold fermentAll
  simp only [List.length_cons, fermentAllWith]
  rw [fermentAllWith_fuel word.length _ _ (by omega) (Nat.le_refl _)]

/-- What `fermentRun` does: adds the spec's `fermentAll` of the run. -/
theorem fermentRun_spec {t : ByteArray} {hs : t.size < 2 ^ 24} : ∀ (N : Nat) (pos n : USize) (buf : ByteArray)
    (h : pos.toNat + n.toNat ≤ t.size), n.toNat = N →
    (fermentRun t hs pos n buf h).data.toList.map UInt8.toNat =
      buf.data.toList.map UInt8.toNat ++ fermentAll (slice t pos.toNat n.toNat) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro pos n buf h hN
    rw [fermentRun]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]
      subst hn
      have h0 : (0 : USize).toNat = 0 := rfl
      rw [h0, slice_zero]
      simp [fermentAll, fermentAllWith]
    · rw [dite_eq_right hn]
      have hnz := usize_ne hn
      obtain ⟨hpush, hrest, hu1, hu2⟩ := ferment_step (t := t) (hs := hs) (buf := buf) h hnz
      dsimp only at hpush hrest hu1 hu2 ⊢
      have hp : (pos + fermentUsed (t.uget pos (by omega)) n).toNat = pos.toNat + (fermentUsed (t.uget pos (by omega)) n).toNat :=
        usize_add_small (by omega)
      have hm : (n - fermentUsed (t.uget pos (by omega)) n).toNat = n.toNat - (fermentUsed (t.uget pos (by omega)) n).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu2)
      rw [ih (n - fermentUsed (t.uget pos (by omega)) n).toNat (by omega) (pos + fermentUsed (t.uget pos (by omega)) n)
        (n - fermentUsed (t.uget pos (by omega)) n) _ _ rfl, hpush, hp, hm, List.append_assoc, ← hrest]
      obtain ⟨M, hM⟩ : ∃ M, n.toNat = M + 1 := ⟨n.toNat - 1, by omega⟩
      have hb : slice t pos.toNat n.toNat = (t.uget pos (by omega)).toNat :: slice t (pos.toNat + 1) M := by
        rw [hM]
        exact slice_cons rfl (by omega) (by omega)
      rw [hb, fermentAll_cons]

/-! ### The transforms -/

/-- A transform's kind and amount, as numbers. -/
def elemCode : ElementaryTransform → Nat × Nat
  | .identity => (0, 0)
  | .fermentFirst => (1, 0)
  | .fermentAll => (2, 0)
  | .omitFirst k => (3, k)
  | .omitLast k => (4, k)

/-- A transform as 32 numbers: its kind, amount, prefix length and suffix length, its prefix, its suffix, then zeros. -/
def rowNat (t : WordTransform) : List Nat :=
  let hd := [(elemCode t.elementary).1, (elemCode t.elementary).2, (bytes t.prefixString).length, (bytes t.suffixString).length] ++
    bytes t.prefixString ++ bytes t.suffixString
  hd ++ List.replicate (32 - hd.length) 0

/-- A transform as 32 bytes. -/
def rowBytes (t : WordTransform) : List UInt8 := (rowNat t).map Nat.toUInt8

/-- The transforms' table. -/
def transLut : ByteArray := (transforms.flatMap rowBytes).toByteArray

private theorem rows_ok : ∀ t ∈ transforms,
    (bytes t.prefixString).length + (bytes t.suffixString).length ≤ 13 ∧ (∀ x ∈ rowNat t, x < 256) := by
  decide +kernel

theorem transforms_length : transforms.length = 121 := by
  decide +kernel

private theorem rowNat_length {t : WordTransform} (ht : t ∈ transforms) : (rowNat t).length = 32 := by
  have := (rows_ok t ht).1
  simp [rowNat]
  omega

private theorem flatMap_drop : ∀ (l : List WordTransform) (i : Nat), (∀ t ∈ l, (rowBytes t).length = 32) →
    (l.flatMap rowBytes).drop (32 * i) = (l.drop i).flatMap rowBytes
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | x :: xs, i + 1, h => by
    rw [List.flatMap_cons, show 32 * (i + 1) = 32 + 32 * i by omega, ← List.drop_drop,
      List.drop_left' (h x (by simp)), flatMap_drop xs i (fun t ht => h t (List.mem_cons_of_mem _ ht))]
    rfl

private theorem map_row {t : WordTransform} (ht : t ∈ transforms) : (rowBytes t).map UInt8.toNat = rowNat t := by
  unfold rowBytes
  exact map_toUInt8 _ (rows_ok t ht).2

theorem transLut_size : transLut.size = 3872 := by
  have key : ∀ l : List WordTransform, (∀ t ∈ l, (rowBytes t).length = 32) → (l.flatMap rowBytes).length = l.length * 32 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons x xs ih =>
      intro h
      rw [List.flatMap_cons, List.length_append, h x (by simp), ih (fun t ht => h t (List.mem_cons_of_mem _ ht)), List.length_cons]
      omega
  simp only [transLut, List.size_toByteArray]
  rw [key _ (fun t ht => by simp [rowBytes, rowNat_length ht]), transforms_length]

/-- The table from a transform's row on, with the numbers of that row first. -/
private theorem transLut_row {id : Nat} {t : WordTransform} (h : transforms[id]? = some t) :
    ∃ R : List Nat, (transLut.data.toList.drop (32 * id)).map UInt8.toNat = rowNat t ++ R := by
  have hm := List.mem_of_getElem? h
  obtain ⟨hlt, hv⟩ := List.getElem?_eq_some_iff.mp h
  have hd : transLut.data.toList = transforms.flatMap rowBytes := by
    simp [transLut, List.data_toByteArray]
  rw [hd, flatMap_drop _ _ (fun t ht => by simp [rowBytes, rowNat_length ht]), List.drop_eq_getElem_cons hlt, hv,
    List.flatMap_cons, List.map_append, map_row hm]
  exact ⟨_, rfl⟩

/-- A run of a row's bytes. -/
private theorem row_slice {id : Nat} {t : WordTransform} (h : transforms[id]? = some t) (j n : Nat) (hj : j + n ≤ 32) :
    slice transLut (32 * id + j) n = ((rowNat t).drop j).take n := by
  obtain ⟨R, hR⟩ := transLut_row h
  have hlen := rowNat_length (List.mem_of_getElem? h)
  unfold slice
  rw [← List.drop_drop, List.map_take, List.map_drop, hR, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

private theorem row_prefix (t : WordTransform) :
    ((rowNat t).drop 4).take (bytes t.prefixString).length = bytes t.prefixString := by
  have e : rowNat t = [(elemCode t.elementary).1, (elemCode t.elementary).2, (bytes t.prefixString).length,
      (bytes t.suffixString).length] ++ (bytes t.prefixString ++ (bytes t.suffixString ++ List.replicate
        (32 - (4 + (bytes t.prefixString).length + (bytes t.suffixString).length)) 0)) := by
    simp [rowNat] <;> omega
  rw [e, List.drop_left' (i := 4) rfl, List.take_left' rfl]

private theorem row_suffix (t : WordTransform) :
    ((rowNat t).drop (4 + (bytes t.prefixString).length)).take (bytes t.suffixString).length = bytes t.suffixString := by
  have e : rowNat t = ([(elemCode t.elementary).1, (elemCode t.elementary).2, (bytes t.prefixString).length,
      (bytes t.suffixString).length] ++ bytes t.prefixString) ++ (bytes t.suffixString ++ List.replicate
        (32 - (4 + (bytes t.prefixString).length + (bytes t.suffixString).length)) 0) := by
    simp [rowNat] <;> omega
  rw [e, List.drop_left' (by simp; omega), List.take_left' rfl]

/-- A byte of a row. -/
private theorem row_byte {id j : Nat} {t : WordTransform} (h : transforms[id]? = some t) (hj : j < 32) {i : USize}
    (hi : i.toNat = 32 * id + j) (hb : i.toNat < transLut.size) :
    (transLut.uget i hb).toNat = (rowNat t).getD j 0 := by
  have hlen := rowNat_length (List.mem_of_getElem? h)
  have hs := row_slice h j 1 (by omega)
  have hc := slice_cons (t := transLut) (i := i) (n := 0) hi (by omega) hb
  rw [hs] at hc
  have hd : (rowNat t).drop j = (rowNat t)[j] :: (rowNat t).drop (j + 1) := List.drop_eq_getElem_cons (by omega)
  rw [hd, List.take_succ_cons] at hc
  simp only [List.take_zero, slice_zero] at hc
  have := List.head_eq_of_cons_eq hc
  rw [← this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- A transform's prefix and suffix are 13 bytes at most together. -/
theorem affix_le {id : Nat} (hid : id < 121) :
    (transLut.data[32 * id + 2]?.getD 0).toNat + (transLut.data[32 * id + 3]?.getD 0).toNat ≤ 13 := by
  have hl := transforms_length
  obtain ⟨t, ht⟩ : ∃ t, transforms[id]? = some t := ⟨transforms[id]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  have hsz := transLut_size
  have hrow := (rows_ok t (List.mem_of_getElem? ht)).1
  have key : ∀ j, j < 32 → (transLut.data[32 * id + j]?.getD 0).toNat = (rowNat t).getD j 0 := by
    intro j hj
    have hu : (USize.ofNat (32 * id + j)).toNat = 32 * id + j := by
      rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
      have := USize.le_size
      exact Nat.mod_eq_of_lt (by omega)
    have hb : (USize.ofNat (32 * id + j)).toNat < transLut.size := by rw [hu]; omega
    have hget : (transLut.uget (USize.ofNat (32 * id + j)) hb).toNat = (transLut.data[(USize.ofNat (32 * id + j)).toNat]?.getD 0).toNat := by
      generalize transLut = t at hb
      cases t with
      | mk bs =>
        have h' : (USize.ofNat (32 * id + j)).toNat < bs.size := hb
        show (bs[(USize.ofNat (32 * id + j)).toNat]'h').toNat = (bs[(USize.ofNat (32 * id + j)).toNat]?.getD 0).toNat
        rw [Array.getElem?_eq_getElem h']
        rfl
    have := row_byte ht hj hu hb
    rw [hget, hu] at this
    exact this
  rw [key 2 (by decide), key 3 (by decide)]
  simp only [rowNat, List.append_assoc, List.cons_append, List.getD_cons_succ, List.getD_cons_zero]
  exact hrow

/-! ### A word -/

/-- The transform's elementary part, added to a buffer. -/
def elementStep (t : ByteArray) (hs : t.size < 2 ^ 24) (kind k : UInt8) (off len : USize) (buf : ByteArray)
    (h : off.toNat + len.toNat ≤ t.size) : ByteArray :=
  if kind = 0 then emitRun t buf off.toNat len.toNat
  else if kind = 1 then
    if hn : len = 0 then buf
    else
      have hnz := usize_ne hn
      let u := fermentUsed (t.uget off (by omega)) len
      emitRun t (fermentPush t hs off len buf h hnz) (off + u).toNat (len - u).toNat
  else if kind = 2 then fermentRun t hs off len buf h
  else if kind = 3 then
    let m := usmin len k.toUSize
    emitRun t buf (off + m).toNat (len - m).toNat
  else emitRun t buf off.toNat (len - usmin len k.toUSize).toNat

private theorem u8_usize (x : UInt8) : x.toUSize.toNat = x.toNat := by
  simp

/-- What `elementStep` does: adds the spec's elementary transform of the run. -/
theorem elementStep_spec {t : ByteArray} {hs : t.size < 2 ^ 24} {kind k : UInt8} {off len : USize} {buf : ByteArray}
    (h : off.toNat + len.toNat ≤ t.size) {e : ElementaryTransform} (hk : (elemCode e).1 = kind.toNat) (hk2 : (elemCode e).2 = k.toNat) :
    (elementStep t hs kind k off len buf h).data.toList.map UInt8.toNat =
      buf.data.toList.map UInt8.toNat ++ applyElementary e (slice t off.toNat len.toNat) := by
  have hzero : ∀ x : UInt8, x.toNat = 0 → x = 0 := fun x e => UInt8.toNat_inj.mp (by rw [e]; rfl)
  have hkU := u8_usize k
  have hmin : (usmin len k.toUSize).toNat = min len.toNat k.toNat := by rw [usmin_toNat, hkU]
  have hub : k.toNat < 256 := k.toNat_lt
  have hp : (off + usmin len k.toUSize).toNat = off.toNat + min len.toNat k.toNat := by
    rw [usize_add_small (by rw [hmin]; omega), hmin]
  have hm : (len - usmin len k.toUSize).toNat = len.toNat - min len.toNat k.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
  have hslen : (slice t off.toNat len.toNat).length = len.toNat := slice_length h
  unfold elementStep
  cases e with
  | identity =>
    have h0 : kind = 0 := hzero _ hk.symm
    rw [ite_eq_left h0, emit_slice _ _ h]
    rfl
  | fermentFirst =>
    have h1 : kind = 1 := UInt8.toNat_inj.mp (by rw [← hk]; rfl)
    subst h1
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    by_cases hn : len = 0
    · rw [dite_eq_left hn]
      subst hn
      rw [show (0 : USize).toNat = 0 from rfl, slice_zero]
      simp [applyElementary, fermentFirst, ferment]
    · rw [dite_eq_right hn]
      have hnz := usize_ne hn
      obtain ⟨hpush, hrest, hu1, hu2⟩ := ferment_step (t := t) (hs := hs) (buf := buf) h hnz
      dsimp only at hpush hrest hu1 hu2 ⊢
      generalize fermentUsed _ _ = u at hrest hu1 hu2 ⊢
      have hpu : (off + u).toNat = off.toNat + u.toNat := usize_add_small (by omega)
      have hmu : (len - u).toNat = len.toNat - u.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu2)
      rw [emit_slice _ _ (by rw [hpu, hmu]; omega), hpush, hpu, hmu, List.append_assoc, ← hrest]
      rfl
  | fermentAll =>
    have h2 : kind = 2 := UInt8.toNat_inj.mp (by rw [← hk]; rfl)
    subst h2
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    exact fermentRun_spec _ _ _ _ h rfl
  | omitFirst j =>
    have h3 : kind = 3 := UInt8.toNat_inj.mp (by rw [← hk]; rfl)
    have hj : j = k.toNat := hk2
    subst h3
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    dsimp only
    rw [emit_slice _ _ (by rw [hp, hm]; omega), hp, hm]
    show _ = _ ++ (slice t off.toNat len.toNat).drop j
    rw [hj]
    by_cases hle : k.toNat ≤ len.toNat
    · rw [slice_drop, Nat.min_eq_right hle]
    · rw [Nat.min_eq_left (by omega), List.drop_eq_nil_of_le (by omega), Nat.sub_self, slice_zero]
  | omitLast j =>
    have h4 : kind = 4 := UInt8.toNat_inj.mp (by rw [← hk]; rfl)
    have hj : j = k.toNat := hk2
    subst h4
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide)]
    rw [emit_slice _ _ (by rw [hm]; omega), hm]
    show _ = _ ++ (slice t off.toNat len.toNat).take ((slice t off.toNat len.toNat).length - j)
    rw [hslen, hj, slice_take _ _ _ _ (by omega)]
    congr 2
    omega

/-! ### Stores at masked window positions

The fast command loop writes the window through these stores, and a dictionary word can be written straight into the
window through them, with no buffer: `putList` is what such a write does, a byte list stored from a position on, each
byte at its masked position. -/

/-- A window index masked with the constant `0xFFFFFF`, which is no change (every window is at most `2 ^ 24` bytes) but
tells the C compiler the index is small, so that a byte store can't reach the array's reference count and the store's
exclusivity check isn't repeated (P25, `docs/lean-facts.md`). -/
@[inline] def wix (i : USize) : USize := i &&& USize.ofNat 0xFFFFFF

theorem wix_toNat {i : USize} (h : i.toNat < 2 ^ 24) : (wix i).toNat = i.toNat := by
  unfold wix
  rw [USize.toNat_and, usize_lit (by decide), show 16777215 = 2 ^ 24 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

theorem mask_lt {i mask : USize} {k : Nat} (hm : mask.toNat = 2 ^ k - 1) : (i &&& mask).toNat < 2 ^ k := by
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A store at a masked window position. -/
@[inline] def wput (ring : ByteArray) (i mask : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) (v : UInt8) : ByteArray :=
  ring.uset (wix (i &&& mask)) v (by
    have := mask_lt (i := i) hm
    have : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    rw [wix_toNat (by omega)]
    omega)

theorem wput_size (ring : ByteArray) (i mask : USize) {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) (v : UInt8) : (wput ring i mask hk hm hs v).size = 2 ^ k :=
  (size_ringWrite ring _ v _).trans hs

private theorem uget_list (t : ByteArray) (i : USize) (h : i.toNat < t.size) :
    t.uget i h = t.data.toList[i.toNat]'(by have : t.size = t.data.size := rfl; simp only [Array.length_toList]; omega) := by
  cases t with
  | mk bs => simp [ByteArray.uget]

section
variable {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)

/-- The window after the bytes `l` are stored from position `o` on, each at its masked position. -/
def putList : (ring : ByteArray) → (o : USize) → ring.size = 2 ^ k → List UInt8 → ByteArray
  | ring, _, _, [] => ring
  | ring, o, hs, b :: l => putList (wput ring o mask hk hm hs b) (o + USize.ofNat 1) (wput_size ring o mask hk hm hs b) l

theorem putList_size : ∀ (l : List UInt8) (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k),
    (putList hk hm ring o hs l).size = 2 ^ k
  | [], _, _, hs => hs
  | b :: l, ring, o, hs => putList_size l (wput ring o mask hk hm hs b) (o + USize.ofNat 1) (wput_size ring o mask hk hm hs b)

theorem putList_congr {r1 r2 : ByteArray} {o1 o2 : USize} {h1 : r1.size = 2 ^ k} {h2 : r2.size = 2 ^ k}
    {l : List UInt8} (e1 : r1 = r2) (e2 : o1 = o2) : putList hk hm r1 o1 h1 l = putList hk hm r2 o2 h2 l := by
  subst e1 e2
  rfl

theorem putList_append : ∀ (l1 l2 : List UInt8) (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k),
    putList hk hm ring o hs (l1 ++ l2) =
      putList hk hm (putList hk hm ring o hs l1) (o + USize.ofNat l1.length) (putList_size hk hm l1 ring o hs) l2
  | [], l2, ring, o, hs => putList_congr hk hm rfl (by rw [List.length_nil, show USize.ofNat 0 = 0 from rfl,
      USize.add_zero])
  | b :: l1, l2, ring, o, hs => by
    show putList hk hm (wput ring o mask hk hm hs b) (o + USize.ofNat 1) (wput_size ring o mask hk hm hs b) (l1 ++ l2) =
      putList hk hm (putList hk hm (wput ring o mask hk hm hs b) (o + USize.ofNat 1) (wput_size ring o mask hk hm hs b) l1)
        (o + USize.ofNat (b :: l1).length) _ l2
    refine (putList_append l1 l2 _ _ _).trans (putList_congr hk hm rfl ?_)
    rw [List.length_cons, USize.ofNat_add, USize.add_assoc, USize.add_comm (USize.ofNat 1)]

theorem uset_idx {t : ByteArray} {i j : USize} {v : UInt8} {hi : i.toNat < t.size} {hj : j.toNat < t.size}
    (e : i = j) : t.uset i v hi = t.uset j v hj := by
  subst e
  rfl

theorem uset_congr2 {t : ByteArray} {i j : USize} {v w : UInt8} {hi : i.toNat < t.size} {hj : j.toNat < t.size}
    (e : i = j) (ev : v = w) : t.uset i v hi = t.uset j w hj := by
  subst e ev
  rfl

theorem wput_congr {ring : ByteArray} {i j : USize} {hs : ring.size = 2 ^ k} {v : UInt8}
    (e : i &&& mask = j &&& mask) : wput ring i mask hk hm hs v = wput ring j mask hk hm hs v := by
  unfold wput
  exact uset_idx (by rw [e])

include hk hm in
/-- The next position, masked, depends only on the position masked. -/
theorem next_mask {a b : USize} (e : a &&& mask = b &&& mask) :
    (a + USize.ofNat 1) &&& mask = (b + USize.ofNat 1) &&& mask := by
  have hb : k ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hd : 2 ^ k ∣ 2 ^ System.Platform.numBits := Nat.pow_dvd_pow 2 hb
  have e' := congrArg USize.toNat e
  rw [USize.toNat_and, USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod] at e'
  apply USize.toNat_inj.mp
  rw [USize.toNat_and, USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    USize.toNat_add, USize.toNat_add, Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd, Nat.add_mod, e',
    ← Nat.add_mod]

/-- A list stored from a position is stored from any position equal to it masked. -/
theorem putList_mask : ∀ (l : List UInt8) (ring : ByteArray) (o o' : USize) (hs : ring.size = 2 ^ k),
    o &&& mask = o' &&& mask → putList hk hm ring o hs l = putList hk hm ring o' hs l
  | [], _, _, _, _, _ => rfl
  | b :: l, ring, o, o', hs, e => by
    show putList hk hm (wput ring o mask hk hm hs b) (o + USize.ofNat 1) (wput_size ring o mask hk hm hs b) l =
      putList hk hm (wput ring o' mask hk hm hs b) (o' + USize.ofNat 1) (wput_size ring o' mask hk hm hs b) l
    exact (putList_congr hk hm (wput_congr hk hm e) rfl).trans (putList_mask l _ _ _ _ (next_mask hk hm e))

include hm in
theorem mask_mask (o : USize) : (o &&& mask) &&& mask = o &&& mask := by
  apply USize.toNat_inj.mp
  rw [USize.toNat_and, USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]

/-- What the word loop does to the window: its bytes stored from its position on. -/
theorem wordRun_put {buf : ByteArray} : ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hb : idx.toNat + n.toNat ≤ buf.size) (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k)
    (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
    (wordRun buf mask k hk hm n idx ring wpos p1 p2 hb hb32 hsize hwp).ring =
      putList hk hm ring wpos hsize ((buf.data.toList.drop idx.toNat).take n.toNat) := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    rw [wordRun, dite_eq_left (usize_zero hN), hN, List.take_zero]
    rfl
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [wordRun, dite_eq_right hn]
    dsimp only
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    have hl : idx.toNat < buf.data.toList.length := by
      have : buf.size = buf.data.size := rfl
      simp only [Array.length_toList]
      omega
    rw [ih (n - USize.ofNat 1) _ _ _ _ _ _ _ _ _ (by omega), hi, hpred, hN, List.drop_eq_getElem_cons hl,
      List.take_succ_cons, Nat.add_sub_cancel]
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    rw [putList.eq_2]
    refine (putList_congr hk hm ?_ rfl).trans (putList_mask hk hm _ _ _ _ _ ?_)
    · unfold ringWrite wput
      refine uset_congr2 (USize.toNat_inj.mp ?_) (uget_list buf idx _)
      rw [wix_toNat (Nat.lt_of_lt_of_le (mask_lt (i := wpos) hm) hR), USize.toNat_and, hm,
        Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hwp]
    · exact mask_mask hm _

/-- `n` bytes of `t` from `p`, stored in the window from position `o` on, each at its masked position. -/
def putRun (t : ByteArray) (ht : t.size < 2 ^ 24) (p n : USize) (h : p.toNat + n.toNat ≤ t.size) (ring : ByteArray)
    (o : USize) (hs : ring.size = 2 ^ k) : ByteArray :=
  if hn : n = 0 then ring
  else
    have hnz := usize_ne hn
    have hp : (p + USize.ofNat 1).toNat = p.toNat + 1 := by exact usize_plus (by decide) (by omega)
    have hq := usize_pred hn
    putRun t ht (p + USize.ofNat 1) (n - USize.ofNat 1) (by rw [hp, hq]; omega)
      (wput ring o mask hk hm hs (t.uget p (by omega))) (o + USize.ofNat 1)
      (wput_size ring o mask hk hm hs _)
termination_by n.toNat
decreasing_by
  have := usize_ne hn
  omega

theorem putRun_eq (t : ByteArray) (ht : t.size < 2 ^ 24) : ∀ (N : Nat) (p n : USize) (h : p.toNat + n.toNat ≤ t.size)
    (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k), n.toNat = N →
    putRun hk hm t ht p n h ring o hs = putList hk hm ring o hs ((t.data.toList.drop p.toNat).take n.toNat) := by
  intro N
  induction N with
  | zero =>
    intro p n h ring o hs hN
    rw [putRun, dite_eq_left (usize_zero hN), hN, List.take_zero]
    rfl
  | succ N ih =>
    intro p n h ring o hs hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hp : (p + USize.ofNat 1).toNat = p.toNat + 1 := usize_plus (by decide) (by omega)
    rw [putRun, dite_eq_right hn]
    dsimp only
    have hl : p.toNat < t.data.toList.length := by
      have : t.size = t.data.size := rfl
      simp only [Array.length_toList]
      omega
    rw [ih (p + USize.ofNat 1) (n - USize.ofNat 1) _ _ _ _ (by omega), hp, hpred, hN, List.drop_eq_getElem_cons hl,
      List.take_succ_cons, Nat.add_sub_cancel]
    rw [putList.eq_2]
    exact putList_congr hk hm (congrArg (wput ring o mask hk hm hs) (uget_list t p _)) rfl

theorem putRun_size (t : ByteArray) (ht : t.size < 2 ^ 24) (p n : USize) (h : p.toNat + n.toNat ≤ t.size)
    (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k) : (putRun hk hm t ht p n h ring o hs).size = 2 ^ k := by
  rw [putRun_eq hk hm t ht _ p n h ring o hs rfl]
  exact putList_size hk hm _ _ _ _

theorem take_drop_length {t : ByteArray} {p n : Nat} (h : p + n ≤ t.size) :
    ((t.data.toList.drop p).take n).length = n := by
  have : t.size = t.data.size := rfl
  simp only [List.length_take, List.length_drop, Array.length_toList]
  omega

private theorem data_push2 (b : ByteArray) (x y : UInt8) :
    ((b.push x).push y).data.toList = b.data.toList ++ [x, y] := by
  rw [data_push, data_push, List.append_assoc]
  rfl

private theorem data_push3 (b : ByteArray) (x y z : UInt8) :
    (((b.push x).push y).push z).data.toList = b.data.toList ++ [x, y, z] := by
  rw [data_push, data_push2, List.append_assoc]
  rfl

/-- What `fermentPush` adds to a buffer, stored in the window instead, from position `o` on. -/
def fermentPut (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (h : pos.toNat + n.toNat ≤ t.size)
    (hn : n.toNat ≠ 0) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) : ByteArray :=
  have h1 : (pos + USize.ofNat 1).toNat = pos.toNat + 1 := by exact usize_plus (by decide) (by omega)
  have h2 : (pos + USize.ofNat 2).toNat = pos.toNat + 2 := by exact usize_plus (by decide) (by omega)
  let b := t.uget pos (by omega)
  if b < 192 then wput ring o mask hk hm hr (if 97 ≤ b ∧ b ≤ 122 then b ^^^ 32 else b)
  else if b < 224 then
    if hn1 : n.toNat = 1 then wput ring o mask hk hm hr b
    else
      wput (wput ring o mask hk hm hr b) (o + USize.ofNat 1) mask hk hm (wput_size ring o mask hk hm hr b)
        (t.uget (pos + USize.ofNat 1) (by omega) ^^^ 32)
  else
    if hn1 : n.toNat = 1 then wput ring o mask hk hm hr b
    else if hn2 : n.toNat = 2 then
      wput (wput ring o mask hk hm hr b) (o + USize.ofNat 1) mask hk hm (wput_size ring o mask hk hm hr b)
        (t.uget (pos + USize.ofNat 1) (by omega))
    else
      wput (wput (wput ring o mask hk hm hr b) (o + USize.ofNat 1) mask hk hm (wput_size ring o mask hk hm hr b)
          (t.uget (pos + USize.ofNat 1) (by omega)))
        (o + USize.ofNat 1 + USize.ofNat 1) mask hk hm (wput_size _ _ mask hk hm (wput_size ring o mask hk hm hr b) _)
        (t.uget (pos + USize.ofNat 2) (by omega) ^^^ 5)

/-- `fermentPut` stores what `fermentPush` adds. -/
theorem fermentPut_mirror (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (h : pos.toNat + n.toNat ≤ t.size)
    (hn : n.toNat ≠ 0) (buf ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    ∃ L : List UInt8, (fermentPush t hs pos n buf h hn).data.toList = buf.data.toList ++ L ∧
      fermentPut hk hm t hs pos n h hn ring o hr = putList hk hm ring o hr L ∧
      L.length = (fermentUsed (t.uget pos (by omega)) n).toNat := by
  have one : (USize.ofNat 1).toNat = 1 := usize_lit (by decide)
  have two : (USize.ofNat 2).toNat = 2 := usize_lit (by decide)
  have three : (USize.ofNat 3).toNat = 3 := usize_lit (by decide)
  unfold fermentPush fermentPut fermentUsed
  dsimp only
  by_cases h192 : t.uget pos (by omega) < 192
  · rw [ite_eq_left h192, ite_eq_left h192, ite_eq_left h192]
    exact ⟨_, data_push _ _, rfl, by rw [one]; rfl⟩
  · rw [ite_eq_right h192, ite_eq_right h192, ite_eq_right h192]
    by_cases h224 : t.uget pos (by omega) < 224
    · rw [ite_eq_left h224, ite_eq_left h224, ite_eq_left h224, usmin_toNat, two]
      by_cases hn1 : n.toNat = 1
      · rw [dite_eq_left hn1, dite_eq_left hn1]
        exact ⟨_, data_push _ _, rfl, by simp only [List.length_singleton]; omega⟩
      · rw [dite_eq_right hn1, dite_eq_right hn1]
        exact ⟨_, data_push2 _ _ _, rfl, by simp only [List.length_cons, List.length_nil]; omega⟩
    · rw [ite_eq_right h224, ite_eq_right h224, ite_eq_right h224, usmin_toNat, three]
      by_cases hn1 : n.toNat = 1
      · rw [dite_eq_left hn1, dite_eq_left hn1]
        exact ⟨_, data_push _ _, rfl, by simp only [List.length_singleton]; omega⟩
      · rw [dite_eq_right hn1, dite_eq_right hn1]
        by_cases hn2 : n.toNat = 2
        · rw [dite_eq_left hn2, dite_eq_left hn2]
          exact ⟨_, data_push2 _ _ _, rfl, by simp only [List.length_cons, List.length_nil]; omega⟩
        · rw [dite_eq_right hn2, dite_eq_right hn2]
          exact ⟨_, data_push3 _ _ _ _, rfl, by simp only [List.length_cons, List.length_nil]; omega⟩

theorem fermentPut_size (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (h : pos.toNat + n.toNat ≤ t.size)
    (hn : n.toNat ≠ 0) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    (fermentPut hk hm t hs pos n h hn ring o hr).size = 2 ^ k := by
  obtain ⟨L, -, e, -⟩ := fermentPut_mirror hk hm t hs pos n h hn ByteArray.empty ring o hr
  rw [e]
  exact putList_size hk hm _ _ _ _

/-- What `fermentRun` adds to a buffer, stored in the window instead, from position `o` on. -/
def fermentRunPut (t : ByteArray) (hs : t.size < 2 ^ 24) (pos n : USize) (h : pos.toNat + n.toNat ≤ t.size)
    (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) : ByteArray :=
  if hn : n = 0 then ring
  else
    have hnz := usize_ne hn
    have hu := fermentUsed_bounds (t.uget pos (by omega)) hnz
    have hp : (pos + fermentUsed (t.uget pos (by omega)) n).toNat =
        pos.toNat + (fermentUsed (t.uget pos (by omega)) n).toNat := by exact usize_add_small (by omega)
    have hq : (n - fermentUsed (t.uget pos (by omega)) n).toNat =
        n.toNat - (fermentUsed (t.uget pos (by omega)) n).toNat :=
      USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
    fermentRunPut t hs (pos + fermentUsed (t.uget pos (by omega)) n) (n - fermentUsed (t.uget pos (by omega)) n)
      (by rw [hp, hq]; omega) (fermentPut hk hm t hs pos n h hnz ring o hr)
      (o + fermentUsed (t.uget pos (by omega)) n) (fermentPut_size hk hm t hs pos n h hnz ring o hr)
termination_by n.toNat
decreasing_by
  rw [hq]
  omega

/-- `fermentRunPut` stores what `fermentRun` adds. -/
theorem fermentRunPut_mirror (t : ByteArray) (hs : t.size < 2 ^ 24) : ∀ (N : Nat) (pos n : USize)
    (h : pos.toNat + n.toNat ≤ t.size), n.toNat = N → ∀ (buf ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k),
    ∃ L : List UInt8, (fermentRun t hs pos n buf h).data.toList = buf.data.toList ++ L ∧
      fermentRunPut hk hm t hs pos n h ring o hr = putList hk hm ring o hr L ∧ L.length = n.toNat := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro pos n h hN buf ring o hr
    rw [fermentRun, fermentRunPut]
    by_cases hn : n = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      exact ⟨[], by rw [List.append_nil], rfl, by rw [hn]; rfl⟩
    · rw [dite_eq_right hn, dite_eq_right hn]
      have hnz := usize_ne hn
      obtain ⟨L1, e1, p1, l1⟩ := fermentPut_mirror hk hm t hs pos n h hnz buf ring o hr
      have hu := fermentUsed_bounds (t.uget pos (by omega)) hnz
      have hq : (n - fermentUsed (t.uget pos (by omega)) n).toNat =
          n.toNat - (fermentUsed (t.uget pos (by omega)) n).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
      have hp : (pos + fermentUsed (t.uget pos (by omega)) n).toNat =
          pos.toNat + (fermentUsed (t.uget pos (by omega)) n).toNat := usize_add_small (by omega)
      obtain ⟨L2, e2, p2, l2⟩ := ih (n - fermentUsed (t.uget pos (by omega)) n).toNat (by rw [hq]; omega)
        (pos + fermentUsed (t.uget pos (by omega)) n) (n - fermentUsed (t.uget pos (by omega)) n)
        (by rw [hp, hq]; omega) rfl (fermentPush t hs pos n buf h hnz)
        (fermentPut hk hm t hs pos n h hnz ring o hr) (o + fermentUsed (t.uget pos (by omega)) n)
        (fermentPut_size hk hm t hs pos n h hnz ring o hr)
      refine ⟨L1 ++ L2, by rw [e2, e1, List.append_assoc], ?_, by rw [List.length_append, l1, l2, hq]; omega⟩
      rw [p2, putList_append]
      exact putList_congr hk hm p1 (by rw [l1, USize.ofNat_toNat])

/-- How many bytes the transform's elementary part leaves of a word of `len` bytes. -/
@[inline] def elemLen (kind k : UInt8) (len : USize) : USize :=
  if kind < 3 then len else len - usmin len k.toUSize

/-- What `elementStep` adds to a buffer, stored in the window instead, from position `o` on. -/
def elemPut (t : ByteArray) (hs : t.size < 2 ^ 24) (kind amt : UInt8) (off len : USize)
    (h : off.toNat + len.toNat ≤ t.size) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) : ByteArray :=
  if kind = 0 then putRun hk hm t hs off len h ring o hr
  else if kind = 1 then
    if hn : len = 0 then ring
    else
      have hnz := usize_ne hn
      have hu := fermentUsed_bounds (t.uget off (by omega)) hnz
      have hp : (off + fermentUsed (t.uget off (by omega)) len).toNat =
          off.toNat + (fermentUsed (t.uget off (by omega)) len).toNat := by exact usize_add_small (by omega)
      have hq : (len - fermentUsed (t.uget off (by omega)) len).toNat =
          len.toNat - (fermentUsed (t.uget off (by omega)) len).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
      putRun hk hm t hs (off + fermentUsed (t.uget off (by omega)) len) (len - fermentUsed (t.uget off (by omega)) len)
        (by rw [hp, hq]; omega) (fermentPut hk hm t hs off len h hnz ring o hr)
        (o + fermentUsed (t.uget off (by omega)) len) (fermentPut_size hk hm t hs off len h hnz ring o hr)
  else if kind = 2 then fermentRunPut hk hm t hs off len h ring o hr
  else if kind = 3 then
    have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
    have hub : amt.toNat < 256 := amt.toNat_lt
    have hp : (off + usmin len amt.toUSize).toNat = off.toNat + min len.toNat amt.toNat := by
      rw [usize_add_small (by rw [hmin]; omega), hmin]
    have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
    putRun hk hm t hs (off + usmin len amt.toUSize) (len - usmin len amt.toUSize) (by rw [hp, hq]; omega) ring o hr
  else
    have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
    have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
    putRun hk hm t hs off (len - usmin len amt.toUSize) (by rw [hq]; omega) ring o hr

/-- `elemPut` stores what `elementStep` adds. -/
theorem elemPut_mirror (t : ByteArray) (hs : t.size < 2 ^ 24) (kind amt : UInt8) (off len : USize)
    (h : off.toNat + len.toNat ≤ t.size) (buf ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    ∃ L : List UInt8, (elementStep t hs kind amt off len buf h).data.toList = buf.data.toList ++ L ∧
      elemPut hk hm t hs kind amt off len h ring o hr = putList hk hm ring o hr L ∧
      L.length = (elemLen kind amt len).toNat := by
  have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
  have hub : amt.toNat < 256 := amt.toNat_lt
  have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
  unfold elementStep elemPut elemLen
  by_cases h0 : kind = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (show (0 : UInt8) < 3 by decide), emitRun_data _ _ h,
      putRun_eq hk hm t hs _ off len h ring o hr rfl]
    exact ⟨_, rfl, rfl, take_drop_length h⟩
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h1 : kind = 1
  · subst h1
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (show (1 : UInt8) < 3 by decide)]
    by_cases hn : len = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      exact ⟨[], by rw [List.append_nil], rfl, by rw [hn]; rfl⟩
    · rw [dite_eq_right hn, dite_eq_right hn]
      dsimp only
      have hnz := usize_ne hn
      obtain ⟨L1, e1, p1, l1⟩ := fermentPut_mirror hk hm t hs off len h hnz buf ring o hr
      have hu := fermentUsed_bounds (t.uget off (by omega)) hnz
      have hp : (off + fermentUsed (t.uget off (by omega)) len).toNat =
          off.toNat + (fermentUsed (t.uget off (by omega)) len).toNat := usize_add_small (by omega)
      have hq' : (len - fermentUsed (t.uget off (by omega)) len).toNat =
          len.toNat - (fermentUsed (t.uget off (by omega)) len).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
      refine ⟨L1 ++ (t.data.toList.drop (off + fermentUsed (t.uget off (by omega)) len).toNat).take
        (len - fermentUsed (t.uget off (by omega)) len).toNat, ?_, ?_, ?_⟩
      · rw [emitRun_data _ _ (by rw [hp, hq']; omega), e1, List.append_assoc]
      · rw [putRun_eq hk hm t hs _ _ _ _ _ _ _ rfl, putList_append]
        exact putList_congr hk hm p1 (by rw [l1, USize.ofNat_toNat])
      · rw [List.length_append, take_drop_length (by rw [hp, hq']; omega), l1, hq']
        omega
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases h2 : kind = 2
  · subst h2
    rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left (show (2 : UInt8) < 3 by decide)]
    exact fermentRunPut_mirror hk hm t hs _ off len h rfl buf ring o hr
  rw [ite_eq_right h2, ite_eq_right h2]
  have hk3 : ¬ kind < 3 := fun e => by
    have e' := UInt8.lt_iff_toNat_lt.mp e
    have a0 : kind.toNat ≠ 0 := fun x => h0 (UInt8.toNat_inj.mp (by rw [x]; rfl))
    have a1 : kind.toNat ≠ 1 := fun x => h1 (UInt8.toNat_inj.mp (by rw [x]; rfl))
    have a2 : kind.toNat ≠ 2 := fun x => h2 (UInt8.toNat_inj.mp (by rw [x]; rfl))
    rw [show (3 : UInt8).toNat = 3 from rfl] at e'
    omega
  rw [ite_eq_right hk3]
  by_cases h3 : kind = 3
  · subst h3
    rw [ite_eq_left rfl, ite_eq_left rfl]
    dsimp only
    have hp : (off + usmin len amt.toUSize).toNat = off.toNat + min len.toNat amt.toNat := by
      rw [usize_add_small (by rw [hmin]; omega), hmin]
    rw [emitRun_data _ _ (by rw [hp, hq]; omega), putRun_eq hk hm t hs _ _ _ _ _ _ _ rfl]
    exact ⟨_, rfl, rfl, take_drop_length (by rw [hp, hq]; omega)⟩
  · rw [ite_eq_right h3, ite_eq_right h3]
    rw [emitRun_data _ _ (by rw [hq]; omega), putRun_eq hk hm t hs _ _ _ _ _ _ _ rfl]
    exact ⟨_, rfl, rfl, take_drop_length (by rw [hq]; omega)⟩

theorem elemPut_size (t : ByteArray) (hs : t.size < 2 ^ 24) (kind amt : UInt8) (off len : USize)
    (h : off.toNat + len.toNat ≤ t.size) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    (elemPut hk hm t hs kind amt off len h ring o hr).size = 2 ^ k := by
  obtain ⟨L, -, e, -⟩ := elemPut_mirror hk hm t hs kind amt off len h ByteArray.empty ring o hr
  rw [e]
  exact putList_size hk hm _ _ _ _

end

theorem base_toNat {id : USize} (hid : id.toNat < 121) : (id * USize.ofNat 32).toNat = 32 * id.toNat := by
  rw [USize.toNat_mul, usize_lit (by decide), Nat.mul_comm, ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- Builds a word: the transform's prefix, its elementary part on the base word, and its suffix. -/
def buildWord (id off len : USize) (hid : id.toNat < 121) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hs : dictBytes.size < 2 ^ 24) : ByteArray :=
  let base := id * USize.ofNat 32
  have hb := base_toNat hid
  have hsz := transLut_size
  have h0 : base.toNat < transLut.size := by
    show (id * USize.ofNat 32).toNat < _
    omega
  have h1 : (base + USize.ofNat 1).toNat < transLut.size := by
    rw [usize_plus (by decide) (by show (id * USize.ofNat 32).toNat < _; omega)]
    show (id * USize.ofNat 32).toNat + 1 < _
    omega
  have h2 : (base + USize.ofNat 2).toNat < transLut.size := by
    rw [usize_plus (by decide) (by show (id * USize.ofNat 32).toNat < _; omega)]
    show (id * USize.ofNat 32).toNat + 2 < _
    omega
  have h3 : (base + USize.ofNat 3).toNat < transLut.size := by
    rw [usize_plus (by decide) (by show (id * USize.ofNat 32).toNat < _; omega)]
    show (id * USize.ofNat 32).toNat + 3 < _
    omega
  let kind := transLut.uget base h0
  let k := transLut.uget (base + USize.ofNat 1) h1
  let pl := transLut.uget (base + USize.ofNat 2) h2
  let sl := transLut.uget (base + USize.ofNat 3) h3
  let b0 := emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat
  let b1 := elementStep dictBytes hs kind k off len b0 h
  emitRun transLut b1 (base + USize.ofNat 4 + pl.toUSize).toNat sl.toNat

/-- What `buildWord` does: the spec's transform of the run. -/
theorem buildWord_spec {id off len : USize} {hid : id.toNat < 121} {h : off.toNat + len.toNat ≤ dictBytes.size}
    {hs : dictBytes.size < 2 ^ 24} {t : WordTransform} (ht : transforms[id.toNat]? = some t) :
    (buildWord id off len hid h hs).data.toList.map UInt8.toNat = applyTransform t (slice dictBytes off.toNat len.toNat) := by
  have hb := base_toNat hid
  have hsz := transLut_size
  have htm := List.mem_of_getElem? ht
  have hlen := rowNat_length htm
  have hrow := rows_ok t htm
  have hplus : ∀ n, n < 2 ^ 16 → (id * USize.ofNat 32 + USize.ofNat n).toNat = 32 * id.toNat + n := by
    intro n hn
    rw [usize_plus hn (by omega), hb]
  have hget : ∀ j, j < 32 → (i : USize) → i.toNat = 32 * id.toNat + j → (hb' : i.toNat < transLut.size) →
      (transLut.uget i hb').toNat = (rowNat t).getD j 0 := fun j hj i hi hb' => row_byte ht hj hi hb'
  unfold buildWord
  dsimp only
  have hkind := hget 0 (by decide) (id * USize.ofNat 32) (by omega) (by omega)
  have hk := hget 1 (by decide) (id * USize.ofNat 32 + USize.ofNat 1) (hplus 1 (by decide)) (by rw [hplus 1 (by decide)]; omega)
  have hpl := hget 2 (by decide) (id * USize.ofNat 32 + USize.ofNat 2) (hplus 2 (by decide)) (by rw [hplus 2 (by decide)]; omega)
  have hsl := hget 3 (by decide) (id * USize.ofNat 32 + USize.ofNat 3) (hplus 3 (by decide)) (by rw [hplus 3 (by decide)]; omega)
  have e0 : (rowNat t).getD 0 0 = (elemCode t.elementary).1 := by simp [rowNat]
  have e1 : (rowNat t).getD 1 0 = (elemCode t.elementary).2 := by simp [rowNat]
  have e2 : (rowNat t).getD 2 0 = (bytes t.prefixString).length := by simp [rowNat]
  have e3 : (rowNat t).getD 3 0 = (bytes t.suffixString).length := by simp [rowNat]
  rw [e0] at hkind
  rw [e1] at hk
  rw [e2] at hpl
  rw [e3] at hsl
  generalize transLut.uget (id * USize.ofNat 32) _ = kind at hkind ⊢
  generalize transLut.uget (id * USize.ofNat 32 + USize.ofNat 1) _ = k at hk ⊢
  generalize transLut.uget (id * USize.ofNat 32 + USize.ofNat 2) _ = pl at hpl ⊢
  generalize transLut.uget (id * USize.ofNat 32 + USize.ofNat 3) _ = sl at hsl ⊢
  have hplU : (id * USize.ofNat 32 + USize.ofNat 4 + pl.toUSize).toNat = 32 * id.toNat + (4 + pl.toNat) := by
    rw [usize_add_small (by rw [hplus 4 (by decide), u8_usize]; omega), hplus 4 (by decide), u8_usize]
    omega
  have hfour := hplus 4 (by decide)
  rw [emit_slice _ _ (by rw [hplU, hsz]; omega), hplU, elementStep_spec h hkind.symm hk.symm,
    emit_slice _ _ (by rw [hfour, hsz]; omega), hfour]
  have hempty : (freshBytes 38).data.toList.map UInt8.toNat = [] := rfl
  rw [hempty, List.nil_append, row_slice ht 4 pl.toNat (by omega), row_slice ht (4 + pl.toNat) sl.toNat (by omega), hpl, hsl,
    row_prefix, row_suffix]
  rfl

/-- Slot `i` of the word length table: `NDBITS`, then `DOFFSET` above it. -/
def lenEntry (i : Nat) : Nat :=
  NDBITS.getD i 0 + 256 * DOFFSET i

/-- Byte `j` of the word length table. -/
def lenByte (j : Nat) : Nat :=
  (lenEntry (j / 4) >>> (8 * (j % 4))) &&& 255

/-- The word length table. -/
def lenLut : ByteArray :=
  ((List.range 100).map fun j => (lenByte j).toUInt8).toByteArray

theorem lenLut_size : lenLut.size = 100 := by
  simp [lenLut, List.size_toByteArray]

private theorem lenLut_size32 : lenLut.size < 2 ^ 32 := by
  rw [lenLut_size]
  decide

private theorem lenLut_byte {j : Nat} (h : j < 100) : (lenLut.data[j]?.getD 0).toNat = lenByte j := by
  have hb : lenByte j < 256 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  simp only [lenLut, List.data_toByteArray]
  simp [h]
  omega

private theorem len_whole : ∀ i, i < 25 →
    lenByte (4 * i) + 256 * lenByte (4 * i + 1) + 65536 * lenByte (4 * i + 2) + 16777216 * lenByte (4 * i + 3) = lenEntry i := by
  decide +kernel

private theorem len_small : ∀ i, i < 25 → NDBITS.getD i 0 ≤ 11 ∧ DOFFSET i ≤ 122784 := by
  decide +kernel

/-- A word length's slot. -/
@[inline] def lenRow (c : UInt64) (hc : c.toNat < 25) : UInt64 :=
  slotWord lenLut c.toUSize
    (by
      rw [word_toUSize (by omega), lenLut_size]
      omega) (by exact lenLut_size32)

/-- What a word length's slot holds. -/
theorem lenRow_fields {c : UInt64} (hc : c.toNat < 25) :
    (rowBits (lenRow c hc)).toNat = NDBITS.getD c.toNat 0 ∧ (rowBase (lenRow c hc)).toNat = DOFFSET c.toNat := by
  have hs := len_small _ hc
  have hv : (lenRow c hc).toNat = NDBITS.getD c.toNat 0 + 256 * DOFFSET c.toNat := by
    unfold lenRow
    rw [slotWord_toNat, word_toUSize (by omega)]
    unfold u32At
    rw [lenLut_byte (by omega), lenLut_byte (by omega), lenLut_byte (by omega), lenLut_byte (by omega)]
    exact len_whole _ hc
  constructor
  · unfold rowBits
    rw [UInt64.toNat_and, show (255 : UInt64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hv]
    omega
  · unfold rowBase
    rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftRight_eq_div_pow, hv]
    show (NDBITS.getD c.toNat 0 + 256 * DOFFSET c.toNat) / 256 = _
    omega

theorem lt25 {clen : UInt64} (h : 4 ≤ clen ∧ clen ≤ 24) : clen.toNat < 25 := by
  have := UInt64.le_iff_toNat_le.mp h.2
  rw [show (24 : UInt64).toNat = 24 from rfl] at this
  omega

theorem ge4 {clen : UInt64} (h : 4 ≤ clen ∧ clen ≤ 24) : 4 ≤ clen.toNat := by
  have := UInt64.le_iff_toNat_le.mp h.1
  rwa [show (4 : UInt64).toNat = 4 from rfl] at this

theorem lt121 {t : UInt64} (h : t < 121) : t.toNat < 121 := by
  have := UInt64.lt_iff_toNat_lt.mp h
  rwa [show (121 : UInt64).toNat = 121 from rfl] at this

/-- The word ID's transform, from a word length's slot. -/
@[inline] def dictTid (row wordId : UInt64) : UInt64 := wordId >>> rowBits row

/-- Whether a dictionary reference is valid: its length, and the transform its word ID gives. -/
def dictValid (clen wordId : UInt64) : Prop :=
  ∃ h : 4 ≤ clen ∧ clen ≤ 24, dictTid (lenRow clen (lt25 h)) wordId < 121

@[inline] instance (clen wordId : UInt64) : Decidable (dictValid clen wordId) :=
  if h : 4 ≤ clen ∧ clen ≤ 24 then
    if ht : dictTid (lenRow clen (lt25 h)) wordId < 121 then isTrue ⟨h, ht⟩
    else isFalse fun ⟨_, e⟩ => ht e
  else isFalse fun ⟨e, _⟩ => h e

/-- The word index's byte offset, from a word length's slot. -/
@[inline] def dictOff (row clen wordId : UInt64) : UInt64 :=
  rowBase row + (wordId &&& (((1 : UInt64) <<< rowBits row) - 1)) * clen

theorem dict_parts {clen wordId row : UInt64} (h4 : 4 ≤ clen.toNat) (h24 : clen.toNat ≤ 24)
    (hb : (rowBits row).toNat = NDBITS.getD clen.toNat 0) (hbase : (rowBase row).toNat = DOFFSET clen.toNat) :
    (dictTid row wordId).toNat = wordId.toNat >>> NDBITS.getD clen.toNat 0 ∧
      (dictOff row clen wordId).toNat = wordOffset clen.toNat (wordId.toNat % NWORDS clen.toNat) ∧
      (dictOff row clen wordId).toNat + clen.toNat ≤ 122784 := by
  have hs := len_small clen.toNat (by omega)
  have hle := wordOffset_le clen.toNat (by omega) h4
  have hsize := DICTSIZE_eq.1
  rw [hsize] at hle
  have hnw : NWORDS clen.toNat = 2 ^ NDBITS.getD clen.toNat 0 := by
    unfold NWORDS
    rw [ite_eq_right (by omega), Nat.shiftLeft_eq, Nat.one_mul]
  have hb64 : (rowBits row).toNat < 64 := by omega
  have hone : ((1 : UInt64) <<< rowBits row).toNat = 2 ^ NDBITS.getD clen.toNat 0 := by
    have hp : 2 ^ (rowBits row).toNat ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (by omega)
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt hb64, show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul, hb]
    rw [hb] at hp
    exact Nat.mod_eq_of_lt (by
      have : (2 : Nat) ^ 11 = 2048 := by decide
      omega)
  have hpos : 1 ≤ 2 ^ NDBITS.getD clen.toNat 0 := Nat.two_pow_pos _
  have hmask : (((1 : UInt64) <<< rowBits row) - 1).toNat = 2 ^ NDBITS.getD clen.toNat 0 - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hone]; exact hpos)), hone]
    rfl
  have hidx : (wordId &&& (((1 : UInt64) <<< rowBits row) - 1)).toNat = wordId.toNat % NWORDS clen.toNat := by
    rw [UInt64.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod, hnw]
  have hnpos : 0 < NWORDS clen.toNat := by
    rw [hnw]
    exact Nat.two_pow_pos _
  have hlt : wordId.toNat % NWORDS clen.toNat < NWORDS clen.toNat := Nat.mod_lt _ hnpos
  have hmul : (wordId.toNat % NWORDS clen.toNat + 1) * clen.toNat ≤ NWORDS clen.toNat * clen.toNat :=
    Nat.mul_le_mul_right _ hlt
  rw [Nat.add_mul, Nat.one_mul] at hmul
  unfold wordOffset at hle
  have hprod : ((wordId &&& (((1 : UInt64) <<< rowBits row) - 1)) * clen).toNat = (wordId.toNat % NWORDS clen.toNat) * clen.toNat := by
    rw [UInt64.toNat_mul, hidx]
    exact Nat.mod_eq_of_lt (by
      have : (122784 : Nat) < 2 ^ 64 := by decide
      omega)
  have hoff : (dictOff row clen wordId).toNat = wordOffset clen.toNat (wordId.toNat % NWORDS clen.toNat) := by
    unfold dictOff wordOffset
    rw [UInt64.toNat_add, hbase, hprod]
    exact Nat.mod_eq_of_lt (by
      have : (122784 : Nat) < 2 ^ 64 := by decide
      omega)
  refine ⟨?_, hoff, ?_⟩
  · unfold dictTid
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hb64, hb]
  · rw [hoff]
    unfold wordOffset
    omega

/-- A valid dictionary reference's word ID is below `2 ^ 18`: one of 121 transforms of at most `2 ^ 11` words. -/
theorem dictValid_lt {clen wordId : UInt64} (h : dictValid clen wordId) : wordId.toNat < 2 ^ 18 := by
  obtain ⟨hc, ht⟩ := h
  have hl := lt25 hc
  obtain ⟨h1, -, -⟩ := dict_parts (wordId := wordId) (ge4 hc) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
  have ht' := lt121 ht
  rw [h1, Nat.shiftRight_eq_div_pow] at ht'
  have hp : 2 ^ NDBITS.getD clen.toNat 0 ≤ 2 ^ 11 := Nat.pow_le_pow_right (by decide) (len_small _ hl).1
  have hw := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mp ht'
  have hm := Nat.mul_le_mul_left 121 hp
  have h11 : (2 : Nat) ^ 11 = 2048 := rfl
  have h18 : (2 : Nat) ^ 18 = 262144 := rfl
  omega

theorem dictBytes_small : dictBytes.size < 2 ^ 24 := by
  rw [dictBytes_size]
  decide

private theorem clen_usize {clen : UInt64} (h : clen.toNat < 25) : clen.toUSize.toNat = clen.toNat :=
  word_toUSize (by omega)

/-- Builds the word of a valid dictionary reference. -/
def dictBuild (clen wordId : UInt64) (h : dictValid clen wordId) : ByteArray :=
  have hc := h.1
  have hl := lt25 hc
  have hp := dict_parts (wordId := wordId) (ge4 hc) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
  buildWord (dictTid (lenRow clen hl) wordId).toUSize (dictOff (lenRow clen hl) clen wordId).toUSize clen.toUSize
    (by
      have ht := lt121 h.2
      rw [word_toUSize (by omega)]
      exact ht)
    (by
      rw [word_toUSize (by omega), clen_usize hl, dictBytes_size]
      exact hp.2.2)
    dictBytes_small

/-- `dictValid` and `dictBuild` are the spec's `dictionaryWord`. -/
theorem dictBuild_spec {clen wordId : UInt64} {distance maxDistance : Nat} (hw : wordId.toNat = distance - (maxDistance + 1)) :
    dictionaryWord clen.toNat distance maxDistance =
      if h : dictValid clen wordId then some ((dictBuild clen wordId h).data.toList.map UInt8.toNat) else none := by
  by_cases h : dictValid clen wordId
  · rw [dite_eq_left h]
    have hc := h.1
    have hl := lt25 hc
    have h4 := ge4 hc
    obtain ⟨h1, h2, h3⟩ := dict_parts (wordId := wordId) h4 (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
    have ht := lt121 h.2
    rw [h1] at ht
    have hlt : wordId.toNat >>> NDBITS.getD clen.toNat 0 < transforms.length := by
      rw [transforms_length]
      exact ht
    obtain ⟨t, hget⟩ : ∃ t, transforms[wordId.toNat >>> NDBITS.getD clen.toNat 0]? = some t :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    have hgetU : transforms[(dictTid (lenRow clen hl) wordId).toUSize.toNat]? = some t := by
      rw [word_toUSize (by rw [h1]; omega), h1]
      exact hget
    unfold dictionaryWord dictBuild
    rw [ite_eq_right (by omega), buildWord_spec hgetU]
    dsimp only
    rw [← hw, hget, word_toUSize (by omega), clen_usize hl, h2, dict_slice (by rw [← h2]; exact h3)]
    rfl
  · rw [dite_eq_right h]
    unfold dictionaryWord
    by_cases hc : 4 ≤ clen ∧ clen ≤ 24
    · have hl := lt25 hc
      have h4 := ge4 hc
      obtain ⟨h1, -, -⟩ := dict_parts (wordId := wordId) h4 (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
      have hge : ¬ dictTid (lenRow clen hl) wordId < 121 := fun e => h ⟨hc, e⟩
      have hge' : 121 ≤ wordId.toNat >>> NDBITS.getD clen.toNat 0 := by
        rw [← h1]
        exact Nat.le_of_not_lt fun e => hge (UInt64.lt_iff_toNat_lt.mpr (by rw [show (121 : UInt64).toNat = 121 from rfl]; exact e))
      rw [ite_eq_right (by omega)]
      dsimp only
      rw [← hw, List.getElem?_eq_none (by rw [transforms_length]; exact hge')]
      rfl
    · have hout : clen.toNat < 4 ∨ 24 < clen.toNat := by
        rcases Nat.lt_or_ge clen.toNat 4 with h1 | h1
        · exact Or.inl h1
        · rcases Nat.lt_or_ge 24 clen.toNat with h2 | h2
          · exact Or.inr h2
          · exact absurd ⟨UInt64.le_iff_toNat_le.mpr (by rw [show (4 : UInt64).toNat = 4 from rfl]; exact h1),
              UInt64.le_iff_toNat_le.mpr (by rw [show (24 : UInt64).toNat = 24 from rfl]; exact h2)⟩ hc
      rw [ite_eq_left hout]

/-! ### A word's length, and the word written straight into the window

The fast command loop takes a dictionary word itself: its length from the transform's row alone (`dictLen`), and its
bytes stored straight into the window (`dictPutW`), with no word built. `dictLen_eq` proves the length the built word's.
`dictPutW_spec` proves the window the one `putList` leaves with the built word, but perhaps for the 8 bytes after it;
`wordRun_put` shows `putList` is what the step machine's word loop leaves.
-/

/-- A byte of a transform's row. -/
private theorem row_at {id : USize} (hid : id.toNat < 121) {j : Nat} (hj : j < 32) :
    (id * USize.ofNat 32 + USize.ofNat j).toNat = 32 * id.toNat + j ∧ 32 * id.toNat + j < transLut.size := by
  have hb := base_toNat hid
  have hsz := transLut_size
  rw [usize_plus (by omega) (by omega), hb]
  exact ⟨rfl, by omega⟩

/-- A transform's prefix and suffix lengths, as the row holds them, are 13 bytes at most together. -/
private theorem affix_uget {id : USize} (hid : id.toNat < 121) (h2 : (id * USize.ofNat 32 + USize.ofNat 2).toNat < transLut.size)
    (h3 : (id * USize.ofNat 32 + USize.ofNat 3).toNat < transLut.size) :
    (transLut.uget (id * USize.ofNat 32 + USize.ofNat 2) h2).toNat +
      (transLut.uget (id * USize.ofNat 32 + USize.ofNat 3) h3).toNat ≤ 13 := by
  have e : ∀ (i : USize) (hi : i.toNat < transLut.size), transLut.uget i hi = transLut.data[i.toNat]?.getD 0 := by
    intro i hi
    generalize transLut = t at hi
    cases t with
    | mk bs =>
      have h' : i.toNat < bs.size := hi
      show bs[i.toNat]'h' = (bs[i.toNat]?).getD 0
      rw [Array.getElem?_eq_getElem h']
      rfl
  rw [e, e, (row_at hid (j := 2) (by decide)).1, (row_at hid (j := 3) (by decide)).1]
  exact affix_le hid

theorem row_lt {id : USize} (hid : id.toNat < 121) {j : Nat} (hj : j < 32) :
    (id * USize.ofNat 32 + USize.ofNat j).toNat < transLut.size := by
  rw [(row_at hid hj).1]
  exact (row_at hid hj).2

theorem base_lt {id : USize} (hid : id.toNat < 121) : (id * USize.ofNat 32).toNat < transLut.size := by
  have := base_toNat hid
  have := transLut_size
  omega

private theorem u8_ofNat (x : UInt8) : x.toUSize = USize.ofNat x.toNat :=
  USize.toNat_inj.mp (by rw [u8_usize, usize_lit (by have := x.toNat_lt; omega)])

theorem elemLen_le (kind amt : UInt8) (len : USize) : (elemLen kind amt len).toNat ≤ len.toNat := by
  unfold elemLen
  split
  · exact Nat.le_refl _
  · rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [usmin_toNat]; omega))]
    omega

/-- The length of a word from its transform's fields: prefix, elementary part and suffix. -/
@[inline] def wordLenF (kind amt pl sl : UInt8) (len : USize) : USize :=
  pl.toUSize + elemLen kind amt len + sl.toUSize

/-- The length of the word of transform `id` on a base word of `len` bytes. -/
@[inline] def wordLenB (id len : USize) (hid : id.toNat < 121) : USize :=
  wordLenF (transLut.uget (id * USize.ofNat 32) (base_lt hid))
    (transLut.uget (id * USize.ofNat 32 + USize.ofNat 1) (row_lt hid (by decide)))
    (transLut.uget (id * USize.ofNat 32 + USize.ofNat 2) (row_lt hid (by decide)))
    (transLut.uget (id * USize.ofNat 32 + USize.ofNat 3) (row_lt hid (by decide))) len

section
variable {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)

/-- A word stored in the window from position `o` on, from its transform's fields (the row at `base`): the prefix, the
elementary part on the base word, the suffix. -/
def wordPutF (base off len : USize) (kind amt pl sl : UInt8)
    (hB : (base + USize.ofNat 4).toNat + pl.toNat + sl.toNat ≤ transLut.size)
    (h : off.toNat + len.toNat ≤ dictBytes.size) (hs : dictBytes.size < 2 ^ 24) (ring : ByteArray) (o : USize)
    (hr : ring.size = 2 ^ k) : ByteArray :=
  have hsz := transLut_size
  have hlt : transLut.size < 2 ^ 24 := by omega
  have hpl : pl.toUSize.toNat = pl.toNat := by exact u8_usize pl
  have hsl : sl.toUSize.toNat = sl.toNat := by exact u8_usize sl
  have hp4 : (base + USize.ofNat 4 + pl.toUSize).toNat = (base + USize.ofNat 4).toNat + pl.toNat := by
    rw [usize_add_small (by rw [hpl]; omega), hpl]
  let r0 := putRun hk hm transLut hlt (base + USize.ofNat 4) pl.toUSize (by rw [hpl]; omega) ring o hr
  let r1 := elemPut hk hm dictBytes hs kind amt off len h r0 (o + pl.toUSize) (putRun_size hk hm _ _ _ _ _ _ _ _)
  putRun hk hm transLut hlt (base + USize.ofNat 4 + pl.toUSize) sl.toUSize (by rw [hp4, hsl]; omega) r1
    (o + pl.toUSize + elemLen kind amt len) (elemPut_size hk hm _ _ _ _ _ _ _ _ _ _)

/-- `wordPutF` stores the word `buildWord` builds from the same fields, and `wordLenF` is its length. -/
theorem wordPutF_eq (base off len : USize) (kind amt pl sl : UInt8)
    (hB : (base + USize.ofNat 4).toNat + pl.toNat + sl.toNat ≤ transLut.size)
    (h : off.toNat + len.toNat ≤ dictBytes.size) (hs : dictBytes.size < 2 ^ 24) (ring : ByteArray) (o : USize)
    (hr : ring.size = 2 ^ k) :
    let w := emitRun transLut (elementStep dictBytes hs kind amt off len
      (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat) h) (base + USize.ofNat 4 + pl.toUSize).toNat
      sl.toNat
    wordPutF hk hm base off len kind amt pl sl hB h hs ring o hr = putList hk hm ring o hr w.data.toList ∧
      (wordLenF kind amt pl sl len).toNat = w.size := by
  intro w
  have hsz := transLut_size
  have hlt : transLut.size < 2 ^ 24 := by omega
  have hpl : pl.toUSize.toNat = pl.toNat := u8_usize pl
  have hsl : sl.toUSize.toNat = sl.toNat := u8_usize sl
  have hp4 : (base + USize.ofNat 4 + pl.toUSize).toNat = (base + USize.ofNat 4).toNat + pl.toNat := by
    rw [usize_add_small (by rw [hpl]; omega), hpl]
  have hP := emitRun_data transLut (freshBytes 38) (start := (base + USize.ofNat 4).toNat) (len := pl.toNat)
    (by omega)
  have hfresh : (freshBytes 38).data.toList = [] := rfl
  rw [hfresh, List.nil_append] at hP
  have hr0 := putRun_size hk hm transLut hlt (base + USize.ofNat 4) pl.toUSize (by rw [hpl]; omega) ring o hr
  obtain ⟨E, eE, pE, lE⟩ := elemPut_mirror hk hm dictBytes hs kind amt off len h
    (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat)
    (putRun hk hm transLut hlt (base + USize.ofNat 4) pl.toUSize (by rw [hpl]; omega) ring o hr) (o + pl.toUSize) hr0
  have hS := emitRun_data transLut (elementStep dictBytes hs kind amt off len
    (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat) h)
    (start := (base + USize.ofNat 4 + pl.toUSize).toNat) (len := sl.toNat) (by rw [hp4]; omega)
  rw [eE, hP] at hS
  have lP : ((transLut.data.toList.drop (base + USize.ofNat 4).toNat).take pl.toNat).length = pl.toNat :=
    take_drop_length (by omega)
  have lS : ((transLut.data.toList.drop (base + USize.ofNat 4 + pl.toUSize).toNat).take sl.toNat).length = sl.toNat :=
    take_drop_length (by rw [hp4]; omega)
  have hel := elemLen_le kind amt len
  have hd : dictBytes.size < 2 ^ 24 := hs
  refine ⟨?_, ?_⟩
  · show _ = putList hk hm ring o hr w.data.toList
    unfold wordPutF
    dsimp only
    rw [show w.data.toList = _ from hS, putList_append,
      putRun_eq hk hm transLut hlt _ (base + USize.ofNat 4 + pl.toUSize) sl.toUSize _ _ _ _ rfl, hsl]
    refine putList_congr hk hm ?_ ?_
    · rw [pE, putList_append]
      refine putList_congr hk hm ((putRun_eq hk hm transLut hlt _ _ _ _ _ _ _ rfl).trans (by rw [hpl])) ?_
      rw [lP, ← u8_ofNat]
    · rw [List.length_append, USize.ofNat_add, lP, lE, USize.ofNat_toNat, ← u8_ofNat, USize.add_assoc]
  · show _ = w.data.size
    rw [← Array.length_toList, show w.data.toList = _ from hS, List.length_append, List.length_append, lP, lE, lS]
    unfold wordLenF
    rw [usize_add_small (by rw [usize_add_small (by rw [hpl]; omega), hpl, hsl]; omega),
      usize_add_small (by rw [hpl]; omega), hpl, hsl]

end

/-! ### The word in 8-byte blocks

Where the word and the 8 bytes after it fit before the window's end, the word is written in 8-byte blocks, each one load
from `transLut` or `dictBytes` and one store in the window: the prefix, the base word and the suffix, each part from the
exact end of the one before, so that only the last part's overrun stays, in the 8 bytes after the word (`WritesJ`). -/

/-- A run of `n` bytes of `t` from `p`. -/
@[reducible] def runBytes (t : ByteArray) (p n : Nat) : List UInt8 := (t.data.toList.drop p).take n

theorem runBytes_add (t : ByteArray) (p a b : Nat) :
    runBytes t p (a + b) = runBytes t p a ++ runBytes t (p + a) b := by
  unfold runBytes
  rw [List.take_add, List.drop_drop]

theorem runBytes_length {t : ByteArray} {p n : Nat} (h : p + n ≤ t.size) : (runBytes t p n).length = n :=
  take_drop_length h

theorem runBytes_8 {t : ByteArray} {p n : Nat} (h : 8 ≤ n) :
    runBytes t p 8 ++ runBytes t (p + 8) (n - 8) = runBytes t p n := by
  rw [← runBytes_add]
  congr 1
  omega

theorem runBytes_get {t : ByteArray} {p n j : Nat} (hj : j < n) : (runBytes t p n)[j]? = t.data[p + j]? := by
  unfold runBytes
  rw [List.getElem?_take, ite_eq_left hj, List.getElem?_drop, Array.getElem?_toList]

/-- `R'` holds the bytes `X` from window index `i` on, perhaps other bytes in the 8 after them, and `R`'s bytes
elsewhere. -/
def WritesJ (R R' : ByteArray) (i : Nat) (X : List UInt8) : Prop :=
  R'.size = R.size ∧ ∀ q, (i ≤ q → q < i + X.length → R'.data[q]? = X[q - i]?) ∧
    (q < i ∨ i + X.length + 8 ≤ q → R'.data[q]? = R.data[q]?)

theorem WritesJ.refl (R : ByteArray) (i : Nat) : WritesJ R R i [] :=
  ⟨rfl, fun _ => ⟨fun h1 h2 => absurd h2 (by simp only [List.length_nil]; omega), fun _ => rfl⟩⟩

/-- A window index `≤` a small literal. -/
theorem usize_le_lit {n : USize} {c : Nat} (hc : c < 2 ^ 32) : n ≤ USize.ofNat c ↔ n.toNat ≤ c := by
  rw [USize.le_iff_toNat_le, fastLit hc]

theorem WritesJ.of_eq {R R' : ByteArray} {i : Nat} {X Y : List UInt8} (h : WritesJ R R' i X) (e : X = Y) :
    WritesJ R R' i Y := e ▸ h

theorem WritesJ.trans {R R1 R2 : ByteArray} {i j : Nat} {X Y : List UInt8} (h1 : WritesJ R R1 i X)
    (h2 : WritesJ R1 R2 j Y) (hj : j = i + X.length) : WritesJ R R2 i (X ++ Y) := by
  subst hj
  refine ⟨h2.1.trans h1.1, fun q => ⟨fun hq1 hq2 => ?_, fun hq => ?_⟩⟩
  · rw [List.length_append] at hq2
    by_cases hx : q < i + X.length
    · rw [(h2.2 q).2 (Or.inl hx), (h1.2 q).1 hq1 hx, List.getElem?_append_left (by omega)]
    · rw [(h2.2 q).1 (by omega) (by omega), List.getElem?_append_right (by omega)]
      congr 1
      omega
  · rw [List.length_append] at hq
    rw [(h2.2 q).2 (by omega), (h1.2 q).2 (by omega)]

/-- A write of exactly `X` from `i`. -/
theorem WritesJ.exact {R R' : ByteArray} {i : Nat} {X : List UInt8} (hs : R'.size = R.size)
    (h : ∀ q, R'.data[q]? = if i ≤ q ∧ q < i + X.length then X[q - i]? else R.data[q]?) : WritesJ R R' i X :=
  ⟨hs, fun q => ⟨fun h1 h2 => by rw [h q, ite_eq_left ⟨h1, h2⟩],
    fun hq => by rw [h q, ite_eq_right (show ¬ (i ≤ q ∧ q < i + X.length) by omega)]⟩⟩

private theorem uset_get' (t : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < t.size) (q : Nat) :
    (t.uset i v h).data[q]? = if q = i.toNat then some v else t.data[q]? := by
  by_cases hq : q = i.toNat
  · subst hq
    rw [ite_eq_left rfl]
    have hs : i.toNat < (t.uset i v h).data.size := by
      show i.toNat < (t.uset i v h).size
      rw [size_uset']
      exact h
    have e := uset_get_same (v := v) h
    cases hx : (t.uset i v h).data[i.toNat]? with
    | none => exact absurd hx (by rw [Array.getElem?_eq_getElem hs]; simp)
    | some x =>
      rw [hx] at e
      exact congrArg some e
  · rw [ite_eq_right hq, uset_get_ne h hq]

section
variable {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)

include hk hm in
/-- The window index of `o + c`. -/
theorem add_mask_toNat (o c : USize) : ((o + c) &&& mask).toNat = ((o &&& mask).toNat + c.toNat) % 2 ^ k := by
  have hb : k ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hd : 2 ^ k ∣ 2 ^ System.Platform.numBits := Nat.pow_dvd_pow 2 hb
  rw [USize.toNat_and, USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    USize.toNat_add, Nat.mod_mod_of_dvd _ hd, Nat.mod_add_mod]

/-- The bytes `putList` stores, where they don't reach the window's end. -/
theorem putList_get : ∀ (l : List UInt8) (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k),
    (o &&& mask).toNat + l.length ≤ 2 ^ k → ∀ q, (putList hk hm ring o hs l).data[q]? =
      if (o &&& mask).toNat ≤ q ∧ q < (o &&& mask).toNat + l.length then l[q - (o &&& mask).toNat]? else ring.data[q]?
  | [], ring, o, hs, _, q => by
    rw [ite_eq_right (by simp)]
    rfl
  | x :: l, ring, o, hs, hb, q => by
    have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
    have hlt := mask_lt (i := o) hm
    have hw : ∀ q, (wput ring o mask hk hm hs x).data[q]? =
        if q = (o &&& mask).toNat then some x else ring.data[q]? := by
      intro q
      unfold wput
      rw [uset_get', wix_toNat (by omega)]
    have h1 : (USize.ofNat 1).toNat = 1 := usize_lit (by decide)
    have hn : ((o + USize.ofNat 1) &&& mask).toNat = ((o &&& mask).toNat + 1) % 2 ^ k := by
      rw [add_mask_toNat hk hm, h1]
    rw [putList.eq_2]
    simp only [List.length_cons] at hb ⊢
    by_cases hl : l = []
    · subst hl
      rw [putList.eq_1, hw]
      by_cases hq : q = (o &&& mask).toNat
      · rw [ite_eq_left hq, ite_eq_left ⟨by omega, by simp only [List.length_nil]; omega⟩, hq, Nat.sub_self]
        rfl
      · rw [ite_eq_right hq, ite_eq_right (fun hc => hq (by simp only [List.length_nil] at hc; omega))]
    · have hlen : 1 ≤ l.length := by
        cases l with
        | nil => exact absurd rfl hl
        | cons _ _ => simp
      have hn' : ((o + USize.ofNat 1) &&& mask).toNat = (o &&& mask).toNat + 1 := by
        rw [hn, Nat.mod_eq_of_lt (by omega)]
      rw [putList_get l _ _ _ (by rw [hn']; omega) q, hn', hw]
      by_cases hin : (o &&& mask).toNat + 1 ≤ q ∧ q < (o &&& mask).toNat + 1 + l.length
      · rw [ite_eq_left hin, ite_eq_left (by omega),
          show q - (o &&& mask).toNat = (q - ((o &&& mask).toNat + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [ite_eq_right hin]
        by_cases hq : q = (o &&& mask).toNat
        · rw [ite_eq_left hq, ite_eq_left (by omega), hq, Nat.sub_self, List.getElem?_cons_zero]
        · rw [ite_eq_right hq, ite_eq_right (by omega)]

/-- `putList`, where it doesn't reach the window's end, writes exactly its bytes. -/
theorem putList_writes (l : List UInt8) (ring : ByteArray) (o : USize) (hs : ring.size = 2 ^ k)
    (h : (o &&& mask).toNat + l.length ≤ 2 ^ k) : WritesJ ring (putList hk hm ring o hs l) (o &&& mask).toNat l :=
  WritesJ.exact ((putList_size hk hm l ring o hs).trans hs.symm) (putList_get hk hm l ring o hs h)

end

private theorem leList_toNat (v : UInt64) : ∀ (n j : Nat), j < n →
    ((leList v n)[j]?).map UInt8.toNat = some (v.toNat / 256 ^ j % 256)
  | 0, _, h => absurd h (by omega)
  | n + 1, 0, _ => by
    rw [leList, List.getElem?_cons_zero]
    show some v.toUInt8.toNat = _
    rw [UInt64.toNat_toUInt8, Nat.pow_zero, Nat.div_one]
  | n + 1, j + 1, h => by
    rw [leList, List.getElem?_cons_succ, leList_toNat (v >>> 8) n j (by omega)]
    congr 1
    rw [UInt64.toNat_shiftRight, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftRight_eq_div_pow,
      show (2 : Nat) ^ 8 = 256 from rfl, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

private theorem leAt_byteD (t : ByteArray) : ∀ (n i j : Nat), j < n → (leAt t i n / 256 ^ j) % 256 = byteN t (i + j)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, i, 0, _ => by
    rw [leAt, Nat.pow_zero, Nat.div_one]
    show _ = byteN t i
    have := byteN_lt t i
    omega
  | n + 1, i, j + 1, h => by
    rw [leAt, Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul]
    have hb := byteN_lt t i
    have : (byteN t i + 256 * leAt t (i + 1) n) / 256 = leAt t (i + 1) n := by omega
    rw [this, leAt_byteD t n (i + 1) j (by omega)]
    congr 1
    omega

/-- 8 bytes of `t` from `p`, stored at window index `i`: one 8-byte load and one 8-byte store. -/
@[inline] def blk (t : ByteArray) (p : USize) (hp : p.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) (ring : ByteArray)
    (i : USize) (hi : i.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24) : ByteArray :=
  store64 ring (wix i) (load64 t p hp h32) (by rw [wix_toNat (by omega)]; exact hi)

theorem blk_size (t : ByteArray) (p : USize) (hp : p.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) (ring : ByteArray)
    (i : USize) (hi : i.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24) :
    (blk t p hp h32 ring i hi h24).size = ring.size :=
  storeLE_size _ _ _ _ (by rw [wix_toNat (by omega)]; exact hi)

theorem blk_get (t : ByteArray) (p : USize) (hp : p.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) (ring : ByteArray)
    (i : USize) (hi : i.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24) (q : Nat) :
    (blk t p hp h32 ring i hi h24).data[q]? =
      if i.toNat ≤ q ∧ q < i.toNat + 8 then t.data[p.toNat + (q - i.toNat)]? else ring.data[q]? := by
  have hix : (wix i).toNat = i.toNat := wix_toNat (by omega)
  show (storeLE ring (wix i) (load64 t p hp h32) 8).data[q]? = _
  rw [storeLE_get _ _ _ _ (by rw [hix]; exact hi), hix]
  by_cases hq : i.toNat ≤ q ∧ q < i.toNat + 8
  · rw [ite_eq_left hq, ite_eq_left hq]
    have e := leList_toNat (load64 t p hp h32) 8 (q - i.toNat) (by omega)
    rw [load64_toNat, leAt_byteD t 8 p.toNat (q - i.toNat) (by omega)] at e
    have hlt : p.toNat + (q - i.toNat) < t.data.size := by
      have : t.size = t.data.size := rfl
      omega
    rw [Array.getElem?_eq_getElem hlt]
    revert e
    cases (leList (load64 t p hp h32) 8)[q - i.toNat]? with
    | none => intro e; cases e
    | some x =>
      intro e
      have e' : x.toNat = byteN t (p.toNat + (q - i.toNat)) := Option.some.inj e
      unfold byteN at e'
      rw [Array.getElem?_eq_getElem hlt] at e'
      exact congrArg some (UInt8.toNat_inj.mp e')
  · rw [ite_eq_right hq, ite_eq_right hq]

/-- A block holding a run of at most 8 bytes. -/
theorem blk_writes (t : ByteArray) (p : USize) (hp : p.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) (ring : ByteArray)
    (i : USize) (hi : i.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24) (n : Nat) (hn : n ≤ 8) :
    WritesJ ring (blk t p hp h32 ring i hi h24) i.toNat (runBytes t p.toNat n) := by
  have hl : (runBytes t p.toNat n).length = n := runBytes_length (by omega)
  refine ⟨blk_size t p hp h32 ring i hi h24, fun q => ⟨fun h1 h2 => ?_, fun hq => ?_⟩⟩
  · rw [hl] at h2
    rw [blk_get, ite_eq_left ⟨h1, by omega⟩, runBytes_get (by omega)]
  · rw [hl] at hq
    rw [blk_get, ite_eq_right (by omega)]

/-- A run of at most 16 bytes (an affix), by one block or two. -/
@[inline] def aff2 (t : ByteArray) (p n : USize) (hp : p.toNat + n.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32)
    (ring : ByteArray) (i : USize) (hi : i.toNat + n.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24)
    (hn : n.toNat ≤ 16) : ByteArray :=
  if n = 0 then ring
  else
    let r := blk t p (by omega) h32 ring i (by omega) h24
    have hr : r.size = ring.size := blk_size t p (by omega) h32 ring i (by omega) h24
    if hn8 : n ≤ USize.ofNat 8 then r
    else
      have h8 : 8 < n.toNat := Nat.lt_of_not_le fun e => hn8 ((usize_le_lit (by decide)).mpr e)
      blk t (p + USize.ofNat 8) (by rw [fastIdx_add (by omega)]; omega) h32 r (i + USize.ofNat 8)
        (by rw [fastIdx_add (by omega), hr]; omega) (by rw [hr]; exact h24)

theorem aff2_writes (t : ByteArray) (p n : USize) (hp : p.toNat + n.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32)
    (ring : ByteArray) (i : USize) (hi : i.toNat + n.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24)
    (hn : n.toNat ≤ 16) :
    WritesJ ring (aff2 t p n hp h32 ring i hi h24 hn) i.toNat (runBytes t p.toNat n.toNat) := by
  unfold aff2
  by_cases hn0 : n = 0
  · rw [ite_eq_left hn0]
    have : n.toNat = 0 := by rw [hn0]; rfl
    exact (WritesJ.refl ring i.toNat).of_eq (by rw [this]; simp)
  · rw [ite_eq_right hn0]
    dsimp only
    by_cases hn8 : n ≤ USize.ofNat 8
    · rw [dite_eq_left hn8]
      exact blk_writes _ _ _ _ _ _ _ _ _ ((usize_le_lit (by decide)).mp hn8)
    · rw [dite_eq_right hn8]
      have h8 : 8 < n.toNat := Nat.lt_of_not_le fun e => hn8 ((usize_le_lit (by decide)).mpr e)
      refine WritesJ.of_eq (WritesJ.trans (blk_writes _ _ _ _ _ _ _ _ 8 (Nat.le_refl _))
        (blk_writes _ _ _ _ _ _ _ _ (n.toNat - 8) (by omega)) ?_) ?_
      · rw [fastIdx_add (by omega), runBytes_length (by omega)]
      · rw [fastIdx_add (by omega), ← runBytes_add]
        congr 1
        omega

/-- A run of at most 24 bytes (a base word), by one to three blocks. -/
@[inline] def run3 (t : ByteArray) (p n : USize) (hp : p.toNat + n.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32)
    (ring : ByteArray) (i : USize) (hi : i.toNat + n.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24)
    (hn : n.toNat ≤ 24) : ByteArray :=
  if n = 0 then ring
  else
    let r := blk t p (by omega) h32 ring i (by omega) h24
    have hr : r.size = ring.size := blk_size t p (by omega) h32 ring i (by omega) h24
    if hn8 : n ≤ USize.ofNat 8 then r
    else
      have h8 : 8 < n.toNat := Nat.lt_of_not_le fun e => hn8 ((usize_le_lit (by decide)).mpr e)
      let r2 := blk t (p + USize.ofNat 8) (by rw [fastIdx_add (by omega)]; omega) h32 r (i + USize.ofNat 8)
        (by rw [fastIdx_add (by omega), hr]; omega) (by rw [hr]; exact h24)
      have hr2 : r2.size = ring.size := (blk_size _ _ _ _ _ _ _ _).trans hr
      if hn16 : n ≤ USize.ofNat 16 then r2
      else
        have h16 : 16 < n.toNat := Nat.lt_of_not_le fun e => hn16 ((usize_le_lit (by decide)).mpr e)
        blk t (p + USize.ofNat 16) (by rw [fastIdx_add (by omega)]; omega) h32 r2 (i + USize.ofNat 16)
          (by rw [fastIdx_add (by omega), hr2]; omega) (by rw [hr2]; exact h24)

theorem run3_writes (t : ByteArray) (p n : USize) (hp : p.toNat + n.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32)
    (ring : ByteArray) (i : USize) (hi : i.toNat + n.toNat + 8 ≤ ring.size) (h24 : ring.size ≤ 2 ^ 24)
    (hn : n.toNat ≤ 24) :
    WritesJ ring (run3 t p n hp h32 ring i hi h24 hn) i.toNat (runBytes t p.toNat n.toNat) := by
  unfold run3
  by_cases hn0 : n = 0
  · rw [ite_eq_left hn0]
    have : n.toNat = 0 := by rw [hn0]; rfl
    exact (WritesJ.refl ring i.toNat).of_eq (by rw [this]; simp)
  · rw [ite_eq_right hn0]
    dsimp only
    by_cases hn8 : n ≤ USize.ofNat 8
    · rw [dite_eq_left hn8]
      exact blk_writes _ _ _ _ _ _ _ _ _ ((usize_le_lit (by decide)).mp hn8)
    · rw [dite_eq_right hn8]
      have h8 : 8 < n.toNat := Nat.lt_of_not_le fun e => hn8 ((usize_le_lit (by decide)).mpr e)
      have w1 := blk_writes t p (by omega) h32 ring i (by omega) h24 8 (Nat.le_refl _)
      have w2 := WritesJ.trans w1
        (blk_writes t (p + USize.ofNat 8) (by rw [fastIdx_add (by omega)]; omega) h32
          (blk t p (by omega) h32 ring i (by omega) h24) (i + USize.ofNat 8)
          (by rw [fastIdx_add (by omega), blk_size]; omega) (by rw [blk_size]; exact h24) (min (n.toNat - 8) 8)
          (by omega))
        (by rw [fastIdx_add (by omega), runBytes_length (by omega)])
      by_cases hn16 : n ≤ USize.ofNat 16
      · rw [dite_eq_left hn16]
        have h16 := (usize_le_lit (by decide)).mp hn16
        refine w2.of_eq ?_
        rw [fastIdx_add (by omega), Nat.min_eq_left (by omega), runBytes_8 (by omega)]
      · rw [dite_eq_right hn16]
        have h16 : 16 < n.toNat := Nat.lt_of_not_le fun e => hn16 ((usize_le_lit (by decide)).mpr e)
        refine WritesJ.of_eq (WritesJ.trans w2 (blk_writes _ _ _ _ _ _ _ _ (n.toNat - 16) (by omega)) ?_) ?_
        · rw [fastIdx_add (by omega), List.length_append, runBytes_length (by omega),
            runBytes_length (by rw [fastIdx_add (by omega)]; omega)]
          omega
        · rw [fastIdx_add (by omega), fastIdx_add (by omega), Nat.min_eq_right (by omega), List.append_assoc,
            show p.toNat + 16 = p.toNat + 8 + 8 by omega, show n.toNat - 16 = n.toNat - 8 - 8 by omega,
            runBytes_8 (by omega), runBytes_8 (by omega)]

section
variable {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)

theorem elemLen_lt3 {kind amt : UInt8} {len : USize} (h : kind < 3) : elemLen kind amt len = len := by
  unfold elemLen
  rw [ite_eq_left h]

theorem elemLen_ge3 {kind amt : UInt8} {len : USize} (h : ¬ kind < 3) :
    elemLen kind amt len = len - usmin len amt.toUSize := by
  unfold elemLen
  rw [ite_eq_right h]

theorem kind_not_lt3 {kind : UInt8} (h0 : ¬ kind = 0) (h1 : ¬ kind = 1) (h2 : ¬ kind = 2) : ¬ kind < 3 := fun e => by
  have e' := UInt8.lt_iff_toNat_lt.mp e
  have a0 : kind.toNat ≠ 0 := fun x => h0 (UInt8.toNat_inj.mp (by rw [x]; rfl))
  have a1 : kind.toNat ≠ 1 := fun x => h1 (UInt8.toNat_inj.mp (by rw [x]; rfl))
  have a2 : kind.toNat ≠ 2 := fun x => h2 (UInt8.toNat_inj.mp (by rw [x]; rfl))
  rw [show (3 : UInt8).toNat = 3 from rfl] at e'
  omega

/-- The transform's elementary part on the base word, stored from window index `i` (the masked `o`): the identity and
the omissions by blocks, fermentFirst by its byte writer and then blocks, fermentAll byte by byte; 32 bytes of
`dictBytes` follow `off`, and the part and 8 bytes more fit before the window's end. -/
@[inline] def elemPutB (kind amt : UInt8) (off len : USize) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hd : off.toNat + 32 ≤ dictBytes.size) (hl : len.toNat ≤ 24) (ring : ByteArray) (o i : USize)
    (hr : ring.size = 2 ^ k) (_hio : (o &&& mask).toNat = i.toNat)
    (hw : i.toNat + (elemLen kind amt len).toNat + 8 ≤ 2 ^ k) : ByteArray :=
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hds := dictBytes_size
  have h32 : dictBytes.size < 2 ^ 32 := by omega
  if h0 : kind = 0 then
    have he : elemLen kind amt len = len := elemLen_lt3 (by rw [h0]; decide)
    run3 dictBytes off len (by omega) h32 ring i (by rw [he] at hw; omega) (by omega) hl
  else if h1 : kind = 1 then
    have he : elemLen kind amt len = len := elemLen_lt3 (by rw [h1]; decide)
    if hn : len = 0 then ring
    else
      have hnz := usize_ne hn
      have hu := fermentUsed_bounds (dictBytes.uget off (by omega)) hnz
      have hp : (off + fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          off.toNat + (fermentUsed (dictBytes.uget off (by omega)) len).toNat := by exact usize_add_small (by omega)
      have hq : (len - fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          len.toNat - (fermentUsed (dictBytes.uget off (by omega)) len).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
      have hi : (i + fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          i.toNat + (fermentUsed (dictBytes.uget off (by omega)) len).toNat := by exact usize_add_small (by omega)
      have hf := fermentPut_size hk hm dictBytes dictBytes_small off len h hnz ring o hr
      run3 dictBytes (off + fermentUsed (dictBytes.uget off (by omega)) len)
        (len - fermentUsed (dictBytes.uget off (by omega)) len) (by rw [hp, hq]; omega) h32
        (fermentPut hk hm dictBytes dictBytes_small off len h hnz ring o hr)
        (i + fermentUsed (dictBytes.uget off (by omega)) len) (by rw [hf, hi, hq]; rw [he] at hw; omega)
        (by rw [hf]; omega) (by rw [hq]; omega)
  else if h2 : kind = 2 then fermentRunPut hk hm dictBytes dictBytes_small off len h ring o hr
  else if h3 : kind = 3 then
    have he : elemLen kind amt len = len - usmin len amt.toUSize := elemLen_ge3 (by rw [h3]; decide)
    have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
    have hub : amt.toNat < 256 := amt.toNat_lt
    have hp : (off + usmin len amt.toUSize).toNat = off.toNat + min len.toNat amt.toNat := by
      rw [usize_add_small (by rw [hmin]; omega), hmin]
    have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
    run3 dictBytes (off + usmin len amt.toUSize) (len - usmin len amt.toUSize) (by rw [hp, hq]; omega) h32 ring i
      (by rw [he, hq] at hw; rw [hq]; omega) (by omega) (by rw [hq]; omega)
  else
    have he : elemLen kind amt len = len - usmin len amt.toUSize := elemLen_ge3 (kind_not_lt3 h0 h1 h2)
    have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
    have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
      rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
    run3 dictBytes off (len - usmin len amt.toUSize) (by rw [hq]; omega) h32 ring i
      (by rw [he, hq] at hw; rw [hq]; omega) (by omega) (by rw [hq]; omega)

/-- `elemPutB` stores what `elementStep` adds, with up to 8 bytes after it. -/
theorem elemPutB_writes (kind amt : UInt8) (off len : USize) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hd : off.toNat + 32 ≤ dictBytes.size) (hl : len.toNat ≤ 24) (ring : ByteArray) (o i : USize)
    (hr : ring.size = 2 ^ k) (hio : (o &&& mask).toNat = i.toNat)
    (hw : i.toNat + (elemLen kind amt len).toNat + 8 ≤ 2 ^ k) (buf : ByteArray) :
    ∃ E : List UInt8, (elementStep dictBytes dictBytes_small kind amt off len buf h).data.toList = buf.data.toList ++ E ∧
      WritesJ ring (elemPutB hk hm kind amt off len h hd hl ring o i hr hio hw) i.toNat E ∧
      E.length = (elemLen kind amt len).toNat := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hds := dictBytes_size
  have hmin : (usmin len amt.toUSize).toNat = min len.toNat amt.toNat := by rw [usmin_toNat, u8_usize]
  have hub : amt.toNat < 256 := amt.toNat_lt
  have hq : (len - usmin len amt.toUSize).toNat = len.toNat - min len.toNat amt.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hmin]; omega)), hmin]
  unfold elemPutB elementStep
  dsimp only
  by_cases h0 : kind = 0
  · subst h0
    rw [dite_eq_left rfl, ite_eq_left rfl, emitRun_data _ _ h]
    have he : elemLen 0 amt len = len := elemLen_lt3 (by decide)
    exact ⟨_, rfl, run3_writes _ _ _ _ _ _ _ _ _ _, by rw [he]; exact runBytes_length h⟩
  rw [dite_eq_right h0, ite_eq_right h0]
  by_cases h1 : kind = 1
  · subst h1
    rw [dite_eq_left rfl, ite_eq_left rfl]
    have he : elemLen 1 amt len = len := elemLen_lt3 (by decide)
    by_cases hn : len = 0
    · rw [dite_eq_left hn, dite_eq_left hn]
      exact ⟨[], by rw [List.append_nil], WritesJ.refl _ _, by rw [he, hn]; rfl⟩
    · rw [dite_eq_right hn, dite_eq_right hn]
      have hnz := usize_ne hn
      obtain ⟨L1, e1, p1, l1⟩ := fermentPut_mirror hk hm dictBytes dictBytes_small off len h hnz buf ring o hr
      have hu := fermentUsed_bounds (dictBytes.uget off (by omega)) hnz
      have hp : (off + fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          off.toNat + (fermentUsed (dictBytes.uget off (by omega)) len).toNat := usize_add_small (by omega)
      have hq' : (len - fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          len.toNat - (fermentUsed (dictBytes.uget off (by omega)) len).toNat :=
        USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hu.2)
      have hi : (i + fermentUsed (dictBytes.uget off (by omega)) len).toNat =
          i.toNat + (fermentUsed (dictBytes.uget off (by omega)) len).toNat := usize_add_small (by omega)
      rw [he] at hw
      have w1 : WritesJ ring (fermentPut hk hm dictBytes dictBytes_small off len h hnz ring o hr) i.toNat L1 := by
        rw [p1, ← hio]
        exact putList_writes hk hm _ _ _ _ (by rw [hio, l1]; omega)
      refine ⟨L1 ++ runBytes dictBytes (off + fermentUsed (dictBytes.uget off (by omega)) len).toNat
        (len - fermentUsed (dictBytes.uget off (by omega)) len).toNat, ?_, ?_, ?_⟩
      · rw [emitRun_data _ _ (by rw [hp, hq']; omega), e1, List.append_assoc]
      · exact w1.trans (run3_writes _ _ _ _ _ _ _ _ _ _) (by rw [hi, l1])
      · rw [List.length_append, runBytes_length (by rw [hp, hq']; omega), l1, hq', he]
        omega
  rw [dite_eq_right h1, ite_eq_right h1]
  by_cases h2 : kind = 2
  · subst h2
    rw [dite_eq_left rfl, ite_eq_left rfl]
    have he : elemLen 2 amt len = len := elemLen_lt3 (by decide)
    obtain ⟨L, e, p, l⟩ := fermentRunPut_mirror hk hm dictBytes dictBytes_small _ off len h rfl buf ring o hr
    refine ⟨L, e, ?_, by rw [l, he]⟩
    rw [p, ← hio]
    exact putList_writes hk hm _ _ _ _ (by rw [hio, l]; rw [he] at hw; omega)
  rw [dite_eq_right h2, ite_eq_right h2]
  have he : elemLen kind amt len = len - usmin len amt.toUSize := elemLen_ge3 (kind_not_lt3 h0 h1 h2)
  by_cases h3 : kind = 3
  · subst h3
    rw [dite_eq_left rfl, ite_eq_left rfl]
    have hp : (off + usmin len amt.toUSize).toNat = off.toNat + min len.toNat amt.toNat := by
      rw [usize_add_small (by rw [hmin]; omega), hmin]
    rw [emitRun_data _ _ (by rw [hp, hq]; omega)]
    exact ⟨_, rfl, run3_writes _ _ _ _ _ _ _ _ _ _, by rw [he]; exact runBytes_length (by rw [hp, hq]; omega)⟩
  · rw [dite_eq_right h3, ite_eq_right h3]
    rw [emitRun_data _ _ (by rw [hq]; omega)]
    exact ⟨_, rfl, run3_writes _ _ _ _ _ _ _ _ _ _, by rw [he]; exact runBytes_length (by rw [hq]; omega)⟩

theorem elemPutB_size (kind amt : UInt8) (off len : USize) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hd : off.toNat + 32 ≤ dictBytes.size) (hl : len.toNat ≤ 24) (ring : ByteArray) (o i : USize)
    (hr : ring.size = 2 ^ k) (hio : (o &&& mask).toNat = i.toNat)
    (hw : i.toNat + (elemLen kind amt len).toNat + 8 ≤ 2 ^ k) :
    (elemPutB hk hm kind amt off len h hd hl ring o i hr hio hw).size = 2 ^ k := by
  obtain ⟨_, _, w, _⟩ := elemPutB_writes hk hm kind amt off len h hd hl ring o i hr hio hw ByteArray.empty
  exact w.1.trans hr

theorem wordLenF_toNat (kind amt pl sl : UInt8) {len : USize} (hl : len.toNat ≤ 24) :
    (wordLenF kind amt pl sl len).toNat = pl.toNat + (elemLen kind amt len).toNat + sl.toNat := by
  have hel := elemLen_le kind amt len
  have hp := u8_usize pl
  have hs := u8_usize sl
  have a := pl.toNat_lt
  have b := sl.toNat_lt
  unfold wordLenF
  rw [usize_add_small (by rw [usize_add_small (by rw [hp]; omega), hp, hs]; omega), usize_add_small (by rw [hp]; omega),
    hp, hs]

/-- The word from its transform's fields, stored by blocks from window index `o &&& mask`: the prefix, the elementary
part on the base word, the suffix, each from the exact end of the one before; 32 bytes of `transLut` follow the row's
base and of `dictBytes` the base word's offset, and the word and 8 bytes more fit before the window's end. -/
@[inline] def wordPutFB3 (base off len : USize) (kind amt pl sl : UInt8) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hb : base.toNat + 32 ≤ transLut.size) (ha : pl.toNat + sl.toNat ≤ 13) (hl : len.toNat ≤ 24)
    (hd : off.toNat + 32 ≤ dictBytes.size) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k)
    (hw : (o &&& mask).toNat + (wordLenF kind amt pl sl len).toNat + 8 ≤ 2 ^ k) : ByteArray :=
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hts := transLut_size
  have h32 : transLut.size < 2 ^ 32 := by omega
  have hpl : pl.toUSize.toNat = pl.toNat := by exact u8_usize pl
  have hsl : sl.toUSize.toNat = sl.toNat := by exact u8_usize sl
  have hwl := wordLenF_toNat kind amt pl sl hl
  have hel := elemLen_le kind amt len
  have hlt := mask_lt (i := o) hm
  have h4 : (base + USize.ofNat 4).toNat = base.toNat + 4 := fastIdx_add (by omega)
  have hi1 : ((o &&& mask) + pl.toUSize).toNat = (o &&& mask).toNat + pl.toNat := by
    rw [fastAdd (by rw [hpl]; omega), hpl]
  have hi2 : ((o &&& mask) + pl.toUSize + elemLen kind amt len).toNat =
      (o &&& mask).toNat + pl.toNat + (elemLen kind amt len).toNat := by
    rw [fastAdd (by rw [hi1]; omega), hi1]
  have h4p : (base + USize.ofNat 4 + pl.toUSize).toNat = base.toNat + 4 + pl.toNat := by
    rw [fastAdd (by rw [h4, hpl]; omega), h4, hpl]
  let r0 := aff2 transLut (base + USize.ofNat 4) pl.toUSize (by rw [h4, hpl]; omega) h32 ring (o &&& mask)
    (by rw [hpl, hr]; omega) (by omega) (by rw [hpl]; omega)
  have hr0 : r0.size = 2 ^ k := (aff2_writes _ _ _ _ _ _ _ _ _ _).1.trans hr
  let r1 := elemPutB hk hm kind amt off len h hd hl r0 (o + pl.toUSize) ((o &&& mask) + pl.toUSize) hr0
    (by rw [add_mask_toNat hk hm, hpl, hi1, Nat.mod_eq_of_lt (by omega)]) (by rw [hi1]; omega)
  have hr1 : r1.size = 2 ^ k := elemPutB_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  aff2 transLut (base + USize.ofNat 4 + pl.toUSize) sl.toUSize (by rw [h4p, hsl]; omega) h32 r1
    ((o &&& mask) + pl.toUSize + elemLen kind amt len) (by rw [hi2, hsl, hr1]; omega) (by omega)
    (by rw [hsl]; omega)

/-- `wordPutFB3` stores the word `buildWord` builds from the same fields, with up to 8 bytes after it. -/
theorem wordPutFB3_writes (base off len : USize) (kind amt pl sl : UInt8) (h : off.toNat + len.toNat ≤ dictBytes.size)
    (hb : base.toNat + 32 ≤ transLut.size) (ha : pl.toNat + sl.toNat ≤ 13) (hl : len.toNat ≤ 24)
    (hd : off.toNat + 32 ≤ dictBytes.size) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k)
    (hw : (o &&& mask).toNat + (wordLenF kind amt pl sl len).toNat + 8 ≤ 2 ^ k) :
    WritesJ ring (wordPutFB3 hk hm base off len kind amt pl sl h hb ha hl hd ring o hr hw) (o &&& mask).toNat
      (emitRun transLut (elementStep dictBytes dictBytes_small kind amt off len
        (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat) h)
        (base + USize.ofNat 4 + pl.toUSize).toNat sl.toNat).data.toList := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hts := transLut_size
  have hpl : pl.toUSize.toNat = pl.toNat := u8_usize pl
  have hsl : sl.toUSize.toNat = sl.toNat := u8_usize sl
  have hwl := wordLenF_toNat kind amt pl sl hl
  have hel := elemLen_le kind amt len
  have hlt := mask_lt (i := o) hm
  have h4 : (base + USize.ofNat 4).toNat = base.toNat + 4 := fastIdx_add (by omega)
  have hi1 : ((o &&& mask) + pl.toUSize).toNat = (o &&& mask).toNat + pl.toNat := by
    rw [fastAdd (by rw [hpl]; omega), hpl]
  have hi2 : ((o &&& mask) + pl.toUSize + elemLen kind amt len).toNat =
      (o &&& mask).toNat + pl.toNat + (elemLen kind amt len).toNat := by
    rw [fastAdd (by rw [hi1]; omega), hi1]
  have h4p : (base + USize.ofNat 4 + pl.toUSize).toNat = base.toNat + 4 + pl.toNat := by
    rw [fastAdd (by rw [h4, hpl]; omega), h4, hpl]
  unfold wordPutFB3
  dsimp only
  have wP := aff2_writes transLut (base + USize.ofNat 4) pl.toUSize (by rw [h4, hpl]; omega) (by omega) ring
    (o &&& mask) (by rw [hpl, hr]; omega) (by omega) (by rw [hpl]; omega)
  obtain ⟨E, eE, wE, lE⟩ := elemPutB_writes hk hm kind amt off len h hd hl _ (o + pl.toUSize)
    ((o &&& mask) + pl.toUSize) (wP.1.trans hr)
    (by rw [add_mask_toNat hk hm, hpl, hi1, Nat.mod_eq_of_lt (by omega)]) (by rw [hi1]; omega)
    (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat)
  have hP : (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat).data.toList =
      runBytes transLut (base + USize.ofNat 4).toNat pl.toUSize.toNat := by
    rw [emitRun_data _ _ (by rw [h4]; omega), hpl]
    rfl
  rw [emitRun_data _ _ (by rw [h4p]; omega), eE, hP]
  refine WritesJ.trans (j := ((o &&& mask) + pl.toUSize + elemLen kind amt len).toNat) (wP.trans wE ?_) ?_ ?_
  · rw [hi1, runBytes_length (by rw [h4, hpl]; omega), hpl]
  · exact (aff2_writes _ _ _ _ _ _ _ _ _ _).of_eq (by rw [hsl])
  · rw [hi2, List.length_append, runBytes_length (by rw [h4, hpl]; omega), hpl, lE, Nat.add_assoc]

include hk hm in
/-- The window part of `wordPutW`'s guard. -/
theorem guard_win {o wl : USize} {ring : ByteArray} (hr : ring.size = 2 ^ k) (hwl : wl.toNat ≤ 64)
    (hg : (o &&& mask) + wl + USize.ofNat 8 ≤ ring.usize) : (o &&& mask).toNat + wl.toNat + 8 ≤ 2 ^ k := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hlt := mask_lt (i := o) hm
  have hu : ring.usize.toNat = ring.size := by
    show (USize.ofNat ring.size).toNat = _
    exact fastLit (by omega)
  have e := USize.le_iff_toNat_le.mp hg
  rw [fastIdx_add (by rw [fastAdd (by omega)]; omega), fastAdd (by omega), hu, hr] at e
  exact e

/-- The dictionary part of `wordPutW`'s guard. -/
theorem guard_dict {off : USize} (ho : off.toNat < 2 ^ 24) (hg : off + USize.ofNat 32 ≤ USize.ofNat 122784) :
    off.toNat + 32 ≤ dictBytes.size := by
  have e := USize.le_iff_toNat_le.mp hg
  rw [fastIdx_add (by omega), fastLit (by decide)] at e
  rw [dictBytes_size]
  exact e

/-- The word's write, one call a word: by blocks (`wordPutFB3`) where the word and 8 bytes more fit before the window's
end and 32 bytes of `dictBytes` follow the base word's offset, otherwise byte by byte (`wordPutF`). -/
@[noinline] def wordPutW (base off len : USize) (kind amt pl sl : UInt8)
    (hB : (base + USize.ofNat 4).toNat + pl.toNat + sl.toNat ≤ transLut.size)
    (h : off.toNat + len.toNat ≤ dictBytes.size) (hb : base.toNat + 32 ≤ transLut.size)
    (ha : pl.toNat + sl.toNat ≤ 13) (hl : len.toNat ≤ 24) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    ByteArray :=
  if hg : (o &&& mask) + wordLenF kind amt pl sl len + USize.ofNat 8 ≤ ring.usize ∧
      off + USize.ofNat 32 ≤ USize.ofNat 122784 then
    wordPutFB3 hk hm base off len kind amt pl sl h hb ha hl
      (guard_dict (by have := dictBytes_size; omega) hg.2) ring o hr
      (guard_win hk hm hr (by have := elemLen_le kind amt len; rw [wordLenF_toNat kind amt pl sl hl]; omega) hg.1)
  else wordPutF hk hm base off len kind amt pl sl hB h dictBytes_small ring o hr

/-- What `wordPutW` leaves: a window of the same size holding the word `buildWord` builds from the same fields, from
`o &&& mask` on, as `putList` stores it, but where the blocks ran, perhaps for the 8 bytes after the word, which then lie
before the window's end. -/
theorem wordPutW_spec (base off len : USize) (kind amt pl sl : UInt8)
    (hB : (base + USize.ofNat 4).toNat + pl.toNat + sl.toNat ≤ transLut.size)
    (h : off.toNat + len.toNat ≤ dictBytes.size) (hb : base.toNat + 32 ≤ transLut.size)
    (ha : pl.toNat + sl.toNat ≤ 13) (hl : len.toNat ≤ 24) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k) :
    let w := emitRun transLut (elementStep dictBytes dictBytes_small kind amt off len
      (emitRun transLut (freshBytes 38) (base + USize.ofNat 4).toNat pl.toNat) h)
      (base + USize.ofNat 4 + pl.toUSize).toNat sl.toNat
    (wordPutW hk hm base off len kind amt pl sl hB h hb ha hl ring o hr).size = 2 ^ k ∧
      ∀ q, ¬ ((o &&& mask).toNat + w.size ≤ q ∧ q < (o &&& mask).toNat + w.size + 8 ∧
          (o &&& mask).toNat + w.size + 8 ≤ 2 ^ k) →
        (wordPutW hk hm base off len kind amt pl sl hB h hb ha hl ring o hr).data[q]? =
          (putList hk hm ring o hr w.data.toList).data[q]? := by
  intro w
  have hF := wordPutF_eq hk hm base off len kind amt pl sl hB h dictBytes_small ring o hr
  have hel := elemLen_le kind amt len
  have hwl := wordLenF_toNat kind amt pl sl hl
  have hlen : w.data.toList.length = w.size := Array.length_toList
  unfold wordPutW
  by_cases hg : (o &&& mask) + wordLenF kind amt pl sl len + USize.ofNat 8 ≤ ring.usize ∧
      off + USize.ofNat 32 ≤ USize.ofNat 122784
  · rw [dite_eq_left hg]
    have hd := guard_dict (by have := dictBytes_size; omega) hg.2
    have hw := guard_win hk hm hr (by rw [hwl]; omega) hg.1
    have hwr := wordPutFB3_writes hk hm base off len kind amt pl sl h hb ha hl hd ring o hr hw
    have hfit : (o &&& mask).toNat + w.size + 8 ≤ 2 ^ k := by rw [← hF.2]; exact hw
    have hwr' : WritesJ ring (wordPutFB3 hk hm base off len kind amt pl sl h hb ha hl hd ring o hr hw)
        (o &&& mask).toNat w.data.toList := hwr
    refine ⟨hwr.1.trans hr, fun q hq => ?_⟩
    rw [putList_get hk hm _ _ _ _ (by rw [hlen]; omega)]
    replace hwr := hwr'
    by_cases hin : (o &&& mask).toNat ≤ q ∧ q < (o &&& mask).toNat + w.data.toList.length
    · rw [ite_eq_left hin]
      exact (hwr.2 q).1 hin.1 hin.2
    · rw [ite_eq_right hin]
      exact (hwr.2 q).2 (by omega)
  · rw [dite_eq_right hg, hF.1]
    exact ⟨putList_size hk hm _ _ _ _, fun _ _ => rfl⟩

end

/-- The length of a dictionary reference's word, without building it; 0 for a reference that isn't valid. -/
@[inline] def dictLen (clen wordId : UInt64) : USize :=
  if h : dictValid clen wordId then
    wordLenB (dictTid (lenRow clen (lt25 h.1)) wordId).toUSize clen.toUSize
      (by
        have hl := lt25 h.1
        have hp := dict_parts (wordId := wordId) (ge4 h.1) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
        have ht := lt121 h.2
        rw [word_toUSize (by omega)]
        exact ht)
  else 0

/-- A transform's row: its prefix and suffix lie inside `transLut`. -/
theorem row_bound {id : USize} (hid : id.toNat < 121) :
    (id * USize.ofNat 32 + USize.ofNat 4).toNat +
        (transLut.uget (id * USize.ofNat 32 + USize.ofNat 2) (row_lt hid (by decide))).toNat +
        (transLut.uget (id * USize.ofNat 32 + USize.ofNat 3) (row_lt hid (by decide))).toNat ≤ transLut.size := by
  have := affix_uget hid (row_lt hid (by decide)) (row_lt hid (by decide))
  have := transLut_size
  rw [(row_at hid (j := 4) (by decide)).1]
  omega

/-- A transform's prefix and suffix are 13 bytes at most together. -/
theorem row_affix {id : USize} (hid : id.toNat < 121) :
    (transLut.uget (id * USize.ofNat 32 + USize.ofNat 2) (row_lt hid (by decide))).toNat +
      (transLut.uget (id * USize.ofNat 32 + USize.ofNat 3) (row_lt hid (by decide))).toNat ≤ 13 :=
  affix_uget hid _ _

/-- 32 bytes of `transLut` follow a transform's row's start. -/
theorem row_end {id : USize} (hid : id.toNat < 121) : (id * USize.ofNat 32).toNat + 32 ≤ transLut.size := by
  have := base_toNat hid
  have := transLut_size
  omega

/-- `dictLen` is the length of `dictBuild`'s word. -/
theorem dictLen_eq {clen wordId : UInt64} (h : dictValid clen wordId) :
    (dictLen clen wordId).toNat = (dictBuild clen wordId h).size := by
  have hl := lt25 h.1
  have hp := dict_parts (wordId := wordId) (ge4 h.1) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
  have hid : (dictTid (lenRow clen hl) wordId).toUSize.toNat < 121 := by
    have ht := lt121 h.2
    rw [word_toUSize (by omega)]
    exact ht
  unfold dictLen dictBuild
  rw [dite_eq_left h]
  unfold wordLenB buildWord
  exact (wordPutF_eq (mask := 0) (k := 0) (by decide) rfl _ _ _ _ _ _ _ (row_bound hid) _ _ (ByteArray.mk #[0]) 0
    rfl).2

/-- A reference with a word of some length is valid. -/
theorem dictLen_valid {clen wordId : UInt64} (h : dictLen clen wordId ≠ 0) : dictValid clen wordId := by
  unfold dictLen at h
  by_cases hv : dictValid clen wordId
  · exact hv
  · rw [dite_eq_right hv] at h
    exact absurd rfl h

section
variable {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)

/-- The word of a valid dictionary reference written into the window from `o` on (`wordPutW`): `dictBuild`'s word, as
`putList` stores it, perhaps with other bytes in the 8 after it (`dictPutW_spec`). -/
def dictPutW (clen wordId : UInt64) (h : dictValid clen wordId) (ring : ByteArray) (o : USize)
    (hr : ring.size = 2 ^ k) : ByteArray :=
  have hl := lt25 h.1
  have hp := dict_parts (wordId := wordId) (ge4 h.1) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
  have hid : (dictTid (lenRow clen hl) wordId).toUSize.toNat < 121 := by
    have ht := lt121 h.2
    rw [word_toUSize (by omega)]
    exact ht
  wordPutW hk hm ((dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32)
    (dictOff (lenRow clen hl) clen wordId).toUSize clen.toUSize
    (transLut.uget ((dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32) (base_lt hid))
    (transLut.uget ((dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32 + USize.ofNat 1) (row_lt hid (by decide)))
    (transLut.uget ((dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32 + USize.ofNat 2) (row_lt hid (by decide)))
    (transLut.uget ((dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32 + USize.ofNat 3) (row_lt hid (by decide)))
    (row_bound hid)
    (by
      rw [word_toUSize (by omega), clen_usize hl, dictBytes_size]
      exact hp.2.2)
    (row_end hid) (row_affix hid) (by rw [clen_usize hl]; exact h.1.2 |> UInt64.le_iff_toNat_le.mp) ring o hr

set_option maxRecDepth 20000 in
/-- What `dictPutW` leaves: a window of the same size holding `dictBuild`'s word from `o &&& mask` on, as `putList`
stores it, but perhaps for the 8 bytes after the word where those lie before the window's end. These are within the 16
bytes after the write position that the window's relation leaves free (`RingOk`). -/
theorem dictPutW_spec {clen wordId : UInt64} (h : dictValid clen wordId) (ring : ByteArray) (o : USize)
    (hr : ring.size = 2 ^ k) :
    (dictPutW hk hm clen wordId h ring o hr).size = 2 ^ k ∧
      ∀ q, ¬ ((o &&& mask).toNat + (dictBuild clen wordId h).size ≤ q ∧
          q < (o &&& mask).toNat + (dictBuild clen wordId h).size + 8 ∧
          (o &&& mask).toNat + (dictBuild clen wordId h).size + 8 ≤ 2 ^ k) →
        (dictPutW hk hm clen wordId h ring o hr).data[q]? =
          (putList hk hm ring o hr (dictBuild clen wordId h).data.toList).data[q]? := by
  unfold dictPutW dictBuild buildWord
  exact wordPutW_spec hk hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- A dictionary reference looked up once, for the fast loop: when it is valid, `some` gets the word's length and the
write of the word into the window from `o` on (`dictWith_eq`: `dictLen` and `dictPutW`), from one reading of the length
row and the transform's row; otherwise `none`. -/
@[inline] def dictWith {α : Type} (clen wordId : UInt64) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k)
    (none : Unit → α) (some : USize → (Unit → { r : ByteArray // r.size = 2 ^ k }) → α) : α :=
  if h : dictValid clen wordId then
    have hl := lt25 h.1
    have hp := dict_parts (wordId := wordId) (ge4 h.1) (by omega) (lenRow_fields hl).1 (lenRow_fields hl).2
    have hid : (dictTid (lenRow clen hl) wordId).toUSize.toNat < 121 := by
      have ht := lt121 h.2
      rw [word_toUSize (by omega)]
      exact ht
    let base := (dictTid (lenRow clen hl) wordId).toUSize * USize.ofNat 32
    let kind := transLut.uget base (base_lt hid)
    let amt := transLut.uget (base + USize.ofNat 1) (row_lt hid (by decide))
    let pl := transLut.uget (base + USize.ofNat 2) (row_lt hid (by decide))
    let sl := transLut.uget (base + USize.ofNat 3) (row_lt hid (by decide))
    some (wordLenF kind amt pl sl clen.toUSize)
      (fun _ => ⟨wordPutW hk hm base (dictOff (lenRow clen hl) clen wordId).toUSize clen.toUSize kind amt pl sl
          (row_bound hid)
          (by
            rw [word_toUSize (by omega), clen_usize hl, dictBytes_size]
            exact hp.2.2)
          (row_end hid) (row_affix hid) (by rw [clen_usize hl]; exact h.1.2 |> UInt64.le_iff_toNat_le.mp) ring o hr,
        (dictPutW_spec hk hm h ring o hr).1⟩)
  else none ()

/-- `dictWith` gives `dictLen` and `dictPutW`. -/
theorem dictWith_eq {α : Type} (clen wordId : UInt64) (ring : ByteArray) (o : USize) (hr : ring.size = 2 ^ k)
    (none : Unit → α) (some : USize → (Unit → { r : ByteArray // r.size = 2 ^ k }) → α) :
    dictWith hk hm clen wordId ring o hr none some =
      if h : dictValid clen wordId then
        some (dictLen clen wordId) (fun _ => ⟨dictPutW hk hm clen wordId h ring o hr, (dictPutW_spec hk hm h ring o hr).1⟩)
      else none () := by
  unfold dictWith
  by_cases h : dictValid clen wordId
  · rw [dite_eq_left h, dite_eq_left h]
    unfold dictLen
    rw [dite_eq_left h]
    rfl
  · rw [dite_eq_right h, dite_eq_right h]

theorem dictWith_congr {α : Type} {clen wordId : UInt64} {ring : ByteArray} {o : USize} {hr : ring.size = 2 ^ k}
    {n1 n2 : Unit → α} {s1 s2 : USize → (Unit → { r : ByteArray // r.size = 2 ^ k }) → α} (hn : n1 () = n2 ())
    (hs : ∀ wl put, s1 wl put = s2 wl put) :
    dictWith hk hm clen wordId ring o hr n1 s1 = dictWith hk hm clen wordId ring o hr n2 s2 := by
  rw [dictWith_eq, dictWith_eq]
  by_cases h : dictValid clen wordId
  · rw [dite_eq_left h, dite_eq_left h]
    exact hs _ _
  · rw [dite_eq_right h, dite_eq_right h]
    exact hn

theorem dictWith_const {α : Type} {clen wordId : UInt64} {ring : ByteArray} {o : USize} {hr : ring.size = 2 ^ k}
    {n : Unit → α} {s : USize → (Unit → { r : ByteArray // r.size = 2 ^ k }) → α} {v : α} (hn : n () = v)
    (hs : ∀ wl put, s wl put = v) : dictWith hk hm clen wordId ring o hr n s = v := by
  rw [dictWith_eq]
  by_cases h : dictValid clen wordId
  · rw [dite_eq_left h]
    exact hs _ _
  · rw [dite_eq_right h]
    exact hn

end

end Brotli.Decoder
