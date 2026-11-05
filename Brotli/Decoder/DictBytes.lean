module

public import Brotli.Decoder.Copy
public import Brotli.Decoder.CmdLut

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

instance (clen wordId : UInt64) : Decidable (dictValid clen wordId) :=
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

end Brotli.Decoder
