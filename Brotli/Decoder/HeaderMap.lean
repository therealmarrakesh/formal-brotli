module

public import Brotli.Decoder.HeaderSyms

@[expose] public section

/-!
# A context map's values

The place reading a context map's values, and the place at its last bit, with the inverse move-to-front transform and the
check that every tree occurs.
-/

namespace Brotli.Decoder

open Brotli.Spec

section
variable {α : Type} (K : HK α)

/-- With no values left, the last bit is next. -/
theorem hrest_vals_zero (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (bs : List Bool) :
    hrest K g (.vals isL ntrees rlemax code done 0) bs = hrest K g (.imtf isL ntrees done) bs := by
  show (valsFrom rlemax code 0 bs >>= _) = _
  rw [valsFrom_zero]
  show afterVals K g isL ntrees (done ++ []) bs = _
  rw [List.append_nil]
  rfl

/-- With a code that gives a value without reading, every value left is that one. -/
theorem hrest_vals_run (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (left : Nat) {v : Nat}
    (hr : runOf rlemax code = some v) (bs : List Bool) :
    hrest K g (.vals isL ntrees rlemax code done left) bs = hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate left v) 0) bs := by
  show (valsFrom rlemax code left bs >>= _) = (valsFrom rlemax code 0 bs >>= _)
  rw [valsFrom_run hr, valsFrom_zero]
  show afterVals K g isL ntrees (done ++ List.replicate left v) bs = afterVals K g isL ntrees ((done ++ List.replicate left v) ++ []) bs
  rw [List.append_nil]

/-- One more symbol of the values. -/
theorem hrest_vals_step (g : Gh) (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (left : Nat) (bs : List Bool)
    (h0 : left ≠ 0) : hrest K g (.vals isL ntrees rlemax code done left) bs = mapSym rlemax code bs >>= fun p =>
      if left < p.1.2 then none
      else hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate p.1.2 p.1.1) (left - p.1.2)) p.2 := by
  show (valsFrom rlemax code left bs >>= _) = _
  rw [valsFrom_step bs h0]
  cases mapSym rlemax code bs with
  | none => rfl
  | some p =>
    show ((if left < p.1.2 then none else (valsFrom rlemax code (left - p.1.2) p.2 >>= fun q => some (List.replicate p.1.2 p.1.1 ++ q.1, q.2))) >>= _) =
      (if left < p.1.2 then none else valsFrom rlemax code (left - p.1.2) p.2 >>= _)
    by_cases h1 : left < p.1.2
    · rw [ite_eq_left h1, ite_eq_left h1]
      rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      cases valsFrom rlemax code (left - p.1.2) p.2 with
      | none => rfl
      | some q =>
        show afterVals K g isL ntrees (done ++ (List.replicate p.1.2 p.1.1 ++ q.1)) q.2 =
          afterVals K g isL ntrees (done ++ List.replicate p.1.2 p.1.1 ++ q.1) q.2
        rw [List.append_assoc]

end

theorem mapSym_bounds {rlemax ntrees : Nat} {code : PrefixCode} {bs r : List Bool} {v run : Nat}
    (hn : 0 < ntrees) (hr : rlemax ≤ 16) (hs : code.Symbols (contextMapAlphabetSize ntrees rlemax))
    (h : mapSym rlemax code bs = some ((v, run), r)) : v < ntrees ∧ 1 ≤ run ∧ (v ≠ 0 → run = 1) ∧ run < 2 ^ 18 := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, b1⟩ := p
    rw [hd] at h
    have hlt : sym < ntrees + rlemax := decodeSymbol_lt hs hd
    change (match contextMapValue rlemax sym with
      | some v => some ((v, 1), b1)
      | none => readInt sym b1 >>= fun q => some ((0, (1 <<< sym) + q.1), q.2)) = _ at h
    cases hv : contextMapValue rlemax sym with
    | some x =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, _⟩ := h
      refine ⟨?_, by omega, fun _ => rfl, by decide⟩
      unfold contextMapValue at hv
      split at hv
      · simp only [Option.some.injEq] at hv
        omega
      · split at hv
        · cases hv
        · simp only [Option.some.injEq] at hv
          omega
    | none =>
      rw [hv] at h
      cases hx : readInt sym b1 with
      | none => rw [hx] at h; cases h
      | some q =>
        obtain ⟨e, b2⟩ := q
        rw [hx] at h
        have h' : some ((0, (1 <<< sym) + e), b2) = some ((v, run), r) := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨⟨rfl, rfl⟩, _⟩ := h'
        have hsym : sym ≤ 16 := by
          unfold contextMapValue at hv
          split at hv
          · cases hv
          · split at hv
            · omega
            · cases hv
        have he := readInt_lt _ _ _ _ hx
        have hp : 2 ^ sym ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) hsym
        have h216 : (2 : Nat) ^ 16 = 65536 := rfl
        have hpos : 0 < 2 ^ sym := Nat.two_pow_pos _
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        refine ⟨hn, by omega, fun e => absurd rfl e, by have : (2 : Nat) ^ 18 = 262144 := rfl; omega⟩

/-! ### The inverse move-to-front transform -/

theorem imtf_append : ∀ (L vs ws : List Nat),
    inverseMoveToFrontFrom L (vs ++ ws) = inverseMoveToFrontFrom L vs ++ inverseMoveToFrontFrom (mtfAfter L vs) ws
  | _, [], _ => rfl
  | L, idx :: v, ws => by
    show L.getD idx 0 :: inverseMoveToFrontFrom (L.getD idx 0 :: L.eraseIdx idx) (v ++ ws) =
      (L.getD idx 0 :: inverseMoveToFrontFrom (L.getD idx 0 :: L.eraseIdx idx) v) ++ _
    rw [imtf_append]
    rfl

theorem mtfAfter_append : ∀ (L vs ws : List Nat), mtfAfter L (vs ++ ws) = mtfAfter (mtfAfter L vs) ws
  | _, [], _ => rfl
  | _, _ :: v, ws => mtfAfter_append _ v ws

/-- The same index again and again turns the list's first places round, one place each time. -/
theorem mtfAfter_rot (L : List Nat) (s : Nat) (hs : s < L.length) : ∀ k, k ≤ s + 1 →
    mtfAfter L (List.replicate k s) = (L.take (s + 1)).drop (s + 1 - k) ++ (L.take (s + 1)).take (s + 1 - k) ++ L.drop (s + 1)
  | 0, _ => by
    simp only [List.replicate_zero, mtfAfter, Nat.sub_zero]
    rw [List.drop_eq_nil_of_le (by rw [List.length_take]; omega), List.take_take, Nat.min_self, List.nil_append, List.take_append_drop]
  | k + 1, hk => by
    rw [List.replicate_succ', mtfAfter_append, mtfAfter_rot L s hs k (by omega)]
    have hP : (L.take (s + 1)).length = s + 1 := by rw [List.length_take]; omega
    generalize L.take (s + 1) = P at hP ⊢
    generalize L.drop (s + 1) = C
    have hA : (P.drop (s + 1 - k)).length = k := by rw [List.length_drop]; omega
    have hB : (P.take (s + 1 - k)).length = s + 1 - k := by rw [List.length_take]; omega
    show (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 :: (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).eraseIdx s = _
    have hg : (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 = P.getD (s - k) 0 := by
      rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by rw [hA]; omega), hA,
        List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show s - k < s + 1 - k by omega),
        ← List.getD_eq_getElem?_getD]
    have e1 : (P.take (s + 1 - k)).eraseIdx (s - k) = P.take (s - k) := by
      rw [List.eraseIdx_eq_take_drop_succ, List.take_take, List.drop_eq_nil_of_le (by rw [hB]; omega), List.append_nil,
        Nat.min_eq_left (by omega)]
    have he : (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).eraseIdx s = P.drop (s + 1 - k) ++ P.take (s - k) ++ C := by
      rw [List.append_assoc, List.eraseIdx_append_of_length_le (by rw [hA]; omega), hA,
        List.eraseIdx_append_of_lt_length (by rw [hB]; omega), e1, ← List.append_assoc]
    rw [hg, he, show s + 1 - (k + 1) = s - k by omega, List.drop_eq_getElem_cons (show s - k < P.length by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show s - k < P.length by omega), Option.getD_some,
      show s + 1 - k = s - k + 1 by omega]
    rfl

/-- The same index as many times as the places it turns round leaves the list as it was. -/
theorem mtfAfter_period (L : List Nat) (s : Nat) (hs : s < L.length) : mtfAfter L (List.replicate (s + 1) s) = L := by
  rw [mtfAfter_rot L s hs (s + 1) (Nat.le_refl _), Nat.sub_self, List.drop_zero, List.take_zero, List.append_nil, List.take_append_drop]

/-! ### Runs of the same index -/

/-- After the same index again and again, the list depends only on how many times it came, modulo the places it turns
round. -/
theorem mtfAfter_mod (L : List Nat) (s : Nat) (hs : s < L.length) :
    ∀ k, mtfAfter L (List.replicate k s) = mtfAfter L (List.replicate (k % (s + 1)) s) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hk : k < s + 1
    · rw [Nat.mod_eq_of_lt hk]
    · have e : List.replicate k s = List.replicate (s + 1) s ++ List.replicate (k - (s + 1)) s := by
        rw [List.replicate_append_replicate]
        congr 1
        omega
      rw [e, mtfAfter_append, mtfAfter_period L s hs, ih (k - (s + 1)) (by omega)]
      congr 2
      exact (Nat.mod_eq_sub_mod (by omega)).symm

theorem imtf_prefix (L vs ws : List Nat) {j : Nat} (hj : j < vs.length) :
    (inverseMoveToFrontFrom L (vs ++ ws))[j]? = (inverseMoveToFrontFrom L vs)[j]? := by
  rw [imtf_append, List.getElem?_append_left (by rw [inverseMoveToFrontFrom_length]; exact hj)]

theorem imtf_periodic (L : List Nat) (s : Nat) (hs : s < L.length) {k j : Nat} (hj : j + (s + 1) < k) :
    (inverseMoveToFrontFrom L (List.replicate k s))[j + (s + 1)]? = (inverseMoveToFrontFrom L (List.replicate k s))[j]? := by
  have e1 : List.replicate k s = List.replicate (s + 1) s ++ List.replicate (k - (s + 1)) s := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  have e2 : List.replicate k s = List.replicate (k - (s + 1)) s ++ List.replicate (s + 1) s := by
    rw [List.replicate_append_replicate]
    congr 1
    omega
  conv => lhs; rw [e1, imtf_append, mtfAfter_period L s hs]
  rw [List.getElem?_append_right (by rw [inverseMoveToFrontFrom_length, List.length_replicate]; omega),
    inverseMoveToFrontFrom_length, List.length_replicate, Nat.add_sub_cancel, e2, imtf_prefix _ _ _ (by rw [List.length_replicate]; omega)]

/-- The value at the turning point of a list whose first `s + 1` places are turned round `k` places. -/
theorem rot_getD (P C : List Nat) {s k : Nat} (hP : P.length = s + 1) (hk : k ≤ s) :
    (P.drop (s + 1 - k) ++ P.take (s + 1 - k) ++ C).getD s 0 = P.getD (s - k) 0 := by
  have hA : (P.drop (s + 1 - k)).length = k := by rw [List.length_drop]; omega
  have hB : (P.take (s + 1 - k)).length = s + 1 - k := by rw [List.length_take]; omega
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by rw [hA]; omega), hA,
    List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show s - k < s + 1 - k by omega),
    ← List.getD_eq_getElem?_getD]

/-- A round of the same index gives the list's first places backwards. -/
theorem imtf_rot_get (L : List Nat) (s : Nat) (hs : s < L.length) {t : Nat} (ht : t ≤ s) :
    (inverseMoveToFrontFrom L (List.replicate (s + 1) s))[t]? = some (L.getD (s - t) 0) := by
  have e : List.replicate (s + 1) s = List.replicate t s ++ (s :: List.replicate (s - t) s) := by
    rw [← List.replicate_succ, List.replicate_append_replicate]
    congr 1
    omega
  rw [e, imtf_append, List.getElem?_append_right (by rw [inverseMoveToFrontFrom_length, List.length_replicate]; exact Nat.le_refl _),
    inverseMoveToFrontFrom_length, List.length_replicate, Nat.sub_self]
  rw [show inverseMoveToFrontFrom (mtfAfter L (List.replicate t s)) (s :: List.replicate (s - t) s) =
    (mtfAfter L (List.replicate t s)).getD s 0 :: inverseMoveToFrontFrom ((mtfAfter L (List.replicate t s)).getD s 0 ::
      (mtfAfter L (List.replicate t s)).eraseIdx s) (List.replicate (s - t) s) from rfl]
  rw [List.getElem?_cons_zero, mtfAfter_rot L s hs t (by omega), rot_getD _ _ (by rw [List.length_take]; omega) ht,
    List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left (show s - t < s + 1 by omega), ← List.getD_eq_getElem?_getD]

/-- A counter that is not zero counts down by one. -/
private theorem down1 {n : UInt64} (hn : ¬ n = 0) : n.toNat ≠ 0 ∧ (n - 1).toNat = n.toNat - 1 := by
  have h : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  exact ⟨h, UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))⟩

private theorem up1 {j : UInt64} (h : j.toNat + 1 < 2 ^ 64) : (j + 1).toNat = j.toNat + 1 := by
  rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
  exact Nat.mod_eq_of_lt h

/-- What `revOut` needs for its reads and writes to stay in the arrays. -/
def RevPre (m out : ByteArray) (i s j n : UInt64) : Prop :=
  j.toNat + n.toNat ≤ s.toNat + 1 ∧ s.toNat < 256 ∧ m.size = 256 ∧ i.toNat + j.toNat + n.toNat < 2 ^ 32 ∧
    i.toNat + j.toNat + n.toNat ≤ out.size

theorem RevPre.get {m out : ByteArray} {i s j n : UInt64} (h : RevPre m out i s j n) (hn : ¬ n = 0) :
    (s - j).toUSize.toNat < m.size := by
  obtain ⟨h1, h2, h3, _, _⟩ := h
  have := (down1 hn).1
  rw [word_toUSize (by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega),
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
  omega

theorem RevPre.set {m out : ByteArray} {i s j n : UInt64} (h : RevPre m out i s j n) (hn : ¬ n = 0) :
    (i + j).toUSize.toNat < out.size := by
  obtain ⟨_, _, _, h4, h5⟩ := h
  have := (down1 hn).1
  have hij : (i + j).toNat = i.toNat + j.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [word_toUSize (by omega), hij]
  omega

theorem RevPre.next {m out : ByteArray} {i s j n : UInt64} (h : RevPre m out i s j n) (hn : ¬ n = 0) {out' : ByteArray}
    (hs : out'.size = out.size) : RevPre m out' i s (j + 1) (n - 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hn0, hn1⟩ := down1 hn
  have hj1 := up1 (j := j) (by omega)
  exact ⟨by rw [hj1, hn1]; omega, h2, h3, by rw [hj1, hn1]; omega, by rw [hj1, hn1, hs]; omega⟩

/-- A run's first round of values: the `n` outputs from `j`, each the list's value `j` places before `s`. -/
def revOut (m out : ByteArray) (i s j n : UInt64) (h : RevPre m out i s j n) : ByteArray :=
  if hn : n = 0 then out
  else
    revOut m (out.uset (i + j).toUSize (m.uget (s - j).toUSize (h.get hn)) (h.set hn)) i s (j + 1) (n - 1)
      (h.next hn (size_uset' _ _ _ _))
termination_by n.toNat
decreasing_by
  have := down1 hn
  omega

theorem revOut_spec (m : ByteArray) (i s : UInt64) : ∀ (N : Nat) (j n : UInt64) (out : ByteArray) (h : RevPre m out i s j n),
    n.toNat = N →
    (revOut m out i s j n h).size = out.size ∧ (∀ q, q < i.toNat + j.toNat → (revOut m out i s j n h).data[q]? = out.data[q]?) ∧
    (∀ q, i.toNat + j.toNat + N ≤ q → (revOut m out i s j n h).data[q]? = out.data[q]?) ∧
    (∀ t, j.toNat ≤ t → t < j.toNat + N → (revOut m out i s j n h).data[i.toNat + t]?.getD 0 = m.data[s.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro j n out h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [revOut, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun t h1 h2 => absurd h2 (by omega)⟩
  | succ N ih =>
    intro j n out h hn
    obtain ⟨hjs, hs, hm, h32, hsz⟩ := id h
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hij : (i + j).toNat = i.toNat + j.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : (i + j).toUSize.toNat = i.toNat + j.toNat := by rw [word_toUSize (by omega), hij]
    have hsj : (s - j).toUSize.toNat = s.toNat - j.toNat := by
      rw [word_toUSize (by rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega),
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    rw [revOut, dite_eq_right hz]
    have hvb : m.uget (s - j).toUSize (h.get hz) = m.data[s.toNat - j.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [uget_toNat, hsj]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (n - 1) (out.uset (i + j).toUSize (m.uget (s - j).toUSize (h.get hz)) (h.set hz))
      (h.next hz (size_uset' _ _ _ _)) hn1
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_uset'], fun q hq => ?_, fun q hq => ?_, fun t h1 h2 => ?_⟩
    · rw [b2 q (by omega), uset_get_ne (h.set hz) (by rw [hus]; omega)]
    · rw [b3 q (by omega), uset_get_ne (h.set hz) (by rw [hus]; omega)]
    · by_cases ht : t = j.toNat
      · subst ht
        rw [b2 _ (by omega)]
        have := uset_get_same (t := out) (i := (i + j).toUSize) (v := m.uget (s - j).toUSize (h.get hz)) (h.set hz)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 t (by omega) (by omega)

/-- What `rotFrom` needs for its reads and writes to stay in the arrays. -/
def RotPre (out m : ByteArray) (i x a n : UInt64) : Prop :=
  (0 < n.toNat → n.toNat ≤ a.toNat + 1 ∧ i.toNat + a.toNat < 2 ^ 32 ∧ i.toNat + a.toNat < out.size) ∧ x.toNat + n.toNat ≤ 256 ∧
    m.size = 256

theorem RotPre.get {out m : ByteArray} {i x a n : UInt64} (h : RotPre out m i x a n) (hn : ¬ n = 0) :
    (i + a).toUSize.toNat < out.size := by
  obtain ⟨h1, _, _⟩ := h
  obtain ⟨_, h2, h3⟩ := h1 (by have := (down1 hn).1; omega)
  have hia : (i + a).toNat = i.toNat + a.toNat := by
    rw [UInt64.toNat_add]
    exact Nat.mod_eq_of_lt (by omega)
  rw [word_toUSize (by omega), hia]
  exact h3

theorem RotPre.set {out m : ByteArray} {i x a n : UInt64} (h : RotPre out m i x a n) (hn : ¬ n = 0) : x.toUSize.toNat < m.size := by
  obtain ⟨_, h2, h3⟩ := h
  have := (down1 hn).1
  rw [word_toUSize (by omega), h3]
  omega

theorem RotPre.next {out m : ByteArray} {i x a n : UInt64} (h : RotPre out m i x a n) (hn : ¬ n = 0) {m' : ByteArray}
    (hs : m'.size = m.size) : RotPre out m' i (x + 1) (a - 1) (n - 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hn0, hn1⟩ := down1 hn
  obtain ⟨ha1, ha2, ha3⟩ := h1 (by omega)
  have hx1 := up1 (j := x) (by omega)
  refine ⟨fun hp => ?_, by rw [hx1, hn1]; omega, by rw [hs, h3]⟩
  have hA : (a - 1).toNat = a.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
  rw [hn1] at hp
  rw [hn1, hA]
  omega

/-- Rewrites `n` places of the list from `x`, each from the outputs, going back from `a`. -/
def rotFrom (out m : ByteArray) (i x a n : UInt64) (h : RotPre out m i x a n) : ByteArray :=
  if hn : n = 0 then m
  else
    rotFrom out (m.uset x.toUSize (out.uget (i + a).toUSize (h.get hn)) (h.set hn)) i (x + 1) (a - 1) (n - 1)
      (h.next hn (size_uset' _ _ _ _))
termination_by n.toNat
decreasing_by
  have := down1 hn
  omega

theorem rotFrom_spec (out : ByteArray) (i : UInt64) : ∀ (N : Nat) (x a n : UInt64) (m : ByteArray) (h : RotPre out m i x a n),
    n.toNat = N →
    (rotFrom out m i x a n h).size = 256 ∧ (∀ y, y < x.toNat ∨ x.toNat + N ≤ y → (rotFrom out m i x a n h).data[y]? = m.data[y]?) ∧
    (∀ t, t < N → (rotFrom out m i x a n h).data[x.toNat + t]?.getD 0 = out.data[i.toNat + a.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro x a n m h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [rotFrom, dite_eq_left hz]
    exact ⟨h.2.2, fun _ _ => rfl, fun t h => absurd h (by omega)⟩
  | succ N ih =>
    intro x a n m h hn
    obtain ⟨ha, hx, hs⟩ := id h
    obtain ⟨ha1, ha2, _⟩ := ha (by omega)
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hx1 : (x + 1).toNat = x.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hia : (i + a).toNat = i.toNat + a.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : x.toUSize.toNat = x.toNat := word_toUSize (by omega)
    have husa : (i + a).toUSize.toNat = i.toNat + a.toNat := by rw [word_toUSize (by omega), hia]
    rw [rotFrom, dite_eq_right hz]
    have hvb : out.uget (i + a).toUSize (h.get hz) = out.data[i.toNat + a.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [uget_toNat, husa]
    obtain ⟨b1, b2, b3⟩ := ih (x + 1) (a - 1) (n - 1) (m.uset x.toUSize (out.uget (i + a).toUSize (h.get hz)) (h.set hz))
      (h.next hz (size_uset' _ _ _ _)) hn1
    rw [hx1] at b2 b3
    refine ⟨b1, fun y hy => ?_, fun t ht => ?_⟩
    · rw [b2 y (by omega), uset_get_ne (h.set hz) (by rw [hus]; omega)]
    · by_cases ht0 : t = 0
      · subst ht0
        rw [Nat.add_zero, b2 _ (by omega)]
        have := uset_get_same (t := m) (i := x.toUSize) (v := out.uget (i + a).toUSize (h.get hz)) (h.set hz)
        rw [hus] at this
        rw [this, hvb, Nat.sub_zero]
      · have ha1' : (a - 1).toNat = a.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
        have := b3 (t - 1) (by omega)
        rw [ha1', show x.toNat + 1 + (t - 1) = x.toNat + t by omega, show i.toNat + (a.toNat - 1) - (t - 1) = i.toNat + a.toNat - t by omega]
          at this
        exact this

/-- What `copyPeriod` needs for its reads and writes to stay in the array. -/
def CopyPre (out : ByteArray) (j k p : UInt64) : Prop :=
  1 ≤ p.toNat ∧ p.toNat ≤ j.toNat ∧ j.toNat + k.toNat < 2 ^ 32 ∧ j.toNat + k.toNat ≤ out.size

theorem CopyPre.get {out : ByteArray} {j k p : UInt64} (h : CopyPre out j k p) (hk : ¬ k = 0) : (j - p).toUSize.toNat < out.size := by
  obtain ⟨_, h2, h3, h4⟩ := h
  have := (down1 hk).1
  have hjp : (j - p).toNat = j.toNat - p.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h2)
  rw [word_toUSize (by omega), hjp]
  omega

theorem CopyPre.set {out : ByteArray} {j k p : UInt64} (h : CopyPre out j k p) (hk : ¬ k = 0) : j.toUSize.toNat < out.size := by
  obtain ⟨_, _, h3, h4⟩ := h
  have := (down1 hk).1
  rw [word_toUSize (by omega)]
  omega

theorem CopyPre.next {out : ByteArray} {j k p : UInt64} (h : CopyPre out j k p) (hk : ¬ k = 0) {out' : ByteArray}
    (hs : out'.size = out.size) : CopyPre out' (j + 1) (k - 1) p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨hk0, hk1⟩ := down1 hk
  have hj1 := up1 (j := j) (by omega)
  exact ⟨h1, by rw [hj1]; omega, by rw [hj1, hk1]; omega, by rw [hj1, hk1, hs]; omega⟩

/-- Copies `k` bytes from `p` places back, one at a time, so that from `j` on the bytes repeat with period `p`. -/
def copyPeriod (out : ByteArray) (j k p : UInt64) (h : CopyPre out j k p) : ByteArray :=
  if hk : k = 0 then out
  else copyPeriod (out.uset j.toUSize (out.uget (j - p).toUSize (h.get hk)) (h.set hk)) (j + 1) (k - 1) p (h.next hk (size_uset' _ _ _ _))
termination_by k.toNat
decreasing_by
  have := down1 hk
  omega

theorem copyPeriod_spec (p : UInt64) : ∀ (K : Nat) (j k : UInt64) (out : ByteArray) (h : CopyPre out j k p), k.toNat = K →
    (copyPeriod out j k p h).size = out.size ∧ (∀ q, q < j.toNat → (copyPeriod out j k p h).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat + K ≤ q → (copyPeriod out j k p h).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat ≤ q → q < j.toNat + K →
      (copyPeriod out j k p h).data[q]?.getD 0 = (copyPeriod out j k p h).data[q - p.toNat]?.getD 0) := by
  intro K
  induction K with
  | zero =>
    intro j k out h hk
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [copyPeriod, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun q h1 h2 => absurd h2 (by omega)⟩
  | succ K ih =>
    intro j k out h hk
    obtain ⟨hp, hpj, h32, hs⟩ := id h
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hjp : (j - p).toNat = j.toNat - p.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hpj)
    have hus : j.toUSize.toNat = j.toNat := word_toUSize (by omega)
    have husp : (j - p).toUSize.toNat = j.toNat - p.toNat := by rw [word_toUSize (by omega), hjp]
    rw [copyPeriod, dite_eq_right hz]
    have hvb : out.uget (j - p).toUSize (h.get hz) = out.data[j.toNat - p.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [uget_toNat, husp]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (k - 1) (out.uset j.toUSize (out.uget (j - p).toUSize (h.get hz)) (h.set hz))
      (h.next hz (size_uset' _ _ _ _)) hk1
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_uset'], fun q hq => ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩
    · rw [b2 q (by omega), uset_get_ne (h.set hz) (by rw [hus]; omega)]
    · rw [b3 q (by omega), uset_get_ne (h.set hz) (by rw [hus]; omega)]
    · by_cases hq : q = j.toNat
      · subst hq
        rw [b2 _ (by omega), b2 _ (by omega), uset_get_ne (h.set hz) (show j.toNat - p.toNat ≠ j.toUSize.toNat by rw [hus]; omega)]
        have := uset_get_same (t := out) (i := j.toUSize) (v := out.uget (j - p).toUSize (h.get hz)) (h.set hz)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 q (by omega) (by omega)

/-- What `shiftBy` needs for its reads and writes to stay in the list. -/
def ShiftPre (m : ByteArray) (x k n : UInt64) : Prop :=
  (0 < n.toNat → k.toNat + n.toNat ≤ x.toNat + 1 ∧ x.toNat < 256) ∧ 1 ≤ k.toNat ∧ m.size = 256

theorem ShiftPre.get {m : ByteArray} {x k n : UInt64} (h : ShiftPre m x k n) (hn : ¬ n = 0) : (x - k).toUSize.toNat < m.size := by
  obtain ⟨h1, _, h3⟩ := h
  have hn0 := (down1 hn).1
  obtain ⟨h4, h5⟩ := h1 (by omega)
  have hxk : (x - k).toNat = x.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
  rw [word_toUSize (by omega), hxk, h3]
  omega

theorem ShiftPre.set {m : ByteArray} {x k n : UInt64} (h : ShiftPre m x k n) (hn : ¬ n = 0) : x.toUSize.toNat < m.size := by
  obtain ⟨h1, _, h3⟩ := h
  obtain ⟨_, h5⟩ := h1 (by have := (down1 hn).1; omega)
  rw [word_toUSize (by omega), h3]
  exact h5

theorem ShiftPre.next {m : ByteArray} {x k n : UInt64} (h : ShiftPre m x k n) (hn : ¬ n = 0) {m' : ByteArray}
    (hs : m'.size = m.size) : ShiftPre m' (x - 1) k (n - 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hn0, hn1⟩ := down1 hn
  obtain ⟨h4, h5⟩ := h1 (by omega)
  refine ⟨fun hp => ?_, h2, by rw [hs, h3]⟩
  have hX : (x - 1).toNat = x.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
  rw [hn1] at hp
  rw [hn1, hX]
  omega

/-- Moves `n` places of the list up `k` places, from place `x` down: each takes the value `k` places before it. -/
def shiftBy (m : ByteArray) (x k n : UInt64) (h : ShiftPre m x k n) : ByteArray :=
  if hn : n = 0 then m
  else shiftBy (m.uset x.toUSize (m.uget (x - k).toUSize (h.get hn)) (h.set hn)) (x - 1) k (n - 1) (h.next hn (size_uset' _ _ _ _))
termination_by n.toNat
decreasing_by
  have := down1 hn
  omega

theorem shiftBy_spec (k : UInt64) : ∀ (N : Nat) (m : ByteArray) (x n : UInt64) (h : ShiftPre m x k n), n.toNat = N →
    (shiftBy m x k n h).size = 256 ∧ ∀ y, y < 256 → (shiftBy m x k n h).data[y]?.getD 0 =
      if x.toNat + 1 - N ≤ y ∧ y ≤ x.toNat then m.data[y - k.toNat]?.getD 0 else m.data[y]?.getD 0 := by
  intro N
  induction N with
  | zero =>
    intro m x n h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [shiftBy, dite_eq_left hz]
    exact ⟨h.2.2, fun y _ => by rw [ite_eq_right (by omega)]⟩
  | succ N ih =>
    intro m x n h hn
    obtain ⟨hx, hk, hs⟩ := id h
    obtain ⟨hx1, hx2⟩ := hx (by omega)
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hus : x.toUSize.toNat = x.toNat := word_toUSize (by omega)
    have hxk : (x - k).toNat = x.toNat - k.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))
    have husk : (x - k).toUSize.toNat = x.toNat - k.toNat := by rw [word_toUSize (by omega), hxk]
    have hX : 0 < N → (x - 1).toNat = x.toNat - 1 := fun _ =>
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
    rw [shiftBy, dite_eq_right hz]
    have hvb : m.uget (x - k).toUSize (h.get hz) = m.data[x.toNat - k.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [uget_toNat, husk]
    obtain ⟨i1, i2⟩ := ih (m.uset x.toUSize (m.uget (x - k).toUSize (h.get hz)) (h.set hz)) (x - 1) (n - 1)
      (h.next hz (size_uset' _ _ _ _)) hn1
    refine ⟨i1, fun y hy => ?_⟩
    rw [i2 y hy]
    by_cases hyx : y = x.toNat
    · subst hyx
      have hc : ¬ ((x - 1).toNat + 1 - N ≤ x.toNat ∧ x.toNat ≤ (x - 1).toNat) := by
        by_cases hN : 0 < N
        · rw [hX hN]; omega
        · omega
      rw [ite_eq_right hc, ite_eq_left (by omega)]
      have := uset_get_same (t := m) (i := x.toUSize) (v := m.uget (x - k).toUSize (h.get hz)) (h.set hz)
      rw [hus] at this
      rw [this, hvb]
    · by_cases hin : x.toNat + 1 - (N + 1) ≤ y ∧ y ≤ x.toNat
      · have hN : 0 < N := by omega
        have hc : (x - 1).toNat + 1 - N ≤ y ∧ y ≤ (x - 1).toNat := by rw [hX hN]; omega
        rw [ite_eq_left hc, ite_eq_left hin, uset_get_ne (h.set hz) (by rw [hus]; omega)]
      · have hc : ¬ ((x - 1).toNat + 1 - N ≤ y ∧ y ≤ (x - 1).toNat) := by
          by_cases hN : 0 < N
          · rw [hX hN]; omega
          · omega
        rw [ite_eq_right hc, ite_eq_right hin, uset_get_ne (h.set hz) (by rw [hus]; exact hyx)]

/-! The loops, with the sizes they keep, for the loops that follow them. -/

@[inline] def revOutS (m out : ByteArray) (i s j n : UInt64) (h : RevPre m out i s j n) : { r : ByteArray // r.size = out.size } :=
  ⟨revOut m out i s j n h, (revOut_spec m i s _ j n out h rfl).1⟩

theorem revOutS_val {m out : ByteArray} {i s j n : UInt64} {h : RevPre m out i s j n} :
    (revOutS m out i s j n h).1 = revOut m out i s j n h := rfl

@[inline] def shiftByS (m : ByteArray) (x k n : UInt64) (h : ShiftPre m x k n) : { r : ByteArray // r.size = 256 } :=
  ⟨shiftBy m x k n h, (shiftBy_spec k _ m x n h rfl).1⟩

theorem shiftByS_val {m : ByteArray} {x k n : UInt64} {h : ShiftPre m x k n} : (shiftByS m x k n h).1 = shiftBy m x k n h := rfl

@[inline] def copyPeriodS (out : ByteArray) (j k p : UInt64) (h : CopyPre out j k p) : { r : ByteArray // r.size = out.size } :=
  ⟨copyPeriod out j k p h, (copyPeriod_spec p _ j k out h rfl).1⟩

theorem copyPeriodS_val {out : ByteArray} {j k p : UInt64} {h : CopyPre out j k p} :
    (copyPeriodS out j k p h).1 = copyPeriod out j k p h := rfl

@[inline] def rotFromS (out m : ByteArray) (i x a n : UInt64) (h : RotPre out m i x a n) : { r : ByteArray // r.size = 256 } :=
  ⟨rotFrom out m i x a n h, (rotFrom_spec out i _ x a n m h rfl).1⟩

theorem rotFromS_val {out m : ByteArray} {i x a n : UInt64} {h : RotPre out m i x a n} :
    (rotFromS out m i x a n h).1 = rotFrom out m i x a n h := rfl

/-- What `imtfRun` needs for its reads and writes to stay in the arrays. -/
def RunPre (m out : ByteArray) (i s k : UInt64) : Prop :=
  m.size = 256 ∧ s.toNat < 256 ∧ 1 ≤ k.toNat ∧ i.toNat + k.toNat < 2 ^ 32 ∧ i.toNat + k.toNat ≤ out.size

section
variable {m out : ByteArray} {i s k : UInt64}

theorem run_rev1 (h : RunPre m out i s k) (hks : k ≤ s) : RevPre m out i s 0 k := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have := UInt64.le_iff_toNat_le.mp hks
  have hz : (0 : UInt64).toNat = 0 := rfl
  exact ⟨by rw [hz]; omega, h2, h1, by rw [hz]; omega, by rw [hz]; omega⟩

theorem run_shift (h : RunPre m out i s k) (hks : k ≤ s) : ShiftPre m s k (s + 1 - k) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hks' := UInt64.le_iff_toNat_le.mp hks
  have hp1 : (s + 1).toNat = s.toNat + 1 := up1 (by omega)
  have hsk : (s + 1 - k).toNat = s.toNat + 1 - k.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
  exact ⟨fun _ => ⟨by rw [hsk]; omega, h2⟩, h3, h1⟩

theorem run_rot1 (h : RunPre m out i s k) (hks : k ≤ s) {out1 m1 : ByteArray} (h1 : out1.size = out.size) (h2 : m1.size = 256) :
    RotPre out1 m1 i 0 (k - 1) k := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := h
  have hks' := UInt64.le_iff_toNat_le.mp hks
  have hk1 : (k - 1).toNat = k.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
  have hz : (0 : UInt64).toNat = 0 := rfl
  exact ⟨fun _ => ⟨by rw [hk1]; omega, by rw [hk1]; omega, by rw [hk1, h1]; omega⟩, by rw [hz]; omega, h2⟩

theorem run_rev2 (h : RunPre m out i s k) (hks : ¬ k ≤ s) : RevPre m out i s 0 (s + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
  have hp1 : (s + 1).toNat = s.toNat + 1 := up1 (by omega)
  have hz : (0 : UInt64).toNat = 0 := rfl
  exact ⟨by rw [hz, hp1]; omega, h2, h1, by rw [hz, hp1]; omega, by rw [hz, hp1]; omega⟩

theorem run_copy (h : RunPre m out i s k) (hks : ¬ k ≤ s) {out0 : ByteArray} (h0 : out0.size = out.size) :
    CopyPre out0 (i + (s + 1)) (k - (s + 1)) (s + 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
  have hp1 : (s + 1).toNat = s.toNat + 1 := up1 (by omega)
  have hip : (i + (s + 1)).toNat = i.toNat + (s.toNat + 1) := by
    rw [UInt64.toNat_add, hp1]
    exact Nat.mod_eq_of_lt (by omega)
  have hrs : (k - (s + 1)).toNat = k.toNat - (s.toNat + 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
  exact ⟨by rw [hp1]; omega, by rw [hp1, hip]; omega, by rw [hip, hrs]; omega, by rw [hip, hrs, h0]; omega⟩

private theorem run_mod (hks : ¬ k ≤ s) (hs : s.toNat < 256) :
    ((k - (s + 1)) % (s + 1)).toNat < s.toNat + 1 := by
  have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
  have hp1 : (s + 1).toNat = s.toNat + 1 := up1 (by omega)
  rw [UInt64.toNat_mod, hp1]
  exact Nat.mod_lt _ (by omega)

theorem run_rot2 (h : RunPre m out i s k) (hks : ¬ k ≤ s) {out1 : ByteArray} (h1 : out1.size = out.size) :
    RotPre out1 m i 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := h
  have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
  have hK := run_mod hks g2
  generalize (k - (s + 1)) % (s + 1) = K at hK ⊢
  have hz : (0 : UInt64).toNat = 0 := rfl
  refine ⟨fun hK0 => ?_, by rw [hz]; omega, g1⟩
  have hK1 : (K - 1).toNat = K.toNat - 1 :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
  exact ⟨by rw [hK1]; omega, by rw [hK1]; omega, by rw [hK1, h1]; omega⟩

theorem run_rot3 (h : RunPre m out i s k) (hks : ¬ k ≤ s) {out1 m1 : ByteArray} (h1 : out1.size = out.size) (h2 : m1.size = 256) :
    RotPre out1 m1 i ((k - (s + 1)) % (s + 1)) s (s + 1 - (k - (s + 1)) % (s + 1)) := by
  obtain ⟨g1, g2, g3, g4, g5⟩ := h
  have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
  have hp1 : (s + 1).toNat = s.toNat + 1 := up1 (by omega)
  have hK := run_mod hks g2
  generalize (k - (s + 1)) % (s + 1) = K at hK ⊢
  have hpK : (s + 1 - K).toNat = s.toNat + 1 - K.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
  exact ⟨fun _ => ⟨by rw [hpK]; omega, by omega, by rw [h1]; omega⟩, by rw [hpK]; omega, h2⟩

end

/-- The transform of a run of `k` copies of index `s`, from the list `m`, into `out` from `i`. The values of a round are
the list's first places backwards, and after a whole round they repeat; the list's first `s + 1` places turn round, those
the run took from the values and the rest moved up. -/
def imtfRun (m out : ByteArray) (i s k : UInt64) (h : RunPre m out i s k) : ByteArray × ByteArray :=
  if hks : k ≤ s then
    match revOutS m out i s 0 k (run_rev1 h hks) with
    | ⟨out1, h1⟩ =>
      match shiftByS m s k (s + 1 - k) (run_shift h hks) with
      | ⟨m1, h2⟩ => (rotFrom out1 m1 i 0 (k - 1) k (run_rot1 h hks h1 h2), out1)
  else
    match revOutS m out i s 0 (s + 1) (run_rev2 h hks) with
    | ⟨out0, h0⟩ =>
      match copyPeriodS out0 (i + (s + 1)) (k - (s + 1)) (s + 1) (run_copy h hks h0) with
      | ⟨out1, h1⟩ =>
        match rotFromS out1 m i 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) (run_rot2 h hks (h1.trans h0)) with
        | ⟨m1, h2⟩ =>
          (rotFrom out1 m1 i ((k - (s + 1)) % (s + 1)) s (s + 1 - (k - (s + 1)) % (s + 1)) (run_rot3 h hks (h1.trans h0) h2), out1)

/-- What a run does: the transform of its indices, from `i` in the outputs, with the rest of them as they were, and the list
after them. -/
theorem imtfRun_spec {m out : ByteArray} {i s k : UInt64} {L : List Nat} (hm : MtfIs m L) (hs : s.toNat < 256) (hk : 1 ≤ k.toNat)
    (h32 : i.toNat + k.toNat < 2 ^ 32) {h : RunPre m out i s k} :
    (imtfRun m out i s k h).2.size = out.size ∧
    (∀ t, t < k.toNat → (inverseMoveToFrontFrom L (List.replicate k.toNat s.toNat))[t]? =
      some ((imtfRun m out i s k h).2.data[i.toNat + t]?.getD 0).toNat) ∧
    (∀ q, q < i.toNat ∨ i.toNat + k.toNat ≤ q → (imtfRun m out i s k h).2.data[q]? = out.data[q]?) ∧
    MtfIs (imtfRun m out i s k h).1 (mtfAfter L (List.replicate k.toNat s.toNat)) := by
  have hsL : s.toNat < L.length := by rw [hm.length]; exact hs
  have hL := hm.length
  have hz0 : (0 : UInt64).toNat = 0 := rfl
  have hp1 : (s + 1).toNat = s.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  -- A round's values are the list's first places backwards.
  have hround : ∀ t, t ≤ s.toNat → t < k.toNat →
      (inverseMoveToFrontFrom L (List.replicate k.toNat s.toNat))[t]? = some (L.getD (s.toNat - t) 0) := by
    intro t ht htk
    by_cases hkp : k.toNat ≤ s.toNat + 1
    · have e : List.replicate (s.toNat + 1) s.toNat =
          List.replicate k.toNat s.toNat ++ List.replicate (s.toNat + 1 - k.toNat) s.toNat := by
        rw [List.replicate_append_replicate]
        congr 1
        omega
      rw [← imtf_prefix L _ (List.replicate (s.toNat + 1 - k.toNat) s.toNat) (by rw [List.length_replicate]; exact htk), ← e,
        imtf_rot_get L _ hsL ht]
    · have e : List.replicate k.toNat s.toNat =
          List.replicate (s.toNat + 1) s.toNat ++ List.replicate (k.toNat - (s.toNat + 1)) s.toNat := by
        rw [List.replicate_append_replicate]
        congr 1
        omega
      rw [e, imtf_prefix L _ _ (by rw [List.length_replicate]; omega), imtf_rot_get L _ hsL ht]
  unfold imtfRun
  by_cases hks : k ≤ s
  · rw [dite_eq_left hks]
    have hks' : k.toNat ≤ s.toNat := UInt64.le_iff_toNat_le.mp hks
    obtain ⟨o1, o2, o3, o4⟩ := revOut_spec m i s k.toNat 0 k out (run_rev1 h hks) rfl
    rw [hz0, Nat.add_zero] at o2 o3
    rw [hz0] at o4
    generalize hR1 : revOutS m out i s 0 k (run_rev1 h hks) = R1
    obtain ⟨out1, ho1⟩ := R1
    have e1 : out1 = revOut m out i s 0 k (run_rev1 h hks) := by rw [← revOutS_val, hR1]
    rw [← e1] at o1 o2 o3 o4
    dsimp only
    have hsk : (s + 1 - k).toNat = s.toNat + 1 - k.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨b1, b2⟩ := shiftBy_spec k (s.toNat + 1 - k.toNat) m s (s + 1 - k) (run_shift h hks) hsk
    generalize hR2 : shiftByS m s k (s + 1 - k) (run_shift h hks) = R2
    obtain ⟨m1, hm1⟩ := R2
    have e2 : m1 = shiftBy m s k (s + 1 - k) (run_shift h hks) := by rw [← shiftByS_val, hR2]
    rw [← e2] at b1 b2
    dsimp only
    have hk1 : (k - 1).toNat = k.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
    obtain ⟨c1, c2, c3⟩ := rotFrom_spec out1 i k.toNat 0 (k - 1) k m1 (run_rot1 h hks ho1 hm1) rfl
    rw [hz0] at c2 c3
    rw [hk1] at c3
    refine ⟨o1, fun t ht => ?_, fun q hq => ?_, ?_⟩
    · rw [hround t (by omega) ht, o4 t (Nat.zero_le _) (by omega), hm.at_ _ (by omega)]
    · rcases hq with hq | hq
      · exact o2 q hq
      · exact o3 q hq
    · rw [mtfAfter_rot L _ hsL k.toNat (by omega)]
      have hA : ((L.take (s.toNat + 1)).drop (s.toNat + 1 - k.toNat)).length = k.toNat := by
        rw [List.length_drop, List.length_take]; omega
      have hB : ((L.take (s.toNat + 1)).take (s.toNat + 1 - k.toNat)).length = s.toNat + 1 - k.toNat := by
        rw [List.length_take, List.length_take]; omega
      refine ⟨c1, by simp only [List.length_append, hA, hB, List.length_drop]; omega, fun x hx => ?_⟩
      rw [List.getD_eq_getElem?_getD, List.append_assoc]
      by_cases h1 : x < k.toNat
      · rw [List.getElem?_append_left (by rw [hA]; exact h1), List.getElem?_drop, List.getElem?_take,
          ite_eq_left (show s.toNat + 1 - k.toNat + x < s.toNat + 1 by omega), ← List.getD_eq_getElem?_getD]
        have := c3 x h1
        rw [Nat.zero_add] at this
        rw [this, show i.toNat + (k.toNat - 1) - x = i.toNat + (k.toNat - 1 - x) by omega, o4 _ (Nat.zero_le _) (by omega),
          show s.toNat - (k.toNat - 1 - x) = s.toNat + 1 - k.toNat + x by omega, hm.at_ _ (by omega)]
      · rw [List.getElem?_append_right (by rw [hA]; omega), hA, c2 x (Or.inr (by omega)), b2 x hx]
        by_cases h2 : x ≤ s.toNat
        · rw [ite_eq_left (show s.toNat + 1 - (s.toNat + 1 - k.toNat) ≤ x ∧ x ≤ s.toNat by omega),
            List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show x - k.toNat < s.toNat + 1 - k.toNat by omega),
            List.getElem?_take, ite_eq_left (show x - k.toNat < s.toNat + 1 by omega), ← List.getD_eq_getElem?_getD,
            hm.at_ _ (by omega)]
        · rw [ite_eq_right (show ¬ (s.toNat + 1 - (s.toNat + 1 - k.toNat) ≤ x ∧ x ≤ s.toNat) by omega),
            List.getElem?_append_right (by rw [hB]; omega), hB, List.getElem?_drop,
            show s.toNat + 1 + (x - k.toNat - (s.toNat + 1 - k.toNat)) = x by omega, ← List.getD_eq_getElem?_getD, hm.at_ x hx]
  · rw [dite_eq_right hks]
    have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
    obtain ⟨o1, o2, o3, o4⟩ := revOut_spec m i s (s.toNat + 1) 0 (s + 1) out (run_rev2 h hks) hp1
    rw [hz0, Nat.add_zero] at o2 o3
    rw [hz0] at o4
    generalize hR1 : revOutS m out i s 0 (s + 1) (run_rev2 h hks) = R1
    obtain ⟨out1, ho1⟩ := R1
    have e1 : out1 = revOut m out i s 0 (s + 1) (run_rev2 h hks) := by rw [← revOutS_val, hR1]
    rw [← e1] at o1 o2 o3 o4
    dsimp only
    have hip : (i + (s + 1)).toNat = i.toNat + (s.toNat + 1) := by
      rw [UInt64.toNat_add, hp1]
      exact Nat.mod_eq_of_lt (by omega)
    have hrs : (k - (s + 1)).toNat = k.toNat - (s.toNat + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨q1, q2, q3, q4⟩ := copyPeriod_spec (s + 1) (k.toNat - (s.toNat + 1)) (i + (s + 1)) (k - (s + 1)) out1
      (run_copy h hks ho1) hrs
    rw [hip] at q2 q3 q4
    rw [hp1] at q4
    generalize hR2 : copyPeriodS out1 (i + (s + 1)) (k - (s + 1)) (s + 1) (run_copy h hks ho1) = R2
    obtain ⟨out2, ho2⟩ := R2
    have e2 : out2 = copyPeriod out1 (i + (s + 1)) (k - (s + 1)) (s + 1) (run_copy h hks ho1) := by
      rw [← copyPeriodS_val, hR2]
    rw [← e2] at q1 q2 q3 q4
    dsimp only
    -- The round's values, in the outputs, are the list's first places backwards.
    have hfirst : ∀ t, t ≤ s.toNat → (out2.data[i.toNat + t]?.getD 0).toNat = L.getD (s.toNat - t) 0 := by
      intro t ht
      rw [q2 _ (by omega), o4 t (Nat.zero_le _) (by omega), hm.at_ _ (by omega)]
    -- The list after the run: its first places turned round as far as the run goes past whole rounds.
    have hK : (k.toNat - (s.toNat + 1)) % (s.toNat + 1) < s.toNat + 1 := Nat.mod_lt _ (by omega)
    generalize hKd : (k.toNat - (s.toNat + 1)) % (s.toNat + 1) = K at hK
    have hkK : ((k - (s + 1)) % (s + 1)).toNat = K := by rw [UInt64.toNat_mod, hrs, hp1, hKd]
    obtain ⟨a1, a2, a3⟩ := rotFrom_spec out2 i K 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) m
      (run_rot2 h hks (ho2.trans ho1)) hkK
    generalize hR3 : rotFromS out2 m i 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) (run_rot2 h hks (ho2.trans ho1)) = R3
    obtain ⟨m1, hm1⟩ := R3
    have e3 : m1 = rotFrom out2 m i 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) (run_rot2 h hks (ho2.trans ho1)) := by
      rw [← rotFromS_val, hR3]
    rw [← e3] at a1 a2 a3
    dsimp only
    have hpk : (s + 1 - (k - (s + 1)) % (s + 1)).toNat = s.toNat + 1 - K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hkK, hp1]; omega)), hkK, hp1]
    obtain ⟨c1, c2, c3⟩ := rotFrom_spec out2 i (s.toNat + 1 - K) ((k - (s + 1)) % (s + 1)) s (s + 1 - (k - (s + 1)) % (s + 1)) m1
      (run_rot3 h hks (ho2.trans ho1) hm1) hpk
    rw [hz0] at a2 a3
    rw [hkK] at c2 c3
    have hms : MtfIs (rotFrom out2 m1 i ((k - (s + 1)) % (s + 1)) s (s + 1 - (k - (s + 1)) % (s + 1)) (run_rot3 h hks (ho2.trans ho1) hm1))
        (mtfAfter L (List.replicate k.toNat s.toNat)) := by
      rw [mtfAfter_mod L _ hsL, Nat.mod_eq_sub_mod (by omega), hKd, mtfAfter_rot L _ hsL K (by omega)]
      have hA : ((L.take (s.toNat + 1)).drop (s.toNat + 1 - K)).length = K := by
        rw [List.length_drop, List.length_take]; omega
      have hB : ((L.take (s.toNat + 1)).take (s.toNat + 1 - K)).length = s.toNat + 1 - K := by
        rw [List.length_take, List.length_take]; omega
      refine ⟨c1, by simp only [List.length_append, hA, hB, List.length_drop]; omega, fun x hx => ?_⟩
      rw [List.getD_eq_getElem?_getD, List.append_assoc]
      by_cases h1 : x < K
      · rw [List.getElem?_append_left (by rw [hA]; exact h1), List.getElem?_drop, List.getElem?_take,
          ite_eq_left (show s.toNat + 1 - K + x < s.toNat + 1 by omega), ← List.getD_eq_getElem?_getD,
          c2 x (Or.inl h1)]
        have := a3 x h1
        have hk1 : ((k - (s + 1)) % (s + 1) - 1).toNat = K - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hkK, show (1 : UInt64).toNat = 1 from rfl]; omega)), hkK]
          rfl
        rw [show 0 + x = x by omega, hk1] at this
        rw [this, show i.toNat + (K - 1) - x = i.toNat + (K - 1 - x) by omega, hfirst _ (by omega)]
        congr 1
        omega
      · rw [List.getElem?_append_right (by rw [hA]; omega), hA]
        by_cases h2 : x ≤ s.toNat
        · rw [List.getElem?_append_left (by rw [hB]; omega), List.getElem?_take, ite_eq_left (show x - K < s.toNat + 1 - K by omega),
            List.getElem?_take, ite_eq_left (show x - K < s.toNat + 1 by omega), ← List.getD_eq_getElem?_getD]
          have := c3 (x - K) (by omega)
          rw [show K + (x - K) = x by omega] at this
          rw [this, show i.toNat + s.toNat - (x - K) = i.toNat + (s.toNat - (x - K)) by omega, hfirst _ (by omega)]
          congr 1
          omega
        · rw [List.getElem?_append_right (by rw [hB]; omega), hB, List.getElem?_drop,
            show s.toNat + 1 + (x - K - (s.toNat + 1 - K)) = x by omega, ← List.getD_eq_getElem?_getD,
            c2 x (Or.inr (by omega)), a2 x (Or.inr (by omega)), hm.at_ x hx]
    refine ⟨q1.trans o1, fun t => ?_, fun q hq => ?_, hms⟩
    · induction t using Nat.strongRecOn with
      | _ t iht =>
        intro ht
        by_cases hlo : t ≤ s.toNat
        · rw [hround t hlo ht, hfirst t hlo]
        · rw [q4 (i.toNat + t) (by omega) (by omega), show i.toNat + t - (s.toNat + 1) = i.toNat + (t - (s.toNat + 1)) by omega,
            ← iht (t - (s.toNat + 1)) (by omega) (by omega), show t = t - (s.toNat + 1) + (s.toNat + 1) by omega,
            imtf_periodic L _ hsL (by omega), Nat.add_sub_cancel]
    · rcases hq with hq | hq
      · rw [q2 q (by omega), o2 q hq]
      · rw [q3 q (by omega), o3 q (by omega)]

/-- What `markAll` needs for its reads and writes to stay in the arrays. -/
def MarkPre (map flags : ByteArray) (i n : UInt64) : Prop := i.toNat + n.toNat < 2 ^ 32 ∧ i.toNat + n.toNat ≤ map.size ∧ flags.size = 256

theorem MarkPre.get {map flags : ByteArray} {i n : UInt64} (h : MarkPre map flags i n) (hn : ¬ n = 0) : i.toUSize.toNat < map.size := by
  obtain ⟨h1, h2, _⟩ := h
  have := (down1 hn).1
  rw [word_toUSize (by omega)]
  omega

theorem MarkPre.set {map flags : ByteArray} {i n : UInt64} (h : MarkPre map flags i n) (v : UInt8) :
    v.toUInt64.toUSize.toNat < flags.size := by
  have := v.toNat_lt
  rw [word_toUSize (by rw [UInt8.toNat_toUInt64]; omega), UInt8.toNat_toUInt64, h.2.2]
  exact this

theorem MarkPre.next {map flags : ByteArray} {i n : UInt64} (h : MarkPre map flags i n) (hn : ¬ n = 0) {f : ByteArray}
    (hs : f.size = flags.size) : MarkPre map f (i + 1) (n - 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨hn0, hn1⟩ := down1 hn
  have hi1 := up1 (j := i) (by omega)
  exact ⟨by rw [hi1, hn1]; omega, by rw [hi1, hn1]; omega, by rw [hs, h3]⟩

/-- A run's transformed values are as many as before. -/
theorem imtfRun_size (m out : ByteArray) (i s k : UInt64) (h : RunPre m out i s k) : (imtfRun m out i s k h).2.size = out.size := by
  unfold imtfRun
  by_cases hks : k ≤ s
  · rw [dite_eq_left hks]
    generalize revOutS m out i s 0 k (run_rev1 h hks) = R1
    obtain ⟨out1, ho1⟩ := R1
    dsimp only
    generalize shiftByS m s k (s + 1 - k) (run_shift h hks) = R2
    obtain ⟨m1, hm1⟩ := R2
    exact ho1
  · rw [dite_eq_right hks]
    generalize revOutS m out i s 0 (s + 1) (run_rev2 h hks) = R1
    obtain ⟨out0, ho0⟩ := R1
    dsimp only
    generalize copyPeriodS out0 (i + (s + 1)) (k - (s + 1)) (s + 1) (run_copy h hks ho0) = R2
    obtain ⟨out1, ho1⟩ := R2
    dsimp only
    generalize rotFromS out1 m i 0 ((k - (s + 1)) % (s + 1) - 1) ((k - (s + 1)) % (s + 1)) (run_rot2 h hks (ho1.trans ho0)) = R3
    obtain ⟨m1, hm1⟩ := R3
    exact ho1.trans ho0

/-- A run, with the size of its transformed values. -/
@[inline] def imtfRunS (m out : ByteArray) (i s k : UInt64) (h : RunPre m out i s k) :
    { p : ByteArray × ByteArray // p.2.size = out.size } :=
  ⟨imtfRun m out i s k h, imtfRun_size m out i s k h⟩

theorem imtfRunS_val {m out : ByteArray} {i s k : UInt64} {h : RunPre m out i s k} :
    (imtfRunS m out i s k h).1 = imtfRun m out i s k h := rfl

/-- Marks the values of `n` bytes from `i`. -/
def markAll (map flags : ByteArray) (i n : UInt64) (h : MarkPre map flags i n) : ByteArray :=
  if hn : n = 0 then flags
  else
    markAll map (flags.uset (map.uget i.toUSize (h.get hn)).toUInt64.toUSize 1 (h.set _)) (i + 1) (n - 1)
      (h.next hn (size_uset' _ _ _ _))
termination_by n.toNat
decreasing_by
  have := down1 hn
  omega

theorem markAll_spec (map : ByteArray) : ∀ (N : Nat) (flags : ByteArray) (i n : UInt64) (h : MarkPre map flags i n), n.toNat = N →
    (markAll map flags i n h).size = 256 ∧ ∀ t, t < 256 → ((markAll map flags i n h).data[t]?.getD 0 ≠ 0 ↔
      (flags.data[t]?.getD 0 ≠ 0 ∨ ∃ j, i.toNat ≤ j ∧ j < i.toNat + N ∧ (map.data[j]?.getD 0).toNat = t)) := by
  intro N
  induction N with
  | zero =>
    intro flags i n h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [markAll, dite_eq_left hz]
    refine ⟨h.2.2, fun t _ => ⟨Or.inl, ?_⟩⟩
    rintro (h | ⟨j, h1, h2, _⟩)
    · exact h
    · omega
  | succ N ih =>
    intro flags i n h hn
    obtain ⟨h32, hmap, hs⟩ := id h
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    have hv : (map.uget i.toUSize (h.get hz)).toUInt64.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [UInt8.toNat_toUInt64, uget_toNat, hus]
    have hvLt : (map.data[i.toNat]?.getD 0).toNat < 256 := (map.data[i.toNat]?.getD 0).toNat_lt
    have hvU : (map.uget i.toUSize (h.get hz)).toUInt64.toUSize.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [word_toUSize (by omega), hv]
    rw [markAll, dite_eq_right hz]
    obtain ⟨r1, r2⟩ := ih (flags.uset (map.uget i.toUSize (h.get hz)).toUInt64.toUSize 1 (h.set _)) (i + 1) (n - 1)
      (h.next hz (size_uset' _ _ _ _)) hn1
    refine ⟨r1, fun t ht => ?_⟩
    rw [r2 t ht, hi1]
    have hflag : (flags.uset (map.uget i.toUSize (h.get hz)).toUInt64.toUSize 1 (h.set _)).data[t]?.getD 0 ≠ 0 ↔
        (flags.data[t]?.getD 0 ≠ 0 ∨ (map.data[i.toNat]?.getD 0).toNat = t) := by
      by_cases he : t = (map.data[i.toNat]?.getD 0).toNat
      · subst he
        have := uset_get_same (t := flags) (i := (map.uget i.toUSize (h.get hz)).toUInt64.toUSize) (v := 1) (h.set _)
        rw [hvU] at this
        rw [this]
        exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
      · rw [uset_get_ne (h.set _) (by rw [hvU]; exact he)]
        exact ⟨Or.inl, fun h => h.elim id (fun e => absurd e.symm he)⟩
    rw [hflag]
    constructor
    · rintro ((h | h) | ⟨j, h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨i.toNat, Nat.le_refl _, by omega, h⟩
      · exact Or.inr ⟨j, by omega, by omega, h3⟩
    · rintro (h | ⟨j, h1, h2, h3⟩)
      · exact Or.inl (Or.inl h)
      · by_cases he : j = i.toNat
        · subst he
          exact Or.inl (Or.inr h3)
        · exact Or.inr ⟨j, by omega, by omega, h3⟩

/-- What `allSeen` needs for its reads to stay in the array. -/
def AllPre (flags : ByteArray) (t n : UInt64) : Prop := t.toNat + n.toNat < 2 ^ 32 ∧ t.toNat + n.toNat ≤ flags.size

theorem AllPre.get {flags : ByteArray} {t n : UInt64} (h : AllPre flags t n) (hn : ¬ n = 0) : t.toUSize.toNat < flags.size := by
  obtain ⟨h1, h2⟩ := h
  have := (down1 hn).1
  rw [word_toUSize (by omega)]
  omega

theorem AllPre.next {flags : ByteArray} {t n : UInt64} (h : AllPre flags t n) (hn : ¬ n = 0) : AllPre flags (t + 1) (n - 1) := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hn0, hn1⟩ := down1 hn
  have hi1 := up1 (j := t) (by omega)
  exact ⟨by rw [hi1, hn1]; omega, by rw [hi1, hn1]; omega⟩

/-- Checks `n` flags from `t`. -/
def allSeen (flags : ByteArray) (t n : UInt64) (h : AllPre flags t n) : Bool :=
  if hn : n = 0 then true
  else if flags.uget t.toUSize (h.get hn) = 0 then false else allSeen flags (t + 1) (n - 1) (h.next hn)
termination_by n.toNat
decreasing_by
  have := down1 hn
  omega

theorem allSeen_iff (flags : ByteArray) : ∀ (N : Nat) (t n : UInt64) (h : AllPre flags t n), n.toNat = N →
    (allSeen flags t n h = true ↔ ∀ k, t.toNat ≤ k → k < t.toNat + N → flags.data[k]?.getD 0 ≠ 0) := by
  intro N
  induction N with
  | zero =>
    intro t n h hn
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [allSeen, dite_eq_left hz]
    exact ⟨fun _ k h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro t n h hn
    obtain ⟨h32, _⟩ := id h
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (t + 1).toNat = t.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : t.toUSize.toNat = t.toNat := word_toUSize (by omega)
    have hget : flags.uget t.toUSize (h.get hz) = flags.data[t.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [uget_toNat, hus]
    rw [allSeen, dite_eq_right hz, hget]
    by_cases hc : flags.data[t.toNat]?.getD 0 = 0
    · rw [ite_eq_left hc]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd hc (h t.toNat (Nat.le_refl _) (by omega))⟩
    · rw [ite_eq_right hc, ih (t + 1) (n - 1) (h.next hz) hn1, hi1]
      constructor
      · intro h k h1 h2
        by_cases he : k = t.toNat
        · rw [he]
          exact hc
        · exact h k (by omega) (by omega)
      · intro h k h1 h2
        exact h k (by omega) (by omega)

/-- Flags for a list's values say whether every value below `n` occurs. -/
theorem SeenIs.allSeen {flags : ByteArray} {l : List Nat} (h : SeenIs flags l) {n : UInt64} (hn : n.toNat ≤ 256)
    {ha : AllPre flags 0 n} : allSeen flags 0 n ha = true ↔ (List.range n.toNat).all l.contains = true := by
  have hz : (0 : UInt64).toNat = 0 := rfl
  rw [allSeen_iff flags n.toNat 0 n ha rfl, hz]
  simp only [List.all_eq_true, List.mem_range, List.contains_iff_mem]
  constructor
  · intro h' t ht
    exact (h.at_ t (by omega)).mp (h' t (Nat.zero_le _) (by omega))
  · intro h' t _ ht
    exact (h.at_ t (by omega)).mpr (h' t (by omega))

/-! ### A context map's values -/

/-- A run's values repeat after a round. -/
theorem imtf_rep_mod (L : List Nat) (s : Nat) (hs : s < L.length) {k : Nat} : ∀ j, j < k →
    (inverseMoveToFrontFrom L (List.replicate k s))[j]? = (inverseMoveToFrontFrom L (List.replicate k s))[j % (s + 1)]? := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro hj
    by_cases hlt : j < s + 1
    · rw [Nat.mod_eq_of_lt hlt]
    · have e := imtf_periodic L s hs (j := j - (s + 1)) (k := k) (by omega)
      rw [show j - (s + 1) + (s + 1) = j by omega] at e
      rw [e, ih (j - (s + 1)) (by omega) (by omega), Nat.mod_eq_sub_mod (show s + 1 ≤ j by omega)]

/-- A value below 256 indexes a list of flags. -/
theorem SeenIs.at_lt {sr : ByteArray} {l : List Nat} (h : SeenIs sr l) {v : UInt64} (hv : v.toNat < 256) : v.toUSize.toNat < sr.size := by
  rw [word_toUSize (by omega), h.sz]
  exact hv

theorem SeenIs.markU {sr : ByteArray} {l : List Nat} (h : SeenIs sr l) {v : UInt64} (hv : v.toNat < 256) {n : Nat} (hn : 1 ≤ n) :
    SeenIs (setU sr v.toUSize 1) (l ++ List.replicate n v.toNat) where
  sz := by rw [size_setU]; exact h.sz
  at_ t ht := by
    have hus : v.toUSize.toNat = v.toNat := word_toUSize (by omega)
    simp only [List.mem_append, List.mem_replicate]
    by_cases he : t = v.toNat
    · subst he
      have := setU_get_same (t := sr) (i := v.toUSize) (v := 1) (by rw [hus, h.sz]; exact hv)
      rw [hus] at this
      rw [this]
      exact ⟨fun _ => Or.inr ⟨by omega, rfl⟩, fun _ => by decide⟩
    · rw [setU_get_ne (by rw [hus]; exact he), h.at_ t ht]
      exact ⟨Or.inl, fun h' => h'.elim id (fun h2 => absurd h2.2 he)⟩

/-- The value read, flagged. -/
theorem SeenIs.mark {sr : ByteArray} {l : List Nat} (h : SeenIs sr l) {v : UInt64} (hv : v.toNat < 256) {n : Nat} (hn : 1 ≤ n)
    {hb : v.toUSize.toNat < sr.size} : SeenIs (sr.uset v.toUSize 1 hb) (l ++ List.replicate n v.toNat) := by
  rw [uset_setU]
  exact h.markU hv hn

/-- A run's transformed values, flagged from its first round, which has all of them. -/
theorem SeenIs.marks {sx out : ByteArray} {l : List Nat} (h : SeenIs sx l) {L : List Nat} {s : Nat} (hs : s < L.length) {k : Nat}
    {i c : UInt64} (hc : c.toNat = min k (s + 1))
    (hout : ∀ t, t < k → (inverseMoveToFrontFrom L (List.replicate k s))[t]? = some (out.data[i.toNat + t]?.getD 0).toNat)
    {hm : MarkPre out sx i c} :
    SeenIs (markAll out sx i c hm) (l ++ inverseMoveToFrontFrom L (List.replicate k s)) := by
  obtain ⟨m1, m2⟩ := markAll_spec out _ sx i c hm rfl
  refine ⟨m1, fun t ht => ?_⟩
  rw [m2 t ht, h.at_ t ht, List.mem_append]
  refine or_congr Iff.rfl ⟨fun ⟨j, h1, h2, h3⟩ => ?_, fun hm => ?_⟩
  · have e := hout (j - i.toNat) (by omega)
    rw [show i.toNat + (j - i.toNat) = j by omega, h3] at e
    exact List.mem_of_getElem? e
  · obtain ⟨j, e⟩ := List.mem_iff_getElem?.mp hm
    have hlen : (inverseMoveToFrontFrom L (List.replicate k s)).length = k := by
      rw [inverseMoveToFrontFrom_length, List.length_replicate]
    have hjk : j < k := by
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp e).1
    have hjm : j % (s + 1) < s + 1 := Nat.mod_lt _ (by omega)
    have hjl : j % (s + 1) ≤ j := Nat.mod_le _ _
    rw [imtf_rep_mod L s hs j hjk, hout _ (by omega)] at e
    exact ⟨i.toNat + j % (s + 1), by omega, by omega, (Option.some.inj e)⟩

/-- A step's values, written as read and transformed, with their flags. -/
theorem XfRel.step {xf m sr sx : ByteArray} {done : List Nat} {S : Nat} (hx : XfRel xf m sr sx done S) {idx v n c : UInt64}
    {N : Nat} (hN : n.toNat = N) (hidx : idx.toNat = done.length) (hn1 : 1 ≤ N) (hdn : done.length + N ≤ S) (hS : S < 2 ^ 31)
    (hv : v.toNat < 256) (hc : c.toNat = min N (v.toNat + 1)) {hr : RunPre m xf idx v n}
    {hm : MarkPre (imtfRun m xf idx v n hr).2 sx idx c} {hb : v.toUSize.toNat < sr.size} :
    XfRel (imtfRun m xf idx v n hr).2 (imtfRun m xf idx v n hr).1 (sr.uset v.toUSize 1 hb) (markAll (imtfRun m xf idx v n hr).2 sx idx c hm)
      (done ++ List.replicate N v.toNat) S := by
  subst hN
  have hL : (mtfAfter (List.range 256) done).length = 256 := hx.mtf.length
  obtain ⟨r1, r2, r3, r4⟩ := imtfRun_spec (i := idx) (s := v) (k := n) (out := xf) hx.mtf hv hn1 (by omega) (h := hr)
  have happ : inverseMoveToFront (done ++ List.replicate n.toNat v.toNat) =
      inverseMoveToFront done ++ inverseMoveToFrontFrom (mtfAfter (List.range 256) done) (List.replicate n.toNat v.toNat) :=
    imtf_append _ _ _
  have hlenI : (inverseMoveToFront done).length = done.length := inverseMoveToFrontFrom_length _ _
  refine ⟨by rw [r1, hx.sz], fun j hj => ?_, fun j hj => ?_, ?_, hx.seenR.mark hv hn1, ?_⟩
  · rw [happ]
    rw [List.length_append, List.length_replicate] at hj
    by_cases hA : j < done.length
    · rw [List.getElem?_append_left (by rw [hlenI]; exact hA), hx.at_ j hA, r3 j (Or.inl (by omega))]
    · rw [List.getElem?_append_right (by rw [hlenI]; omega), hlenI, r2 (j - done.length) (by omega),
        show idx.toNat + (j - done.length) = j by omega]
  · rw [List.length_append, List.length_replicate] at hj
    rw [r3 j (Or.inr (by omega))]
    exact hx.zero j (by omega)
  · rw [mtfAfter_append]
    exact r4
  · rw [happ]
    exact hx.seenX.marks (by omega) hc r2

theorem XfRel.work {xf m sr sx : ByteArray} {done : List Nat} {S : Nat} (hx : XfRel xf m sr sx done S) (hS : S ≤ 16384) :
    xf.size ≤ 16384 ∧ m.size ≤ 256 ∧ sr.size ≤ 256 ∧ sx.size ≤ 256 :=
  ⟨by rw [hx.sz]; exact hS, Nat.le_of_eq hx.mtf.sz, Nat.le_of_eq hx.seenR.sz, Nat.le_of_eq hx.seenX.sz⟩

/-- Once every value is read, the transformed values are the transform of them. -/
theorem XfRel.final {xf m sr sx : ByteArray} {done : List Nat} {S n : Nat} (hx : XfRel xf m sr sx done S) (hl : done.length = S)
    (hlt : ∀ v ∈ done, v < n) : MapOk xf (inverseMoveToFront done) S n :=
  ⟨hx.sz, by rw [inverseMoveToFront, inverseMoveToFrontFrom_length]; exact hl, fun i hi => hx.at_ i (by omega),
    inverseMoveToFront_lt hlt⟩

/-- A state at a context map's values stands for a place there. -/
theorem vals_ex {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .vals) :
    ∃ g isL ntrees rlemax code done left, HRel st g (.vals isL ntrees rlemax code done left) := by
  obtain ⟨g, p, hr⟩ := h
  cases p with
  | vals isL ntrees rlemax code done left => exact ⟨g, isL, ntrees, rlemax, code, done, left, hr⟩
  | np => exact absurd (hr.2.2.symm.trans ht) (fun e => HTag.noConfusion e)
  | _ => exact absurd (hr.2.2.1.symm.trans ht) (fun e => HTag.noConfusion e)

/-- The arrays at a context map's values. -/
def ValsSizes (st : Hd) : Prop :=
  st.mtf.size = 256 ∧ st.seenR.size = 256 ∧ st.seenX.size = 256 ∧ st.xf.size = st.fill.size ∧
    st.idx.toNat + st.left.toNat = st.fill.size ∧ st.fill.size ≤ 16384

theorem vals_sizes {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .vals) : ValsSizes st := by
  obtain ⟨g, isL, ntrees, rlemax, code, done, left, hrel⟩ := vals_ex h ht
  obtain ⟨hw, hu, _, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩ := hrel
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  exact ⟨hx.mtf.sz, hx.seenR.sz, hx.seenX.sz, by rw [hx.sz, hsz], by omega, by omega⟩

/-- A context map's value, read: below 256, in a run of at least one. -/
theorem vals_read {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .vals)
    (hok : (mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩).status = .ok) :
    (mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩).a.toNat < 256 ∧
      1 ≤ (mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩).b.toNat := by
  obtain ⟨g, isL, ntrees, rlemax, code, done, left, hrel⟩ := vals_ex h ht
  obtain ⟨hw, hu, _, hi, hn, hr, h2, h256, h16, hokT, hC, hsy, _⟩ := hrel
  have R := mapSymFast_ok (t := st.mapT.t) (base := USize.ofNat 0) (hfit := st.mapT.fits) (h32 := st.mapT.h32) (rlemax := st.rlemax)
    hw hokT hC (by omega)
  rw [hr] at R
  obtain ⟨hv, hr1, _, _⟩ := mapSym_bounds (by omega) h16 hsy ((R.ok hok).2 [])
  exact ⟨by omega, hr1⟩

/-- A context map's value read, with what a successful read gives. -/
@[inline] def mapSymFastT (st : Hd) (h : ∃ g p, HRel st g p) (ht : st.tag = .vals) :
    { r : Rd // r.status = .ok → r.a.toNat < 256 ∧ 1 ≤ r.b.toNat } :=
  ⟨mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩, vals_read h ht⟩

theorem mapSymFastT_val {st : Hd} {h : ∃ g p, HRel st g p} {ht : st.tag = .vals} :
    (mapSymFastT st h ht).1 = mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ := rfl

theorem min_run {left v : UInt64} (hv : v.toNat < 256) :
    (if left ≤ v then left else v + 1).toNat = min left.toNat (v.toNat + 1) := by
  by_cases h : left ≤ v
  · rw [ite_eq_left h]
    have := UInt64.le_iff_toNat_le.mp h
    omega
  · rw [ite_eq_right h, UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    have := Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)
    omega

section
variable {st : Hd} (hs : ValsSizes st)
include hs

theorem pre_runA {v : UInt64} (hv : v.toNat < 256) (h0 : ¬ st.left = 0) : RunPre st.mtf st.xf st.idx v st.left := by
  obtain ⟨h1, _, _, h4, h5, h6⟩ := hs
  have := (down1 h0).1
  exact ⟨h1, hv, by omega, by omega, by omega⟩

theorem pre_runB {v b : UInt64} (hv : v.toNat < 256 ∧ 1 ≤ b.toNat) (hb : ¬ st.left < b) : RunPre st.mtf st.xf st.idx v b := by
  obtain ⟨h1, _, _, h4, h5, h6⟩ := hs
  have := Nat.le_of_not_lt fun e => hb (UInt64.lt_iff_toNat_lt.mpr e)
  exact ⟨h1, hv.1, hv.2, by omega, by omega⟩

theorem pre_sr {v : UInt64} (hv : v.toNat < 256) : v.toUSize.toNat < st.seenR.size := by
  rw [word_toUSize (by omega), hs.2.1]
  exact hv

theorem pre_fillA : FillPre st.fill st.idx st.left := by
  obtain ⟨_, _, _, _, h5, h6⟩ := hs
  exact ⟨by omega, by omega⟩

theorem pre_fillB {v b : UInt64} (hv : v.toNat < 256 ∧ 1 ≤ b.toNat) (hb : ¬ st.left < b) : st.idx.toUSize.toNat < st.fill.size := by
  obtain ⟨_, _, _, _, h5, h6⟩ := hs
  have := Nat.le_of_not_lt fun e => hb (UInt64.lt_iff_toNat_lt.mpr e)
  rw [word_toUSize (by omega)]
  omega

theorem pre_markA {v : UInt64} (hv : v.toNat < 256) {q : ByteArray} (hq : q.size = st.xf.size) :
    MarkPre q st.seenX st.idx (if st.left ≤ v then st.left else v + 1) := by
  obtain ⟨_, _, h3, h4, h5, h6⟩ := hs
  have hc := min_run (left := st.left) hv
  exact ⟨by rw [hc]; omega, by rw [hc, hq]; omega, h3⟩

theorem pre_markB {v b : UInt64} (hv : v.toNat < 256 ∧ 1 ≤ b.toNat) (hb : ¬ st.left < b) {q : ByteArray} (hq : q.size = st.xf.size) :
    MarkPre q st.seenX st.idx 1 := by
  obtain ⟨_, _, h3, h4, h5, h6⟩ := hs
  have := Nat.le_of_not_lt fun e => hb (UInt64.lt_iff_toNat_lt.mpr e)
  have h1 : (1 : UInt64).toNat = 1 := rfl
  exact ⟨by rw [h1]; omega, by rw [h1, hq]; omega, h3⟩

end

/-- The place reading a context map's values. Each value is written as read and, through the transform, as it is if the
last bit asks for the transform; the value read is flagged, and so are the step's transformed values from their first
round. -/
def stepHVals (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .vals) : Hd :=
  if h0 : st.left = 0 then { st with pos := pos, status := .next, tag := .imtf }
  else
    match mapSymFastT st h ht with
    | ⟨r, hr⟩ =>
    match hs : r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      if hb : st.left < r.b then markH st pos .bad
      else
        let left := st.left
        let v := r.a
        let run := r.b
        let idx := st.idx
        let fill := st.fill
        let xf := st.xf
        let m := st.mtf
        let sr := st.seenR
        let sx := st.seenX
        let st0 := clearMap st
        if r.count = st.count then
          -- A code that gives a value without reading gives it for every value left.
          match imtfRunS m xf idx v left (pre_runA (vals_sizes h ht) (hr hs).1 h0) with
          | ⟨q, hq⟩ =>
          { st0 with
            pos := pos, status := .next, idx := idx + left, left := 0
            fill := if v = 0 then fill else fillVals fill idx left v.toUInt8 (pre_fillA (vals_sizes h ht))
            xf := q.2, mtf := q.1, seenR := sr.uset v.toUSize 1 (pre_sr (vals_sizes h ht) (hr hs).1)
            seenX := markAll q.2 sx idx (if left ≤ v then left else v + 1) (pre_markA (vals_sizes h ht) (hr hs).1 hq) }
        else if v = 0 then
          match imtfRunS m xf idx v run (pre_runB (vals_sizes h ht) (hr hs) hb) with
          | ⟨q, hq⟩ =>
          { st0 with
            word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
            fill := fill, xf := q.2, mtf := q.1, seenR := sr.uset v.toUSize 1 (pre_sr (vals_sizes h ht) (hr hs).1)
            seenX := markAll q.2 sx idx 1 (pre_markB (vals_sizes h ht) (hr hs) hb hq) }
        else
          match imtfRunS m xf idx v run (pre_runB (vals_sizes h ht) (hr hs) hb) with
          | ⟨q, hq⟩ =>
          { st0 with
            word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
            fill := fill.uset idx.toUSize v.toUInt8 (pre_fillB (vals_sizes h ht) (hr hs) hb), xf := q.2, mtf := q.1
            seenR := sr.uset v.toUSize 1 (pre_sr (vals_sizes h ht) (hr hs).1), seenX := markAll q.2 sx idx 1 (pre_markB (vals_sizes h ht) (hr hs) hb hq) }

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHVals_ok {isL : Bool} {ntrees rlemax : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.vals isL ntrees rlemax code done left)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop)
    {hH : ∃ g p, HRel st g p} {hT : st.tag = .vals} :
    HStepOk K a stop g (.vals isL ntrees rlemax code done left) st pos (stepHVals st pos hH hT) := by
  obtain ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩ := hrel
  have hrel : HRel st g (.vals isL ntrees rlemax code done left) :=
    ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  have hS := vals_sizes hH hT
  unfold stepHVals
  dsimp only
  by_cases h0 : st.left = 0
  · rw [dite_eq_left h0]
    have hl0 : left = 0 := by
      rw [← hleft, h0]
      rfl
    subst hl0
    refine HStepOk.ofNext (g' := g) (p' := .imtf isL ntrees done) rfl
      ⟨hw, hu, rfl, hi, hn, h2, h256, ⟨hsz, by omega, fun i hi' => hat i (by omega), hlt⟩, hx.final (by omega) hlt, hx.seenR, hx.seenX⟩
      (Nat.le_refl _) hp (fun F => hrest_vals_zero K g isL ntrees rlemax code done _) (fun F => hStep_vals_zero _)
  rw [dite_eq_right h0]
  have hl0 : left ≠ 0 := by
    rw [← hleft]
    exact fun e => h0 (UInt64.toNat_inj.mp e)
  have R := mapSymFast_ok (t := st.mapT.t) (base := USize.ofNat 0) (hfit := st.mapT.fits) (h32 := st.mapT.h32) (rlemax := st.rlemax) hw hok hC (by omega)
  rw [hr] at R
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.vals isL ntrees rlemax code done left)) (N := fun v b =>
    if left < v.2 then none else hrest K g (.vals isL ntrees rlemax code (done ++ List.replicate v.2 v.1) (left - v.2)) b)
    (fun bs => hrest_vals_step K g isL ntrees rlemax code done left bs hl0)
  have hval := R.ok
  have hsh0 := R.short
  have hnb : (mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩).status ≠ .bad := by
    unfold mapSymFast
    dsimp only
    split
    · split
      · exact fun e => ReadStatus.noConfusion e
      · split
        · split <;> exact fun e => ReadStatus.noConfusion e
        · exact fun e => ReadStatus.noConfusion e
    · exact fun e => ReadStatus.noConfusion e
  generalize hT' : mapSymFastT st hH hT = rr
  obtain ⟨r, hrr⟩ := rr
  have e : r = mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ := by
    rw [← mapSymFastT_val (h := hH) (ht := hT), hT']
  clear hT'
  rw [← e] at Rok Rshort Rbad hval hsh0 hnb
  dsimp only
  -- A code that gives a value without reading is the case where the read takes no bits.
  have hnone : ∀ v, runOf rlemax code = some v → r.status = .ok ∧ r.count = st.count ∧ r.a.toNat = v ∧ r.b.toNat = 1 := by
    intro v hv
    have hm := mapSym_of_run hv
    cases hsr : r.status with
    | short =>
      obtain ⟨_, _, _, h5⟩ := hsh0 hsr
      rw [hm] at h5
      cases h5
    | bad => exact absurd hsr hnb
    | ok =>
      have e := (hval hsr).2 []
      rw [List.append_nil, List.append_nil, hm] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨⟨e1, e2⟩, e3⟩ := e
      have hl := congrArg List.length e3
      rw [held_len, held_len] at hl
      exact ⟨rfl, UInt64.toNat_inj.mp hl.symm, e1.symm, e2.symm⟩
  split
  · rename_i hsr
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    have hno : runOf rlemax code = none := by
      cases e : runOf rlemax code with
      | none => rfl
      | some v => exact absurd ((hnone v e).1.symm.trans hsr) (by decide)
    exact HStepOk.ofShortRead (X := 31) hrel hfull (by omega) h3 h4
      (by rw [hStep_vals_step _ hl0 hno]; exact readIn_short h5 (by rw [held_len]; exact h3))
  · rename_i hsr
    exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  · rename_i hsr
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨hv, hr1, hv1, hrlt⟩ := mapSym_bounds (by omega) h16 hsy ((hval hsr).2 [])
    have hv256 : r.a.toNat < 256 := by omega
    by_cases hbig : st.left < r.b
    · rw [dite_eq_left hbig]
      have hbig' : left < r.b.toNat := by
        rw [← hleft]
        exact UInt64.lt_iff_toNat_lt.mp hbig
      refine HStepOk.ofBad rfl (fun F => ?_)
      rw [avail_mk, hN]
      simp only [hbig', ↓reduceIte]
    rw [dite_eq_right hbig]
    have hbig' : ¬ left < r.b.toNat := by
      rw [← hleft]
      exact fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
    by_cases hc : r.count = st.count
    · rw [ite_eq_left hc]
      -- The read took no bits: the code gives its value for every value left.
      have hro : runOf rlemax code = some r.a.toNat := by
        have e := (hval hsr).2 []
        rw [List.append_nil, List.append_nil] at e
        refine (mapSym_noRead e ?_).1
        show r.buf.held.length = _
        rw [held_len, held_len]
        exact congrArg UInt64.toNat hc
      have hidx3 : (st.idx + st.left).toNat = done.length + left := by
        rw [UInt64.toNat_add, hidx, hleft]
        exact Nat.mod_eq_of_lt (by omega)
      have hlen3 : (done ++ List.replicate left r.a.toNat).length = done.length + left := by simp
      have hz0 : (0 : UInt64).toNat = 0 := rfl
      generalize hQ : imtfRunS st.mtf st.xf st.idx r.a st.left (pre_runA hS (hrr hsr).1 h0) = QQ
      obtain ⟨q, hq⟩ := QQ
      have eq : q = imtfRun st.mtf st.xf st.idx r.a st.left (pre_runA hS (hrr hsr).1 h0) := by rw [← imtfRunS_val, hQ]
      subst eq
      dsimp only
      have hx' := hx.step (n := st.left) (v := r.a) (idx := st.idx) (c := if st.left ≤ r.a then st.left else r.a + 1)
        hleft hidx (by omega) (by omega) (by omega) hv256 (by rw [min_run hv256, hleft])
        (hr := pre_runA hS (hrr hsr).1 h0) (hm := pre_markA hS (hrr hsr).1 hq) (hb := pre_sr hS (hrr hsr).1)
      have hwork := hx'.work hmle
      by_cases hz : r.a = 0
      · have hz' : r.a.toNat = 0 := by rw [hz]; rfl
        have hfsz : (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).size = st.fill.size := by
          rw [ite_eq_left hz]
        refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate left r.a.toNat) 0)
          (hd := Or.inl (Or.inr ⟨rfl, show 0 < left by omega⟩))
          (hm := ⟨rfl, rfl, fun h => ⟨Nat.le_trans (Nat.le_of_eq hfsz) h.fill,
            h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, hwork⟩,
            ⟨rfl, by simp [budH, tableOf]⟩⟩) rfl
          ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hz0, ?_, ?_, ?_, ?_, ?_, hx'⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
        · show (st.idx + st.left).toNat = _
          rw [hidx3, hlen3]
        · rw [hlen3]
          omega
        · show (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).size = _
          rw [ite_eq_left hz]
          exact hsz
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          show _ = some ((if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).data[i]?.getD 0).toNat
          rw [ite_eq_left hz]
          by_cases hA : i < done.length
          · rw [List.getElem?_append_left hA, hat i hA]
          · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), hzero i (by omega), hz']
            rfl
        · intro i hi'
          rw [hlen3] at hi'
          show (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).data[i]?.getD 0 = 0
          rw [ite_eq_left hz]
          exact hzero i (by omega)
        · rw [hrest_vals_run K g isL ntrees rlemax code done left hro]
          rfl
        · rw [hStep_vals_run _ hl0 hro]
          rfl
      · have hz' : r.a.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp e)
        have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
          rw [UInt64.toNat_toUInt8]
          omega
        obtain ⟨hfs, hfg⟩ := fillVals_spec r.a.toUInt8 left st.fill st.idx st.left (pre_fillA hS) hleft
        have hfsz : (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).size = st.fill.size := by
          rw [ite_eq_right hz, hfs]
        refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate left r.a.toNat) 0)
          (hd := Or.inl (Or.inr ⟨rfl, show 0 < left by omega⟩))
          (hm := ⟨rfl, rfl, fun h => ⟨Nat.le_trans (Nat.le_of_eq hfsz) h.fill,
            h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, hwork⟩,
            ⟨rfl, by simp [budH, tableOf]⟩⟩) rfl
          ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hz0, ?_, ?_, ?_, ?_, ?_, hx'⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
        · show (st.idx + st.left).toNat = _
          rw [hidx3, hlen3]
        · rw [hlen3]
          omega
        · show (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).size = _
          rw [ite_eq_right hz, hfs]
          exact hsz
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          show _ = some ((if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).data[i]?.getD 0).toNat
          rw [ite_eq_right hz, hfg i, hidx]
          by_cases hA : i < done.length
          · rw [ite_eq_right (by omega), List.getElem?_append_left hA, hat i hA]
          · rw [ite_eq_left (by omega), hbyte, List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega)]
        · intro i hi'
          rw [hlen3] at hi'
          show (if r.a = 0 then st.fill else fillVals st.fill st.idx st.left r.a.toUInt8 (pre_fillA hS)).data[i]?.getD 0 = 0
          rw [ite_eq_right hz, hfg i, hidx, ite_eq_right (by omega)]
          exact hzero i (by omega)
        · rw [hrest_vals_run K g isL ntrees rlemax code done left hro]
          rfl
        · rw [hStep_vals_run _ hl0 hro]
          rfl
    rw [ite_eq_right hc]
    have hno : runOf rlemax code = none := by
      cases e : runOf rlemax code with
      | none => rfl
      | some v => exact absurd (hnone v e).2.1 hc
    have hidx2 : (st.idx + r.b).toNat = done.length + r.b.toNat := by
      rw [UInt64.toNat_add, hidx]
      exact Nat.mod_eq_of_lt (by omega)
    have hleft2 : (st.left - r.b).toNat = left - r.b.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hleft]; omega)), hleft]
    have hlen2 : (done ++ List.replicate r.b.toNat r.a.toNat).length = done.length + r.b.toNat := by simp
    have hone : (1 : UInt64).toNat = min r.b.toNat (r.a.toNat + 1) := by
      rw [show (1 : UInt64).toNat = 1 from rfl]
      omega
    by_cases hz : r.a = 0
    · rw [ite_eq_left hz]
      have hz' : r.a.toNat = 0 := by rw [hz]; rfl
      generalize hQ : imtfRunS st.mtf st.xf st.idx r.a r.b (pre_runB hS (hrr hsr) hbig) = QQ
      obtain ⟨q, hq⟩ := QQ
      have eq : q = imtfRun st.mtf st.xf st.idx r.a r.b (pre_runB hS (hrr hsr) hbig) := by rw [← imtfRunS_val, hQ]
      subst eq
      dsimp only
      have hx' := hx.step (n := r.b) (v := r.a) (idx := st.idx) (c := 1) rfl hidx hr1 (by omega) (by omega) hv256 hone
        (hr := pre_runB hS (hrr hsr) hbig) (hm := pre_markB hS (hrr hsr) hbig hq) (hb := pre_sr hS (hrr hsr).1)
      have hwork := hx'.work hmle
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat))
        (hd := Or.inl (Or.inr ⟨rfl, show left - r.b.toNat < left by omega⟩))
        (hm := ⟨rfl, rfl, fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase,
            hwork⟩,
          ⟨rfl, by simp [budH, tableOf]⟩⟩) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, hsz, ?_, ?_, ?_, hx'⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
      · show (st.idx + r.b).toNat = _
        rw [hidx2, hlen2]
      · rw [hlen2]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hlt x h
        · rw [(List.mem_replicate.mp h).2]
          exact hv
      · intro i hi'
        rw [hlen2] at hi'
        by_cases hA : i < done.length
        · rw [List.getElem?_append_left hA, hat i hA]
        · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), hzero i (by omega), hz']
          rfl
      · intro i hi'
        rw [hlen2] at hi'
        exact hzero i (by omega)
      · rw [avail_mk, hN]
        simp only [hbig', ↓reduceIte]
        rfl
      · rw [avail_mk, hStep_vals_step _ hl0 hno, readIn_some ((hval hsr).2 _)]
        simp only [hbig', ↓reduceIte]
        rfl
    · rw [ite_eq_right hz]
      have hz' : r.a.toNat ≠ 0 := fun e => hz (UInt64.toNat_inj.mp e)
      have hrun1 := hv1 hz'
      have hus : st.idx.toUSize.toNat = done.length := by rw [word_toUSize (by omega), hidx]
      have hbyte : r.a.toUInt8.toNat = r.a.toNat := by
        rw [UInt64.toNat_toUInt8]
        omega
      generalize hQ : imtfRunS st.mtf st.xf st.idx r.a r.b (pre_runB hS (hrr hsr) hbig) = QQ
      obtain ⟨q, hq⟩ := QQ
      have eq : q = imtfRun st.mtf st.xf st.idx r.a r.b (pre_runB hS (hrr hsr) hbig) := by rw [← imtfRunS_val, hQ]
      subst eq
      dsimp only
      have hx' := hx.step (n := r.b) (v := r.a) (idx := st.idx) (c := 1) rfl hidx hr1 (by omega) (by omega) hv256 hone
        (hr := pre_runB hS (hrr hsr) hbig) (hm := pre_markB hS (hrr hsr) hbig hq) (hb := pre_sr hS (hrr hsr).1)
      have hwork := hx'.work hmle
      have hfb := pre_fillB hS (hrr hsr) hbig
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat))
        (hd := Or.inl (Or.inr ⟨rfl, show left - r.b.toNat < left by omega⟩))
        (hm := ⟨rfl, rfl, fun h => ⟨by show (st.fill.uset st.idx.toUSize r.a.toUInt8 hfb).size ≤ _; rw [size_uset']; exact h.fill,
          h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, hwork⟩,
          ⟨rfl, by simp [budH, tableOf]⟩⟩) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, ?_, ?_, ?_, ?_, hx'⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
      · show (st.idx + r.b).toNat = _
        rw [hidx2, hlen2]
      · rw [hlen2]
        omega
      · show (st.fill.uset st.idx.toUSize r.a.toUInt8 hfb).size = _
        rw [size_uset']
        exact hsz
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hlt x h
        · rw [(List.mem_replicate.mp h).2]
          exact hv
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show _ = some ((st.fill.uset st.idx.toUSize r.a.toUInt8 hfb).data[i]?.getD 0).toNat
        by_cases hA : i < done.length
        · rw [List.getElem?_append_left hA, hat i hA, uset_get_ne hfb (by rw [hus]; omega)]
        · have he : i = done.length := by omega
          subst he
          have := uset_get_same (t := st.fill) (i := st.idx.toUSize) (v := r.a.toUInt8) hfb
          rw [hus] at this
          rw [this, hbyte, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_replicate, ite_eq_left (by omega)]
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show (st.fill.uset st.idx.toUSize r.a.toUInt8 hfb).data[i]?.getD 0 = 0
        rw [uset_get_ne hfb (by rw [hus]; omega)]
        exact hzero i (by omega)
      · rw [avail_mk, hN]
        simp only [hbig', ↓reduceIte]
        rfl
      · rw [avail_mk, hStep_vals_step _ hl0 hno, readIn_some ((hval hsr).2 _)]
        simp only [hbig', ↓reduceIte]
        rfl

end

/-! ### A context map's last bit -/

/-- A state at a context map's last bit has a flag for every tree. -/
theorem imtf_all {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .imtf) :
    AllPre st.seenR 0 st.ntrees ∧ AllPre st.seenX 0 st.ntrees := by
  obtain ⟨g, p, hr⟩ := h
  cases p with
  | imtf isL ntrees vals =>
    obtain ⟨_, _, _, _, hn, _, h256, _, _, hsR, hsX⟩ := hr
    have hz : (0 : UInt64).toNat = 0 := rfl
    exact ⟨⟨by rw [hz]; omega, by rw [hz, hsR.sz]; omega⟩, ⟨by rw [hz]; omega, by rw [hz, hsX.sz]; omega⟩⟩
  | np => exact absurd (hr.2.2.symm.trans ht) (fun e => HTag.noConfusion e)
  | _ => exact absurd (hr.2.2.1.symm.trans ht) (fun e => HTag.noConfusion e)

/-- The place at a context map's last bit: it chooses the values as read or as transformed, and checks that every tree
occurs from their flags. -/
def stepHImtf (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .imtf) : Hd :=
  if 1 ≤ st.count then
    let b : BitBuffer := ⟨st.word, st.count⟩
    let b1 := b.drop 1
    let n := st.ntrees
    let fill := st.fill
    let xf := st.xf
    let sr := st.seenR
    let sx := st.seenX
    let st0 := clearMap st
    if b.peek 1 = 0 then
      if allSeen sr 0 n (imtf_all h ht).1 then
        mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n fill
      else { st0 with pos := pos, status := .bad }
    else
      if allSeen sx 0 n (imtf_all h ht).2 then
        mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n xf
      else { st0 with pos := pos, status := .bad }
  else markH st pos .needsInput

private theorem not_le_lt3 {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHImtf_ok {isL : Bool} {ntrees : Nat} {vals : List Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.imtf isL ntrees vals)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop)
    {hH : ∃ g p, HRel st g p} {hT : st.tag = .imtf} :
    HStepOk K a stop g (.imtf isL ntrees vals) st pos (stepHImtf st pos hH hT) := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩ := hrel
  have hrel : HRel st g (.imtf isL ntrees vals) := ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  unfold stepHImtf
  dsimp only
  by_cases h1 : 1 ≤ st.count
  · rw [ite_eq_left h1]
    have hread := fun f => read_int (b := ⟨st.word, st.count⟩) (k := 1) f (by decide) h1
    have hw1 := drop_wf' hw (k := 1) (by decide) h1
    generalize (BitBuffer.mk st.word st.count).drop 1 = b1 at hread hw1
    generalize hpk : (BitBuffer.mk st.word st.count).peek 1 = im at hread
    have hspec : ∀ f, hrest K g (.imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
        if (List.range ntrees).all (if im.toNat = 0 then vals else inverseMoveToFront vals).contains then
          afterMap K g isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals) (b1.held ++ f)
        else none := by
      intro f
      show (readInt 1 _ >>= _) = _
      rw [show readInt 1 ((BitBuffer.mk st.word st.count).held ++ f) = _ from hread f]
      rfl
    have hjspec : ∀ f, hStepP (g, .imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
        if (List.range ntrees).all (if im.toNat = 0 then vals else inverseMoveToFront vals).contains then
          .next (g.setMap isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals),
            mapNextPhase (g.setMap isL ntrees (if im.toNat = 0 then vals else inverseMoveToFront vals)) isL) (b1.held ++ f)
        else .bad := by
      intro f
      show readIn 1 (readInt 1) _ _ = _
      rw [readIn_some (show readInt 1 ((BitBuffer.mk st.word st.count).held ++ f) = _ from hread f)]
    obtain ⟨hmR, hmX, hsR, hsX⟩ := hm
    -- Either way: the values chosen, their flags, and the spec's reading with them.
    have key : ∀ (final seen : ByteArray) (cmap : List Nat) (hA : AllPre seen 0 st.ntrees), MapOk final cmap (mapSize g isL) ntrees →
        SeenIs seen cmap →
        (∀ f, hrest K g (.imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
          if (List.range ntrees).all cmap.contains then afterMap K g isL ntrees cmap (b1.held ++ f) else none) →
        (∀ f, hStepP (g, .imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
          if (List.range ntrees).all cmap.contains then
            .next (g.setMap isL ntrees cmap, mapNextPhase (g.setMap isL ntrees cmap) isL) (b1.held ++ f) else .bad) →
        HStepOk K a stop g (.imtf isL ntrees vals) st pos
          (if allSeen seen 0 st.ntrees hA = true then
            mapFinish { clearMap st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final
          else { clearMap st with pos := pos, status := .bad }) := by
      intro final seen cmap hA hfinal hseen hs hj
      have hocc := hseen.allSeen (n := st.ntrees) (by omega) (ha := hA)
      rw [hn] at hocc
      by_cases hc : allSeen seen 0 st.ntrees hA = true
      · rw [ite_eq_left hc]
        exact mapFinish_ok (st0 := st) (st := { clearMap st with word := b1.word, count := b1.count, pos := pos, status := .next })
          (p := .imtf isL ntrees vals) (cmap := cmap) (ntrees := ntrees) (n := st.ntrees) (map := final) hw1 hi hu hfinal hn (by omega) h256
          rfl hp ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
          (fun _ => ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩) rfl
          (by show mapIdx isL ≤ 6; unfold mapIdx; split <;> omega) (imtfNext_down _ _ _ _)
          (fun F => by rw [avail_mk, hs, ite_eq_left (hocc.mp hc)]; rfl)
          (fun F => by rw [avail_mk, hj, ite_eq_left (hocc.mp hc)]; rfl)
      · rw [ite_eq_right hc]
        have hc' : ¬ (List.range ntrees).all cmap.contains = true := fun e => hc (hocc.mpr e)
        refine HStepOk.ofBad rfl (fun F => ?_)
        rw [avail_mk, hs, ite_eq_right hc']
    by_cases hz : im = 0
    · rw [ite_eq_left hz]
      have hz' : im.toNat = 0 := by rw [hz]; rfl
      simp only [hz', ↓reduceIte] at hspec hjspec
      exact key st.fill st.seenR vals (imtf_all hH hT).1 hmR hsR hspec hjspec
    · rw [ite_eq_right hz]
      have hz' : ¬ im.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
      simp only [hz', ↓reduceIte] at hspec hjspec
      exact key st.xf st.seenX (inverseMoveToFront vals) (imtf_all hH hT).2 hmX hsX hspec hjspec
  · rw [ite_eq_right h1]
    have hc : st.count.toNat < 1 := not_le_lt3 h1
    have hnone : hrest K g (.imtf isL ntrees vals) (BitBuffer.mk st.word st.count).held = none := by
      show (readInt 1 _ >>= _) = none
      rw [readInt_short (b := ⟨st.word, st.count⟩) hc]
      rfl
    exact HStepOk.ofShortRead (X := 1) hrel hfull (by omega) hc hnone
      (by show readIn 1 (readInt 1) _ _ = _; exact readIn_short (readInt_short (b := ⟨st.word, st.count⟩) hc) (by rw [held_len]; exact hc))

end

end Brotli.Decoder
