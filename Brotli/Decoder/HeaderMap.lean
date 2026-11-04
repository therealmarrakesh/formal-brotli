import Brotli.Decoder.HeaderSyms

/-!
# A context map's values

The place reading a context map's values, and the place at its last bit, with the inverse move-to-front transform and the
check that every tree occurs.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

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

/-- A run's first round of values: the `n` outputs from `j`, each the list's value `j` places before `s`. -/
def revOut (m out : ByteArray) (i s j n : UInt64) : ByteArray :=
  if _hn : n = 0 then out else revOut m (setU out (i + j).toUSize (getU m (s - j).toUSize)) i s (j + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem revOut_spec (m : ByteArray) (i s : UInt64) : ∀ (N : Nat) (j n : UInt64) (out : ByteArray), n.toNat = N →
    j.toNat + N ≤ s.toNat + 1 → s.toNat < 256 → i.toNat + j.toNat + N < 2 ^ 32 → i.toNat + j.toNat + N ≤ out.size →
    (revOut m out i s j n).size = out.size ∧ (∀ q, q < i.toNat + j.toNat → (revOut m out i s j n).data[q]? = out.data[q]?) ∧
    (∀ q, i.toNat + j.toNat + N ≤ q → (revOut m out i s j n).data[q]? = out.data[q]?) ∧
    (∀ t, j.toNat ≤ t → t < j.toNat + N → (revOut m out i s j n).data[i.toNat + t]?.getD 0 = m.data[s.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro j n out hn _ _ _ _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [revOut, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun t h1 h2 => absurd h2 (by omega)⟩
  | succ N ih =>
    intro j n out hn hjs hs h32 hsz
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
    generalize hv : getU m (s - j).toUSize = v
    have hvb : v = m.data[s.toNat - j.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, hsj]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (n - 1) (setU out (i + j).toUSize v) hn1 (by omega) hs (by omega)
      (by rw [size_setU]; omega)
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_setU], fun q hq => ?_, fun q hq => ?_, fun t h1 h2 => ?_⟩
    · rw [b2 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · rw [b3 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases ht : t = j.toNat
      · subst ht
        rw [b2 _ (by omega)]
        have := setU_get_same (t := out) (i := (i + j).toUSize) (v := v) (by rw [hus]; omega)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 t (by omega) (by omega)

/-- Rewrites `n` places of the list from `x`, each from the outputs, going back from `a`. -/
def rotFrom (out m : ByteArray) (i x a n : UInt64) : ByteArray :=
  if _hn : n = 0 then m else rotFrom out (setU m x.toUSize (getU out (i + a).toUSize)) i (x + 1) (a - 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem rotFrom_spec (out : ByteArray) (i : UInt64) : ∀ (N : Nat) (x a n : UInt64) (m : ByteArray), n.toNat = N →
    (0 < N → N ≤ a.toNat + 1 ∧ i.toNat + a.toNat < 2 ^ 32) → x.toNat + N ≤ 256 → m.size = 256 →
    (rotFrom out m i x a n).size = 256 ∧ (∀ y, y < x.toNat ∨ x.toNat + N ≤ y → (rotFrom out m i x a n).data[y]? = m.data[y]?) ∧
    (∀ t, t < N → (rotFrom out m i x a n).data[x.toNat + t]?.getD 0 = out.data[i.toNat + a.toNat - t]?.getD 0) := by
  intro N
  induction N with
  | zero =>
    intro x a n m hn _ _ hs
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [rotFrom, dite_eq_left hz]
    exact ⟨hs, fun _ _ => rfl, fun t h => absurd h (by omega)⟩
  | succ N ih =>
    intro x a n m hn ha hx hs
    obtain ⟨ha1, ha2⟩ := ha (by omega)
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
    generalize hv : getU out (i + a).toUSize = v
    have hvb : v = out.data[i.toNat + a.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, husa]
    obtain ⟨b1, b2, b3⟩ := ih (x + 1) (a - 1) (n - 1) (setU m x.toUSize v) hn1
      (fun h => by
        have ha1' : (a - 1).toNat = a.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
        rw [ha1']
        omega)
      (by rw [hx1]; omega) (by rw [size_setU]; exact hs)
    rw [hx1] at b2 b3
    refine ⟨b1, fun y hy => ?_, fun t ht => ?_⟩
    · rw [b2 y (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases ht0 : t = 0
      · subst ht0
        rw [Nat.add_zero, b2 _ (by omega)]
        have := setU_get_same (t := m) (i := x.toUSize) (v := v) (by rw [hus, hs]; omega)
        rw [hus] at this
        rw [this, hvb, Nat.sub_zero]
      · have ha1' : (a - 1).toNat = a.toNat - 1 :=
          UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
        have := b3 (t - 1) (by omega)
        rw [ha1', show x.toNat + 1 + (t - 1) = x.toNat + t by omega, show i.toNat + (a.toNat - 1) - (t - 1) = i.toNat + a.toNat - t by omega]
          at this
        exact this

/-- Copies `k` bytes from `p` places back, one at a time, so that from `j` on the bytes repeat with period `p`. -/
def copyPeriod (out : ByteArray) (j k p : UInt64) : ByteArray :=
  if _hk : k = 0 then out else copyPeriod (setU out j.toUSize (getU out (j - p).toUSize)) (j + 1) (k - 1) p
termination_by k.toNat
decreasing_by
  have hne : k.toNat ≠ 0 := fun e => _hk (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (k - 1).toNat = k.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem copyPeriod_spec (p : UInt64) (hp : 1 ≤ p.toNat) : ∀ (K : Nat) (j k : UInt64) (out : ByteArray), k.toNat = K → p.toNat ≤ j.toNat →
    j.toNat + K < 2 ^ 32 → j.toNat + K ≤ out.size →
    (copyPeriod out j k p).size = out.size ∧ (∀ q, q < j.toNat → (copyPeriod out j k p).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat + K ≤ q → (copyPeriod out j k p).data[q]? = out.data[q]?) ∧
    (∀ q, j.toNat ≤ q → q < j.toNat + K → (copyPeriod out j k p).data[q]?.getD 0 = (copyPeriod out j k p).data[q - p.toNat]?.getD 0) := by
  intro K
  induction K with
  | zero =>
    intro j k out hk _ _ _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [copyPeriod, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun q h1 h2 => absurd h2 (by omega)⟩
  | succ K ih =>
    intro j k out hk hpj h32 hs
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
    generalize hv : getU out (j - p).toUSize = v
    have hvb : v = out.data[j.toNat - p.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, husp]
    obtain ⟨b1, b2, b3, b4⟩ := ih (j + 1) (k - 1) (setU out j.toUSize v) hk1 (by omega) (by omega) (by rw [size_setU]; omega)
    rw [hj1] at b2 b3 b4
    refine ⟨by rw [b1, size_setU], fun q hq => ?_, fun q hq => ?_, fun q h1 h2 => ?_⟩
    · rw [b2 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · rw [b3 q (by omega), setU_get_ne (by rw [hus]; omega)]
    · by_cases hq : q = j.toNat
      · subst hq
        rw [b2 _ (by omega), b2 _ (by omega), setU_get_ne (show j.toNat - p.toNat ≠ j.toUSize.toNat by rw [hus]; omega)]
        have := setU_get_same (t := out) (i := j.toUSize) (v := v) (by rw [hus]; omega)
        rw [hus] at this
        rw [this, hvb]
      · exact b4 q (by omega) (by omega)

/-- Moves `n` places of the list up `k` places, from place `x` down: each takes the value `k` places before it. -/
def shiftBy (m : ByteArray) (x k n : UInt64) : ByteArray :=
  if _hn : n = 0 then m else shiftBy (setU m x.toUSize (getU m (x - k).toUSize)) (x - 1) k (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem shiftBy_spec (k : UInt64) : ∀ (N : Nat) (m : ByteArray) (x n : UInt64), n.toNat = N →
    (0 < N → k.toNat + N ≤ x.toNat + 1 ∧ x.toNat < 256) → 1 ≤ k.toNat → m.size = 256 →
    (shiftBy m x k n).size = 256 ∧ ∀ y, y < 256 → (shiftBy m x k n).data[y]?.getD 0 =
      if x.toNat + 1 - N ≤ y ∧ y ≤ x.toNat then m.data[y - k.toNat]?.getD 0 else m.data[y]?.getD 0 := by
  intro N
  induction N with
  | zero =>
    intro m x n hn _ _ hs
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [shiftBy, dite_eq_left hz]
    exact ⟨hs, fun y _ => by rw [ite_eq_right (by omega)]⟩
  | succ N ih =>
    intro m x n hn hx hk hs
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
    generalize hv : getU m (x - k).toUSize = v
    have hvb : v = m.data[x.toNat - k.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [← hv, getU_toNat, husk]
    have hs1 : (setU m x.toUSize v).size = 256 := by rw [size_setU]; exact hs
    obtain ⟨i1, i2⟩ := ih (setU m x.toUSize v) (x - 1) (n - 1) hn1 (fun h => by rw [hX h]; omega) hk hs1
    refine ⟨i1, fun y hy => ?_⟩
    rw [i2 y hy]
    by_cases hyx : y = x.toNat
    · subst hyx
      have hc : ¬ ((x - 1).toNat + 1 - N ≤ x.toNat ∧ x.toNat ≤ (x - 1).toNat) := by
        by_cases hN : 0 < N
        · rw [hX hN]; omega
        · omega
      rw [ite_eq_right hc, ite_eq_left (by omega)]
      have := setU_get_same (t := m) (i := x.toUSize) (v := v) (by rw [hus, hs]; omega)
      rw [hus] at this
      rw [this, hvb]
    · by_cases hin : x.toNat + 1 - (N + 1) ≤ y ∧ y ≤ x.toNat
      · have hN : 0 < N := by omega
        have hc : (x - 1).toNat + 1 - N ≤ y ∧ y ≤ (x - 1).toNat := by rw [hX hN]; omega
        rw [ite_eq_left hc, ite_eq_left hin, setU_get_ne (by rw [hus]; omega)]
      · have hc : ¬ ((x - 1).toNat + 1 - N ≤ y ∧ y ≤ (x - 1).toNat) := by
          by_cases hN : 0 < N
          · rw [hX hN]; omega
          · omega
        rw [ite_eq_right hc, ite_eq_right hin, setU_get_ne (by rw [hus]; exact hyx)]

/-- The transform of a run of `k` copies of index `s`, from the list `m`, into `out` from `i`. The values of a round are
the list's first places backwards, and after a whole round they repeat; the list's first `s + 1` places turn round, those
the run took from the values and the rest moved up. -/
def imtfRun (m out : ByteArray) (i s k : UInt64) : ByteArray × ByteArray :=
  if k ≤ s then
    let out1 := revOut m out i s 0 k
    (rotFrom out1 (shiftBy m s k (s + 1 - k)) i 0 (k - 1) k, out1)
  else
    let p := s + 1
    let out1 := copyPeriod (revOut m out i s 0 p) (i + p) (k - p) p
    let K := (k - p) % p
    (rotFrom out1 (rotFrom out1 m i 0 (K - 1) K) i K s (p - K), out1)

/-- What a run does: the transform of its indices, from `i` in the outputs, with the rest of them as they were, and the list
after them. -/
theorem imtfRun_spec {m out : ByteArray} {i s k : UInt64} {L : List Nat} (hm : MtfIs m L) (hs : s.toNat < 256) (hk : 1 ≤ k.toNat)
    (h32 : i.toNat + k.toNat < 2 ^ 32) (hsz : i.toNat + k.toNat ≤ out.size) :
    (imtfRun m out i s k).2.size = out.size ∧
    (∀ t, t < k.toNat → (inverseMoveToFrontFrom L (List.replicate k.toNat s.toNat))[t]? =
      some ((imtfRun m out i s k).2.data[i.toNat + t]?.getD 0).toNat) ∧
    (∀ q, q < i.toNat ∨ i.toNat + k.toNat ≤ q → (imtfRun m out i s k).2.data[q]? = out.data[q]?) ∧
    MtfIs (imtfRun m out i s k).1 (mtfAfter L (List.replicate k.toNat s.toNat)) := by
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
  · rw [ite_eq_left hks]
    dsimp only
    have hks' : k.toNat ≤ s.toNat := UInt64.le_iff_toNat_le.mp hks
    obtain ⟨o1, o2, o3, o4⟩ := revOut_spec m i s k.toNat 0 k out rfl (by rw [hz0]; omega) hs (by rw [hz0]; omega)
      (by rw [hz0]; omega)
    rw [hz0, Nat.add_zero] at o2 o3
    rw [hz0] at o4
    generalize revOut m out i s 0 k = out1 at o1 o2 o3 o4 ⊢
    have hsk : (s + 1 - k).toNat = s.toNat + 1 - k.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨b1, b2⟩ := shiftBy_spec k (s.toNat + 1 - k.toNat) m s (s + 1 - k) hsk (fun _ => ⟨by omega, hs⟩) hk hm.sz
    have hk1 : (k - 1).toNat = k.toNat - 1 :=
      UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega))
    obtain ⟨c1, c2, c3⟩ := rotFrom_spec out1 i k.toNat 0 (k - 1) k (shiftBy m s k (s + 1 - k)) rfl
      (fun _ => ⟨by rw [hk1]; omega, by rw [hk1]; omega⟩) (by rw [hz0]; omega) b1
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
  · rw [ite_eq_right hks]
    dsimp only
    have hrp : s.toNat < k.toNat := Nat.lt_of_not_le fun e => hks (UInt64.le_iff_toNat_le.mpr e)
    obtain ⟨o1, o2, o3, o4⟩ := revOut_spec m i s (s.toNat + 1) 0 (s + 1) out hp1 (by rw [hz0]; omega) hs
      (by rw [hz0]; omega) (by rw [hz0]; omega)
    rw [hz0, Nat.add_zero] at o2 o3
    rw [hz0] at o4
    generalize revOut m out i s 0 (s + 1) = out1 at o1 o2 o3 o4 ⊢
    have hip : (i + (s + 1)).toNat = i.toNat + (s.toNat + 1) := by
      rw [UInt64.toNat_add, hp1]
      exact Nat.mod_eq_of_lt (by omega)
    have hrs : (k - (s + 1)).toNat = k.toNat - (s.toNat + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨q1, q2, q3, q4⟩ := copyPeriod_spec (s + 1) (by rw [hp1]; omega) (k.toNat - (s.toNat + 1))
      (i + (s + 1)) (k - (s + 1)) out1 hrs (by rw [hip, hp1]; omega) (by rw [hip]; omega) (by rw [hip, o1]; omega)
    rw [hip] at q2 q3 q4
    rw [hp1] at q4
    generalize copyPeriod out1 (i + (s + 1)) (k - (s + 1)) (s + 1) = out2 at q1 q2 q3 q4 ⊢
    -- The round's values, in the outputs, are the list's first places backwards.
    have hfirst : ∀ t, t ≤ s.toNat → (out2.data[i.toNat + t]?.getD 0).toNat = L.getD (s.toNat - t) 0 := by
      intro t ht
      rw [q2 _ (by omega), o4 t (Nat.zero_le _) (by omega), hm.at_ _ (by omega)]
    -- The list after the run: its first places turned round as far as the run goes past whole rounds.
    have hK : (k.toNat - (s.toNat + 1)) % (s.toNat + 1) < s.toNat + 1 := Nat.mod_lt _ (by omega)
    generalize hKd : (k.toNat - (s.toNat + 1)) % (s.toNat + 1) = K at hK
    have hkK : ((k - (s + 1)) % (s + 1)).toNat = K := by rw [UInt64.toNat_mod, hrs, hp1, hKd]
    generalize (k - (s + 1)) % (s + 1) = kk at hkK ⊢
    obtain ⟨a1, a2, a3⟩ := rotFrom_spec out2 i K 0 (kk - 1) kk m hkK
      (fun h => by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hkK, show (1 : UInt64).toNat = 1 from rfl]; omega)), hkK,
          show (1 : UInt64).toNat = 1 from rfl]
        omega)
      (by rw [hz0]; omega) hm.sz
    have hpk : (s + 1 - kk).toNat = s.toNat + 1 - K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hkK, hp1]; omega)), hkK, hp1]
    obtain ⟨c1, c2, c3⟩ := rotFrom_spec out2 i (s.toNat + 1 - K) kk s (s + 1 - kk)
      (rotFrom out2 m i 0 (kk - 1) kk) hpk (fun _ => by omega) (by rw [hkK]; omega) a1
    rw [hz0] at a2 a3
    rw [hkK] at c2 c3
    have hms : MtfIs (rotFrom out2 (rotFrom out2 m i 0 (kk - 1) kk) i kk s (s + 1 - kk))
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
        have hk1 : (kk - 1).toNat = K - 1 := by
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

/-- Marks the values of `n` bytes from `i`. -/
def markAll (map flags : ByteArray) (i n : UInt64) : ByteArray :=
  if _hn : n = 0 then flags else markAll map (setU flags (getU map i.toUSize).toUInt64.toUSize 1) (i + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem markAll_spec (map : ByteArray) : ∀ (N : Nat) (flags : ByteArray) (i n : UInt64), n.toNat = N → i.toNat + N < 2 ^ 32 → flags.size = 256 →
    (markAll map flags i n).size = 256 ∧ ∀ t, t < 256 → ((markAll map flags i n).data[t]?.getD 0 ≠ 0 ↔
      (flags.data[t]?.getD 0 ≠ 0 ∨ ∃ j, i.toNat ≤ j ∧ j < i.toNat + N ∧ (map.data[j]?.getD 0).toNat = t)) := by
  intro N
  induction N with
  | zero =>
    intro flags i n hn _ hs
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [markAll, dite_eq_left hz]
    refine ⟨hs, fun t _ => ⟨Or.inl, ?_⟩⟩
    rintro (h | ⟨j, h1, h2, _⟩)
    · exact h
    · omega
  | succ N ih =>
    intro flags i n hn h32 hs
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    have hv : (getU map i.toUSize).toUInt64.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [UInt8.toNat_toUInt64, getU_toNat, hus]
    have hvLt : (map.data[i.toNat]?.getD 0).toNat < 256 := (map.data[i.toNat]?.getD 0).toNat_lt
    have hvU : (getU map i.toUSize).toUInt64.toUSize.toNat = (map.data[i.toNat]?.getD 0).toNat := by
      rw [word_toUSize (by omega), hv]
    rw [markAll, dite_eq_right hz]
    generalize hf : setU flags (getU map i.toUSize).toUInt64.toUSize 1 = flags1
    have hs1 : flags1.size = 256 := by rw [← hf, size_setU]; exact hs
    obtain ⟨r1, r2⟩ := ih flags1 (i + 1) (n - 1) hn1 (by rw [hi1]; omega) hs1
    refine ⟨r1, fun t ht => ?_⟩
    rw [r2 t ht, hi1]
    have hflag : flags1.data[t]?.getD 0 ≠ 0 ↔ (flags.data[t]?.getD 0 ≠ 0 ∨ (map.data[i.toNat]?.getD 0).toNat = t) := by
      by_cases he : t = (map.data[i.toNat]?.getD 0).toNat
      · subst he
        have := setU_get_same (t := flags) (i := (getU map i.toUSize).toUInt64.toUSize) (v := 1) (by rw [hvU, hs]; exact hvLt)
        rw [hvU] at this
        rw [← hf, this]
        exact ⟨fun _ => Or.inr rfl, fun _ => by decide⟩
      · rw [← hf, setU_get_ne (by rw [hvU]; exact he)]
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

/-- Checks `n` flags from `t`. -/
def allMarked (flags : ByteArray) (t n : UInt64) : Bool :=
  if _hn : n = 0 then true
  else if getU flags t.toUSize = 0 then false else allMarked flags (t + 1) (n - 1)
termination_by n.toNat
decreasing_by
  have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
    rw [show (1 : UInt64).toNat = 1 from rfl]
    omega))
  omega

theorem allMarked_iff (flags : ByteArray) : ∀ (N : Nat) (t n : UInt64), n.toNat = N → t.toNat + N < 2 ^ 32 →
    (allMarked flags t n = true ↔ ∀ k, t.toNat ≤ k → k < t.toNat + N → flags.data[k]?.getD 0 ≠ 0) := by
  intro N
  induction N with
  | zero =>
    intro t n hn _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [allMarked, dite_eq_left hz]
    exact ⟨fun _ k h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ N ih =>
    intro t n hn h32
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (t + 1).toNat = t.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : t.toUSize.toNat = t.toNat := word_toUSize (by omega)
    have hget : getU flags t.toUSize = flags.data[t.toNat]?.getD 0 := by
      apply UInt8.toNat_inj.mp
      rw [getU_toNat, hus]
    rw [allMarked, dite_eq_right hz, hget]
    by_cases hc : flags.data[t.toNat]?.getD 0 = 0
    · rw [ite_eq_left hc]
      exact ⟨fun h => Bool.noConfusion h, fun h => absurd hc (h t.toNat (Nat.le_refl _) (by omega))⟩
    · rw [ite_eq_right hc, ih (t + 1) (n - 1) hn1 (by rw [hi1]; omega), hi1]
      constructor
      · intro h k h1 h2
        by_cases he : k = t.toNat
        · rw [he]
          exact hc
        · exact h k (by omega) (by omega)
      · intro h k h1 h2
        exact h k (by omega) (by omega)

/-- Flags for a list's values say whether every value below `n` occurs. -/
theorem SeenIs.allMarked {flags : ByteArray} {l : List Nat} (h : SeenIs flags l) {n : UInt64} (hn : n.toNat ≤ 256) :
    allMarked flags 0 n = true ↔ (List.range n.toNat).all l.contains = true := by
  have hz : (0 : UInt64).toNat = 0 := rfl
  rw [allMarked_iff flags n.toNat 0 n rfl (by rw [hz]; omega), hz]
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

/-- The value read, flagged. -/
theorem SeenIs.mark {sr : ByteArray} {l : List Nat} (h : SeenIs sr l) {v : UInt64} (hv : v.toNat < 256) {n : Nat} (hn : 1 ≤ n) :
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

/-- A run's transformed values, flagged from its first round, which has all of them. -/
theorem SeenIs.marks {sx out : ByteArray} {l : List Nat} (h : SeenIs sx l) {L : List Nat} {s : Nat} (hs : s < L.length) {k : Nat}
    {i c : UInt64} (hc : c.toNat = min k (s + 1)) (h32 : i.toNat + c.toNat < 2 ^ 32)
    (hout : ∀ t, t < k → (inverseMoveToFrontFrom L (List.replicate k s))[t]? = some (out.data[i.toNat + t]?.getD 0).toNat) :
    SeenIs (markAll out sx i c) (l ++ inverseMoveToFrontFrom L (List.replicate k s)) := by
  obtain ⟨m1, m2⟩ := markAll_spec out _ sx i c rfl h32 h.sz
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
    (hv : v.toNat < 256) (hc : c.toNat = min N (v.toNat + 1)) :
    XfRel (imtfRun m xf idx v n).2 (imtfRun m xf idx v n).1 (setU sr v.toUSize 1) (markAll (imtfRun m xf idx v n).2 sx idx c)
      (done ++ List.replicate N v.toNat) S := by
  subst hN
  have hL : (mtfAfter (List.range 256) done).length = 256 := hx.mtf.length
  obtain ⟨r1, r2, r3, r4⟩ := imtfRun_spec (i := idx) (s := v) (k := n) (out := xf) hx.mtf hv hn1 (by omega) (by rw [hx.sz]; omega)
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
    exact hx.seenX.marks (by omega) hc (by omega) r2

theorem XfRel.work {xf m sr sx : ByteArray} {done : List Nat} {S : Nat} (hx : XfRel xf m sr sx done S) (hS : S ≤ 16384) :
    xf.size ≤ 16384 ∧ m.size ≤ 256 ∧ sr.size ≤ 256 ∧ sx.size ≤ 256 :=
  ⟨by rw [hx.sz]; exact hS, Nat.le_of_eq hx.mtf.sz, Nat.le_of_eq hx.seenR.sz, Nat.le_of_eq hx.seenX.sz⟩

/-- Once every value is read, the transformed values are the transform of them. -/
theorem XfRel.final {xf m sr sx : ByteArray} {done : List Nat} {S n : Nat} (hx : XfRel xf m sr sx done S) (hl : done.length = S)
    (hlt : ∀ v ∈ done, v < n) : MapOk xf (inverseMoveToFront done) S n :=
  ⟨hx.sz, by rw [inverseMoveToFront, inverseMoveToFrontFrom_length]; exact hl, fun i hi => hx.at_ i (by omega),
    inverseMoveToFront_lt hlt⟩

/-- The place reading a context map's values. Each value is written as read and, through the transform, as it is if the
last bit asks for the transform; the value read is flagged, and so are the step's transformed values from their first
round. -/
def stepHVals (st : Hd) (pos : USize) : Hd :=
  let left := st.left
  if left = 0 then { st with pos := pos, status := .next, tag := .imtf }
  else
    let r := mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      let v := r.a
      let run := r.b
      let idx := st.idx
      if left < run then markH st pos .bad
      else
        let fill := st.fill
        let xf := st.xf
        let m := st.mtf
        let sr := st.seenR
        let sx := st.seenX
        let st0 := clearMap st
        if r.count = st.count then
          -- A code that gives a value without reading gives it for every value left.
          let q := imtfRun m xf idx v left
          let c := if left ≤ v then left else v + 1
          { st0 with
            pos := pos, status := .next, idx := idx + left, left := 0
            fill := if v = 0 then fill else fillLens fill idx left v.toUInt8
            xf := q.2, mtf := q.1, seenR := setU sr v.toUSize 1, seenX := markAll q.2 sx idx c }
        else if v = 0 then
          let q := imtfRun m xf idx v run
          { st0 with
            word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
            fill := fill, xf := q.2, mtf := q.1, seenR := setU sr v.toUSize 1, seenX := markAll q.2 sx idx 1 }
        else
          let q := imtfRun m xf idx v run
          { st0 with
            word := r.word, count := r.count, pos := pos, status := .next, idx := idx + run, left := left - run
            fill := setU fill idx.toUSize v.toUInt8, xf := q.2, mtf := q.1, seenR := setU sr v.toUSize 1
            seenX := markAll q.2 sx idx 1 }

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
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHVals_ok {isL : Bool} {ntrees rlemax : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.vals isL ntrees rlemax code done left)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.vals isL ntrees rlemax code done left) st pos (stepHVals st pos) := by
  obtain ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩ := hrel
  have hrel : HRel st g (.vals isL ntrees rlemax code done left) :=
    ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩
  obtain ⟨_, hmle⟩ := mapSizeFast_eq (g := g) hi hu
  unfold stepHVals
  dsimp only
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    have hl0 : left = 0 := by
      rw [← hleft, h0]
      rfl
    subst hl0
    refine HStepOk.ofNext (g' := g) (p' := .imtf isL ntrees done) rfl
      ⟨hw, hu, rfl, hi, hn, h2, h256, ⟨hsz, by omega, fun i hi' => hat i (by omega), hlt⟩, hx.final (by omega) hlt, hx.seenR, hx.seenX⟩
      (Nat.le_refl _) hp (fun F => hrest_vals_zero K g isL ntrees rlemax code done _) (fun F => hStep_vals_zero _)
  rw [ite_eq_right h0]
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
  generalize mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval hsh0 hnb
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
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    have hno : runOf rlemax code = none := by
      cases e : runOf rlemax code with
      | none => rfl
      | some v => exact absurd ((hnone v e).1.symm.trans hsr) (by decide)
    exact HStepOk.ofShortRead (X := 31) hrel hfull (by omega) h3 h4
      (by rw [hStep_vals_step _ hl0 hno]; exact readIn_short h5 (by rw [held_len]; exact h3))
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨hv, hr1, hv1, hrlt⟩ := mapSym_bounds (by omega) h16 hsy ((hval hsr).2 [])
    have hv256 : r.a.toNat < 256 := by omega
    by_cases hbig : st.left < r.b
    · rw [ite_eq_left hbig]
      have hbig' : left < r.b.toNat := by
        rw [← hleft]
        exact UInt64.lt_iff_toNat_lt.mp hbig
      refine HStepOk.ofBad rfl (fun F => ?_)
      rw [avail_mk, hN]
      simp only [hbig', ↓reduceIte]
    rw [ite_eq_right hbig]
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
      have hx' := hx.step (n := st.left) (v := r.a) (idx := st.idx) (c := if st.left ≤ r.a then st.left else r.a + 1)
        hleft hidx (by omega) (by omega) (by omega) hv256 (by rw [min_run hv256, hleft])
      have hwork := hx'.work hmle
      by_cases hz : r.a = 0
      · have hz' : r.a.toNat = 0 := by rw [hz]; rfl
        have hfsz : (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).size = st.fill.size := by
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
        · show (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).size = _
          rw [ite_eq_left hz]
          exact hsz
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          show _ = some ((if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0).toNat
          rw [ite_eq_left hz]
          by_cases hA : i < done.length
          · rw [List.getElem?_append_left hA, hat i hA]
          · rw [List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega), hzero i (by omega), hz']
            rfl
        · intro i hi'
          rw [hlen3] at hi'
          show (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0 = 0
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
        obtain ⟨hfs, hfg⟩ := fillLens_spec r.a.toUInt8 left st.fill st.idx st.left hleft (by rw [hidx]; omega) (by rw [hidx, hsz]; omega)
        have hfsz : (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).size = st.fill.size := by
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
        · show (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).size = _
          rw [ite_eq_right hz, hfs]
          exact hsz
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hlt x h
          · rw [(List.mem_replicate.mp h).2]
            exact hv
        · intro i hi'
          rw [hlen3] at hi'
          show _ = some ((if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0).toNat
          rw [ite_eq_right hz, hfg i, hidx]
          by_cases hA : i < done.length
          · rw [ite_eq_right (by omega), List.getElem?_append_left hA, hat i hA]
          · rw [ite_eq_left (by omega), hbyte, List.getElem?_append_right (by omega), List.getElem?_replicate, ite_eq_left (by omega)]
        · intro i hi'
          rw [hlen3] at hi'
          show (if r.a = 0 then st.fill else fillLens st.fill st.idx st.left r.a.toUInt8).data[i]?.getD 0 = 0
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
      have hx' := hx.step (n := r.b) (v := r.a) (idx := st.idx) (c := 1) rfl hidx hr1 (by omega) (by omega) hv256 hone
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
      have hx' := hx.step (n := r.b) (v := r.a) (idx := st.idx) (c := 1) rfl hidx hr1 (by omega) (by omega) hv256 hone
      have hwork := hx'.work hmle
      refine HStepOk.ofNext (g' := g) (p' := .vals isL ntrees rlemax code (done ++ List.replicate r.b.toNat r.a.toNat) (left - r.b.toNat))
        (hd := Or.inl (Or.inr ⟨rfl, show left - r.b.toNat < left by omega⟩))
        (hm := ⟨rfl, rfl, fun h => ⟨by show (setU st.fill st.idx.toUSize r.a.toUInt8).size ≤ _; rw [size_setU]; exact h.fill,
          h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, hwork⟩,
          ⟨rfl, by simp [budH, tableOf]⟩⟩) rfl
        ⟨hw2, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, ?_, hleft2, ?_, ?_, ?_, ?_, ?_, hx'⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
      · show (st.idx + r.b).toNat = _
        rw [hidx2, hlen2]
      · rw [hlen2]
        omega
      · show (setU st.fill st.idx.toUSize r.a.toUInt8).size = _
        rw [size_setU]
        exact hsz
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hlt x h
        · rw [(List.mem_replicate.mp h).2]
          exact hv
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show _ = some ((setU st.fill st.idx.toUSize r.a.toUInt8).data[i]?.getD 0).toNat
        by_cases hA : i < done.length
        · rw [List.getElem?_append_left hA, hat i hA, setU_get_ne (by rw [hus]; omega)]
        · have he : i = done.length := by omega
          subst he
          have := setU_get_same (t := st.fill) (i := st.idx.toUSize) (v := r.a.toUInt8) (by rw [hus, hsz]; omega)
          rw [hus] at this
          rw [this, hbyte, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_replicate, ite_eq_left (by omega)]
      · intro i hi'
        rw [hlen2, hrun1] at hi'
        show (setU st.fill st.idx.toUSize r.a.toUInt8).data[i]?.getD 0 = 0
        rw [setU_get_ne (by rw [hus]; omega)]
        exact hzero i (by omega)
      · rw [avail_mk, hN]
        simp only [hbig', ↓reduceIte]
        rfl
      · rw [avail_mk, hStep_vals_step _ hl0 hno, readIn_some ((hval hsr).2 _)]
        simp only [hbig', ↓reduceIte]
        rfl

end

/-! ### A context map's last bit -/

/-- The place at a context map's last bit: it chooses the values as read or as transformed, and checks that every tree
occurs from their flags. -/
def stepHImtf (st : Hd) (pos : USize) : Hd :=
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
      if allMarked sr 0 n then mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n fill
      else { st0 with pos := pos, status := .bad }
    else
      if allMarked sx 0 n then mapFinish { st0 with word := b1.word, count := b1.count, pos := pos, status := .next } n xf
      else { st0 with pos := pos, status := .bad }
  else markH st pos .needsInput

private theorem not_le_lt3 {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHImtf_ok {isL : Bool} {ntrees : Nat} {vals : List Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.imtf isL ntrees vals)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.imtf isL ntrees vals) st pos (stepHImtf st pos) := by
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
    have key : ∀ (final seen : ByteArray) (cmap : List Nat), MapOk final cmap (mapSize g isL) ntrees → SeenIs seen cmap →
        (∀ f, hrest K g (.imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
          if (List.range ntrees).all cmap.contains then afterMap K g isL ntrees cmap (b1.held ++ f) else none) →
        (∀ f, hStepP (g, .imtf isL ntrees vals) ((BitBuffer.mk st.word st.count).held ++ f) =
          if (List.range ntrees).all cmap.contains then
            .next (g.setMap isL ntrees cmap, mapNextPhase (g.setMap isL ntrees cmap) isL) (b1.held ++ f) else .bad) →
        HStepOk K a stop g (.imtf isL ntrees vals) st pos
          (if allMarked seen 0 st.ntrees = true then
            mapFinish { clearMap st with word := b1.word, count := b1.count, pos := pos, status := .next } st.ntrees final
          else { clearMap st with pos := pos, status := .bad }) := by
      intro final seen cmap hfinal hseen hs hj
      have hocc := hseen.allMarked (n := st.ntrees) (by omega)
      rw [hn] at hocc
      by_cases hc : allMarked seen 0 st.ntrees = true
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
      exact key st.fill st.seenR vals hmR hsR hspec hjspec
    · rw [ite_eq_right hz]
      have hz' : ¬ im.toNat = 0 := fun e => hz (UInt64.toNat_inj.mp e)
      simp only [hz', ↓reduceIte] at hspec hjspec
      exact key st.xf st.seenX (inverseMoveToFront vals) hmX hsX hspec hjspec
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
