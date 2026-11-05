import Brotli.Decoder.HeaderCode

/-!
# The code lengths of the code length alphabet

The place reading them, up to the code length code's table.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The order of the code length alphabet, in an array. -/
def clOrderLut : ByteArray := (codeLengthOrder.map Nat.toUInt8).toByteArray

private theorem clOrder_values : ∀ i, i < 18 → ∃ x, codeLengthOrder[i]? = some x ∧ x < 18 ∧
    ((codeLengthOrder.map Nat.toUInt8)[i]?.getD 0).toNat = x := by
  decide +kernel

theorem clOrderLut_at {i : Nat} (h : i < 18) : ∃ x, codeLengthOrder[i]? = some x ∧ x < 18 ∧ (clOrderLut.data[i]?.getD 0).toNat = x := by
  obtain ⟨x, h1, h2, h3⟩ := clOrder_values i h
  refine ⟨x, h1, h2, ?_⟩
  simp only [clOrderLut, List.data_toByteArray, List.getElem?_toArray]
  exact h3

section
variable {α : Type} (K : HK α)

/-- With no more code length symbols, one non-zero length gives a single-symbol code. -/
theorem hrest_clens_nil (g : Gh) (o : Owner) (size : Nat) (acc : List (Nat × Nat)) (sum : Nat) (bs : List Bool) :
    hrest K g (.clens o size [] acc sum) bs =
      if (acc.filter (·.2 != 0)).length = 1 then hrest K g (.syms o size (codeLengthCode acc) ⟨[], 8, none⟩) bs else none := by
  show ((if (acc.filter (·.2 != 0)).length = 1 then some (acc, bs) else none) >>= _) = _
  split <;> rfl

/-- One more length of a code length symbol. -/
theorem hrest_clens_cons (g : Gh) (o : Owner) (size : Nat) (sym : Nat) (rest : List Nat) (acc : List (Nat × Nat)) (sum : Nat) (bs : List Bool) :
    hrest K g (.clens o size (sym :: rest) acc sum) bs = readCodeLengthCodeLength bs >>= fun p =>
      if p.1 = 0 then hrest K g (.clens o size rest (acc ++ [(sym, p.1)]) sum) p.2
      else if sum + (32 >>> p.1) = 32 then hrest K g (.syms o size (codeLengthCode (acc ++ [(sym, p.1)])) ⟨[], 8, none⟩) p.2
      else if 32 < sum + (32 >>> p.1) then none
      else hrest K g (.clens o size rest (acc ++ [(sym, p.1)]) (sum + (32 >>> p.1))) p.2 := by
  show (readCodeLengthCodeLengths (sym :: rest) acc sum bs >>= _) = _
  simp only [readCodeLengthCodeLengths]
  cases readCodeLengthCodeLength bs with
  | none => rfl
  | some p =>
    obtain ⟨len, b1⟩ := p
    show ((if len = 0 then readCodeLengthCodeLengths rest (acc ++ [(sym, len)]) sum b1
      else if sum + 32 >>> len = 32 then some (acc ++ [(sym, len)], b1)
      else if 32 < sum + 32 >>> len then none
      else readCodeLengthCodeLengths rest (acc ++ [(sym, len)]) (sum + 32 >>> len) b1) >>= _) =
      (if len = 0 then hrest K g (.clens o size rest (acc ++ [(sym, len)]) sum) b1
      else if sum + (32 >>> len) = 32 then hrest K g (.syms o size (codeLengthCode (acc ++ [(sym, len)])) ⟨[], 8, none⟩) b1
      else if 32 < sum + (32 >>> len) then none
      else hrest K g (.clens o size rest (acc ++ [(sym, len)]) (sum + (32 >>> len))) b1)
    by_cases h0 : len = 0
    · rw [ite_eq_left h0, ite_eq_left h0]
      rfl
    · rw [ite_eq_right h0, ite_eq_right h0]
      by_cases h1 : sum + 32 >>> len = 32
      · rw [ite_eq_left h1, ite_eq_left h1]
        rfl
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : 32 < sum + 32 >>> len
        · rw [ite_eq_left h2, ite_eq_left h2]
          rfl
        · rw [ite_eq_right h2, ite_eq_right h2]
          rfl

end

/-- What's needed of a finished code length code. -/
structure ClDone (st : Hd) (acc : List (Nat × Nat)) : Prop where
  symLt : st.clSym.toNat < 18
  one : st.clNz = 1 → ∃ l, acc.filter (·.2 != 0) = [(st.clSym.toNat, l)]
  sz : st.clNz ≠ 1 → (acc.filter (·.2 != 0)).length ≠ 1
  sum : st.clNz ≠ 1 → lengthSum (acc.map (·.2)) = 32768
  lens : st.clNz ≠ 1 → LensIs st.clLens 18 acc
  keys : (acc.map (·.1)).Nodup
  small : ∀ p ∈ acc, p.1 < 18 ∧ p.2 ≤ 5

private theorem usize18 : (USize.ofNat 18).toNat = 18 := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  have := USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- A finished code length code's lengths are all there. -/
theorem ClDone.len18 {st : Hd} {acc : List (Nat × Nat)} (hd : ClDone st acc) (h1 : st.clNz ≠ 1) :
    (USize.ofNat 18).toNat ≤ st.clLens.size := by
  rw [usize18, (hd.lens h1).sz]
  exact Nat.le_refl _

private theorem mem_lengthsOf_five {size : Nat} {P : List (Nat × Nat)} (h : ∀ p ∈ P, p.2 ≤ 5) : ∀ l ∈ lengthsOf size P, l ≤ 5 := by
  intro l hl
  simp only [lengthsOf, List.mem_map] at hl
  obtain ⟨n, _, e⟩ := hl
  subst e
  cases hf : P.find? (·.1 == n) with
  | none => simp
  | some p =>
    have := h p (List.mem_of_find?_eq_some hf)
    simp only [Option.map_some, Option.getD_some]
    omega

private theorem mem_lengthsOf_le {size : Nat} {P : List (Nat × Nat)} (h : ∀ p ∈ P, p.2 ≤ 5) : ∀ l ∈ lengthsOf size P, l ≤ 15 :=
  fun l hl => Nat.le_trans (mem_lengthsOf_five h l hl) (by decide)

/-- A finished code length code with more than one symbol has no length over five. -/
theorem ClDone.short {st : Hd} {acc : List (Nat × Nat)} (hd : ClDone st acc) (h1 : st.clNz ≠ 1) :
    ∀ l ∈ lensOf st.clLens (USize.ofNat 18).toNat, l ≤ 5 := by
  rw [usize18, (hd.lens h1).eq]
  exact mem_lengthsOf_five (fun p hp => (hd.small p hp).2)

/-- A finished code length code with more than one symbol is a complete code over its lengths. -/
theorem ClDone.complete {st : Hd} {acc : List (Nat × Nat)} (hd : ClDone st acc) (h1 : st.clNz ≠ 1) :
    Complete (.canonical (lensOf st.clLens (USize.ofNat 18).toNat)) := by
  have hl := hd.lens h1
  rw [usize18, hl.eq]
  refine ⟨mem_lengthsOf_le (fun p hp => (hd.small p hp).2), ?_⟩
  rw [lengthSum_lengthsOf_eq 18 acc hd.keys (fun p hp => (hd.small p hp).1), hd.sum h1]

/-- The code length code's table. -/
def clTable (st : Hd) (h : ∃ acc, ClDone st acc) : ByteArray :=
  if h1 : st.clNz = 1 then buildSingleFast ByteArray.empty st.clSym (by decide)
  else
    buildLens ByteArray.empty st.clLens (USize.ofNat 18) (by obtain ⟨_, hd⟩ := h; exact hd.len18 h1)
      ⟨by obtain ⟨_, hd⟩ := h; exact hd.complete h1, by rw [usize18]; decide, rfl, by decide⟩

/-- A finished code length code's table is the code's. -/
theorem clTable_built {st : Hd} {acc : List (Nat × Nat)} (hd : ClDone st acc) (h : ∃ acc, ClDone st acc) :
    Built ByteArray.empty (clTable st h) (codeLengthCode acc) ∧ (clTable st h).size ≤ 788 ∧ Complete (codeLengthCode acc) ∧
      (codeLengthCode acc).Symbols 18 := by
    unfold clTable
    by_cases h1 : st.clNz = 1
    · rw [dite_eq_left h1]
      obtain ⟨l, hl⟩ := hd.one h1
      have hc : codeLengthCode acc = .single st.clSym.toNat := by
        unfold codeLengthCode
        rw [hl]
      obtain ⟨b1, b2⟩ := built_single (t := ByteArray.empty) (sym := st.clSym) (by have := hd.symLt; omega) (by decide)
      rw [hc]
      exact ⟨b1, by rw [b2]; decide, trivial, hd.symLt⟩
    · rw [dite_eq_right h1]
      have hl := hd.lens h1
      have hn : (USize.ofNat 18).toNat = 18 := usize18
      have hnle : (USize.ofNat 18).toNat ≤ st.clLens.size := hd.len18 h1
      have hc : codeLengthCode acc = .canonical (lensOf st.clLens (USize.ofNat 18).toNat) := by
        rw [hn, hl.eq]
        unfold codeLengthCode
        split
        · rename_i sym len he
          have := hd.sz h1
          rw [he] at this
          simp at this
        · rfl
      have hC := hd.complete h1
      obtain ⟨b1, b2⟩ := built_canonical (t := ByteArray.empty) (hn := hnle) ⟨hC, by rw [hn]; decide, rfl, by decide⟩
      have hlen : (lensOf st.clLens (USize.ofNat 18).toNat).length = 18 := by rw [length_lensOf hnle, hn]
      have ht := tableBytes_le hC (size := 18) hlen
      unfold treeMax at ht
      rw [hc]
      refine ⟨b1, ?_, hC, hlen⟩
      rw [b2]
      show 0 + tableBytes (.canonical (lensOf st.clLens (USize.ofNat 18).toNat)) ≤ _
      omega

/-- A finished code length code's table fits. -/
theorem clTable_fits {st : Hd} (h : ∃ acc, ClDone st acc) :
    (clTable st h).size < 2 ^ 32 ∧ TableFits (clTable st h) (USize.ofNat 0).toNat := by
  obtain ⟨acc, hd⟩ := id h
  obtain ⟨hB, hsize, _, _⟩ := clTable_built hd h
  rw [usize_zero']
  exact ⟨by omega, hB.ok.toTableFits⟩

/-- Goes on to a code's lengths with the code length code's table `t`, with every length's list emptied. -/
@[inline] def clFinishAt (st : Hd) (t : ByteArray) (ht : t.size < 2 ^ 32 ∧ TableFits t (USize.ofNat 0).toNat) : Hd :=
  { st with
    tag := .syms, head := resetHead st.head, headSz := resetHead_size st.headSz
    ln := 0, prevLen := 8, repSym := 0, repCount := 0, symSum := 0, clt := ⟨t, ht.1, ht.2⟩ }

/-- Goes on from the code length code to a code's lengths: its table is built before the lists are emptied, so that they
are emptied in place. -/
def clFinish (st : Hd) (h : ∃ acc, ClDone st acc) : Hd := clFinishAt st (clTable st h) (clTable_fits h)

/-- A finished code length code's table. -/
theorem clFinish_ok {st : Hd} {g : Gh} {o : Owner} {size : Nat} {acc : List (Nat × Nat)}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hu : Upto st.d g (ownerStage o)) (hs : SizeOk st size) (ho : OwnerRel st g size o)
    (hd : ClDone st acc) {h : ∃ acc, ClDone st acc} :
    HRel (clFinish st h) g (.syms o size (codeLengthCode acc) ⟨[], 8, none⟩) ∧
      (clFinish st h).status = st.status ∧ (clFinish st h).word = st.word ∧ (clFinish st h).count = st.count ∧
      (clFinish st h).pos = st.pos ∧ (clFinish st h).d = st.d ∧ (HSize st → HSize (clFinish st h)) := by
  obtain ⟨hB, hsize, hC, hsy⟩ := clTable_built hd h
  unfold clFinish clFinishAt
  dsimp only
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨⟨hw, hu, rfl, ⟨hs1, hs2, hs3⟩, ho, ?_⟩, rfl, rfl, rfl, rfl, rfl, fun h =>
    ⟨h.fill, ⟨Nat.le_of_eq (resetHead_size st.headSz), Nat.le_of_eq st.nextSz⟩, h.clLens, hsize, h.mapT, h.modes, h.lMap,
      h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩⟩
  exact {
    table := by rw [usize_zero']; exact hB.ok
    complete := hC
    symbols := hsy
    ln := rfl
    le := by simp
    lists := resetHead_lists st.headSz st.next
    small := by simp
    prev := rfl
    prevOk := by simp
    rep := rfl
    sumOk := by simp [lengthSum]
    sumLe := by simp [lengthSum] }

/-! ### The place reading them -/

private theorem codeOrder_ok' : codeLengthOrder.Nodup ∧ ∀ x ∈ codeLengthOrder, x < 18 := by
  decide +kernel

private theorem len_scale : ∀ l, l < 6 → l ≠ 0 → 32768 >>> l = 1024 * (32 >>> l) := by decide

private theorem sum_push (acc : List (Nat × Nat)) (x len : Nat) :
    lengthSum ((acc ++ [(x, len)]).map (·.2)) = lengthSum (acc.map (·.2)) + (if len = 0 then 0 else 32768 >>> len) := by
  rw [List.map_append, lengthSum_append]
  simp [lengthSum]

private theorem keys_push {acc : List (Nat × Nat)} {x : Nat} {rest : List Nat} (hk : (acc.map (·.1)).Nodup)
    (ha : ∀ p ∈ acc, p.1 ∉ x :: rest) (len : Nat) : ((acc ++ [(x, len)]).map (·.1)).Nodup := by
  rw [List.map_append]
  refine List.pairwise_append.mpr ⟨hk, List.pairwise_singleton _ _, ?_⟩
  intro a hA b hb
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
  subst hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
  intro he
  exact (ha p hp) (by rw [he]; simp)

private theorem apart_push {acc : List (Nat × Nat)} {x : Nat} {rest : List Nat} (hx : x < 18) (hnd : (x :: rest).Nodup)
    (ha : ∀ p ∈ acc, p.1 < 18 ∧ p.1 ∉ x :: rest ∧ p.2 ≤ 5) {len : Nat} (hlen : len ≤ 5) :
    ∀ p ∈ acc ++ [(x, len)], p.1 < 18 ∧ p.1 ∉ rest ∧ p.2 ≤ 5 := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · obtain ⟨h1, h2, h3⟩ := ha p h
    exact ⟨h1, fun hm => h2 (List.mem_cons_of_mem _ hm), h3⟩
  · rw [List.mem_singleton.mp h]
    exact ⟨hx, (List.nodup_cons.mp hnd).1, hlen⟩

/-- The code length code's lengths are complete once the last one read fills the code space. -/
theorem clens_complete {st : Hd} {order : List Nat} {acc : List (Nat × Nat)} {sum : Nat} (hw : (BitBuffer.mk st.word st.count).Wf)
    (hc : ClRel st order acc sum) (h18 : st.clIdx ≠ 18) (hok : (cclFast ⟨st.word, st.count⟩).status = .ok)
    (h0 : (cclFast ⟨st.word, st.count⟩).a ≠ 0) (h32 : st.clSum + ((32 : UInt64) >>> (cclFast ⟨st.word, st.count⟩).a) = 32) :
    Complete (.canonical (lensOf (setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 (cclFast ⟨st.word, st.count⟩).a) 18)) := by
  have horder := hc.orderOk
  have hidxLe := hc.le
  have hidx18 : st.clIdx.toNat ≠ 18 := fun e => h18 (UInt64.toNat_inj.mp e)
  have hidxLt : st.clIdx.toNat < 18 := by omega
  obtain ⟨x, hx, hx18, hlut⟩ := clOrderLut_at hidxLt
  obtain ⟨hL1, hL2⟩ := List.getElem?_eq_some_iff.mp hx
  have horder' : order = x :: codeLengthOrder.drop (st.clIdx.toNat + 1) := by
    rw [horder, List.drop_eq_getElem_cons hL1, hL2]
  have hnodup : (x :: codeLengthOrder.drop (st.clIdx.toNat + 1)).Nodup := by
    rw [← horder', horder]
    exact codeOrder_ok'.1.sublist (List.drop_sublist _ _)
  generalize codeLengthOrder.drop (st.clIdx.toNat + 1) = rest at horder' hnodup
  subst horder'
  have R := cclFast_ok hw
  have hval2 := (R.ok hok).2 []
  generalize cclFast ⟨st.word, st.count⟩ = r at hval2 hok h0 h32 ⊢
  have hlen5 : r.a.toNat ≤ 5 := (readCodeLengthCodeLength_width hval2).1
  have happ := apart_push hx18 hnodup hc.apart hlen5
  have hkeys := keys_push hc.keys (fun p hp => (hc.apart p hp).2.1) r.a.toNat
  have h0' : r.a.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
  have hsym : (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat = x := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by omega), hlut]
  have hsh : ((32 : UInt64) >>> r.a).toNat = 32 >>> r.a.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega)]
    rfl
  have hshLt : 32 >>> r.a.toNat ≤ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _
  have hsumU : (st.clSum + ((32 : UInt64) >>> r.a)).toNat = sum + 32 >>> r.a.toNat := by
    rw [UInt64.toNat_add, hc.sumOk, hsh]
    exact Nat.mod_eq_of_lt (by have := hc.sumLt; omega)
  have h32' : sum + 32 >>> r.a.toNat = 32 := by
    rw [← hsumU, h32]
    rfl
  have hlensP : LensIs (setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a) 18 (acc ++ [(x, r.a.toNat)]) := by
    have := LensIs.push (⟨hc.size, hc.lens⟩ : LensIs st.clLens 18 acc) (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a (by rw [hsym]; exact hx18)
      (by decide) (by omega) (fun p hp e => (hc.apart p hp).2.1 (by rw [e, hsym]; simp))
    rwa [hsym] at this
  have hsumP : lengthSum ((acc ++ [(x, r.a.toNat)]).map (·.2)) = 1024 * (sum + 32 >>> r.a.toNat) := by
    rw [sum_push, ite_eq_right h0', hc.sumEq, len_scale _ (by omega) h0', Nat.mul_add]
  rw [hlensP.eq]
  refine ⟨mem_lengthsOf_le (fun p hp => (happ p hp).2.2), ?_⟩
  rw [lengthSum_lengthsOf_eq 18 _ hkeys (fun p hp => (happ p hp).1), hsumP, h32']

/-- A state at a code length code's lengths stands for a place there. -/
theorem clens_ex {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .clens) :
    ∃ g o size order acc sum, HRel st g (.clens o size order acc sum) := by
  obtain ⟨g, p, hr⟩ := h
  cases p with
  | clens o size order acc sum => exact ⟨g, o, size, order, acc, sum, hr⟩
  | np => exact absurd (hr.2.2.symm.trans ht) (fun e => HTag.noConfusion e)
  | _ => exact absurd (hr.2.2.1.symm.trans ht) (fun e => HTag.noConfusion e)

/-- With all eighteen lengths read and one of them non-zero, the code length code is finished. -/
theorem clens_done0 {st : Hd} {pos : USize} (h : ∃ g p, HRel st g p) (ht : st.tag = .clens) (h18 : st.clIdx = 18)
    (hnz : st.clNz = 1) : ∃ acc, ClDone { st with pos := pos, status := .next } acc := by
  obtain ⟨g, o, size, order, acc, sum, hrel⟩ := clens_ex h ht
  obtain ⟨_, _, _, _, _, hc⟩ := hrel
  have hnil : order = [] := by
    rw [hc.orderOk, h18]
    rfl
  subst hnil
  have hlen1 : (acc.filter (·.2 != 0)).length = 1 := by
    rw [← hc.nz, hnz]
    rfl
  exact ⟨acc, {
    symLt := hc.symLt
    one := fun _ => hc.nzOne hlen1
    sz := fun e => absurd hnz e
    sum := fun e => absurd hnz e
    lens := fun e => absurd hnz e
    keys := hc.keys
    small := fun p hp => ⟨(hc.apart p hp).1, (hc.apart p hp).2.2⟩ }⟩

/-- A non-zero length that fills the code space finishes the code length code. -/
theorem clens_done1 {st : Hd} {pos : USize} {r : Rd} (h : ∃ g p, HRel st g p) (ht : st.tag = .clens) (h18 : ¬ st.clIdx = 18)
    (hr5 : r.a.toNat ≤ 5) (h0 : ¬ r.a = 0) (h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32) :
    ∃ acc, ClDone { st with
      word := r.word, count := r.count, pos := pos, status := .next
      clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
      clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } acc := by
  obtain ⟨g, o, size, order, acc, sum, hrel⟩ := clens_ex h ht
  obtain ⟨_, _, _, _, _, hc⟩ := hrel
  have horder := hc.orderOk
  have hidxLe := hc.le
  have hidx18 : st.clIdx.toNat ≠ 18 := fun e => h18 (UInt64.toNat_inj.mp e)
  have hidxLt : st.clIdx.toNat < 18 := by omega
  obtain ⟨x, hx, hx18, hlut⟩ := clOrderLut_at hidxLt
  obtain ⟨hL1, hL2⟩ := List.getElem?_eq_some_iff.mp hx
  have horder' : order = x :: codeLengthOrder.drop (st.clIdx.toNat + 1) := by
    rw [horder, List.drop_eq_getElem_cons hL1, hL2]
  have hnodup : (x :: codeLengthOrder.drop (st.clIdx.toNat + 1)).Nodup := by
    rw [← horder', horder]
    exact codeOrder_ok'.1.sublist (List.drop_sublist _ _)
  generalize codeLengthOrder.drop (st.clIdx.toNat + 1) = rest at horder' hnodup
  subst horder'
  have happ := apart_push hx18 hnodup hc.apart hr5
  have hkeys := keys_push hc.keys (fun p hp => (hc.apart p hp).2.1) r.a.toNat
  have h0' : r.a.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
  have hsym : (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat = x := by
    rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by omega), hlut]
  have hsh : ((32 : UInt64) >>> r.a).toNat = 32 >>> r.a.toNat := by
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega)]
    rfl
  have hshLt : 32 >>> r.a.toNat ≤ 32 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_le_self _ _
  have hsumU : (st.clSum + ((32 : UInt64) >>> r.a)).toNat = sum + 32 >>> r.a.toNat := by
    rw [UInt64.toNat_add, hc.sumOk, hsh]
    exact Nat.mod_eq_of_lt (by have := hc.sumLt; omega)
  have hnz1 : (st.clNz + 1).toNat = (acc.filter (·.2 != 0)).length + 1 := by
    have hle := hc.nzLe
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega), hc.nz]
  have hfilt : (acc ++ [(x, r.a.toNat)]).filter (·.2 != 0) = acc.filter (·.2 != 0) ++ [(x, r.a.toNat)] := by
    simp [h0']
  have hlensP : LensIs (setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a) 18 (acc ++ [(x, r.a.toNat)]) := by
    have := LensIs.push (⟨hc.size, hc.lens⟩ : LensIs st.clLens 18 acc) (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a (by rw [hsym]; exact hx18)
      (by decide) (by omega) (fun p hp e => (hc.apart p hp).2.1 (by rw [e, hsym]; simp))
    rwa [hsym] at this
  have hsumP : lengthSum ((acc ++ [(x, r.a.toNat)]).map (·.2)) = 1024 * (sum + 32 >>> r.a.toNat) := by
    rw [sum_push, ite_eq_right h0', hc.sumEq, len_scale _ (by omega) h0', Nat.mul_add]
  have h32' : sum + 32 >>> r.a.toNat = 32 := by
    rw [← hsumU, h32]
    rfl
  refine ⟨acc ++ [(x, r.a.toNat)], {
    symLt := ?_
    one := ?_
    sz := ?_
    sum := fun _ => by rw [hsumP, h32']
    lens := fun _ => hlensP
    keys := hkeys
    small := fun p hp => ⟨(happ p hp).1, (happ p hp).2.2⟩ }⟩
  · show (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat < 18
    rw [hsym]
    exact hx18
  · intro e
    have h1 : (st.clNz + 1).toNat = 1 := by rw [show st.clNz + 1 = 1 from e]; rfl
    rw [hnz1] at h1
    have hz : acc.filter (·.2 != 0) = [] := List.length_eq_zero_iff.mp (by omega)
    refine ⟨r.a.toNat, ?_⟩
    rw [hfilt, hz, hsym]
    rfl
  · intro e
    rw [hfilt]
    simp only [List.length_append, List.length_singleton]
    intro h2
    have h1 : (st.clNz + 1).toNat = 1 := by rw [hnz1]; omega
    exact e (UInt64.toNat_inj.mp h1)

/-- The place at the next code length of a code length symbol. -/
def stepHClens (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .clens) : Hd :=
  if h18 : st.clIdx = 18 then
    if hnz : st.clNz = 1 then clFinish { st with pos := pos, status := .next } (clens_done0 h ht h18 hnz)
    else markH st pos .bad
  else
    match cclFastS ⟨st.word, st.count⟩ with
    | ⟨r, hr5⟩ =>
    match r.status with
    | .short => markH st pos .needsInput
    | .bad => markH st pos .bad
    | .ok =>
      if h0 : r.a = 0 then { st with word := r.word, count := r.count, pos := pos, status := .next, clIdx := st.clIdx + 1 }
      else
        if h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32 then
          clFinish { st with
            word := r.word, count := r.count, pos := pos, status := .next
            clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
            clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 }
            (clens_done1 h ht h18 hr5 h0 h32)
        else
          let sym := (getU clOrderLut st.clIdx.toUSize).toUInt64
          let sum := st.clSum + ((32 : UInt64) >>> r.a)
          if 32 < sum then markH st pos .bad
          else
            let lens := st.clLens
            let nz := st.clNz + 1
            let st0 := clearClLens st
            { st0 with
              word := r.word, count := r.count, pos := pos, status := .next, clLens := setLen lens sym r.a, clSum := sum, clNz := nz
              clSym := sym, clIdx := st.clIdx + 1 }

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepHClens_ok {o : Owner} {size : Nat} {order : List Nat} {acc : List (Nat × Nat)} {sum : Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.clens o size order acc sum)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop)
    {hH : ∃ g p, HRel st g p} {hT : st.tag = .clens} :
    HStepOk K a stop g (.clens o size order acc sum) st pos (stepHClens st pos hH hT) := by
  obtain ⟨hw, hu, ht, hs, ho, hc⟩ := hrel
  have hrel : HRel st g (.clens o size order acc sum) := ⟨hw, hu, ht, hs, ho, hc⟩
  have horder := hc.orderOk
  have hidxLe := hc.le
  unfold stepHClens
  dsimp only
  by_cases h18 : st.clIdx = 18
  · rw [dite_eq_left h18]
    have hnil : order = [] := by
      rw [horder, h18]
      rfl
    subst hnil
    by_cases hnz : st.clNz = 1
    · rw [dite_eq_left hnz]
      have hlen1 : (acc.filter (·.2 != 0)).length = 1 := by
        rw [← hc.nz, hnz]
        rfl
      have hdone : ClDone { st with pos := pos, status := .next } acc :=
        { symLt := hc.symLt, one := fun _ => hc.nzOne hlen1, sz := fun h => absurd hnz h, sum := fun h => absurd hnz h,
          lens := fun h => absurd hnz h, keys := hc.keys, small := fun p hp => ⟨(hc.apart p hp).1, (hc.apart p hp).2.2⟩ }
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := clFinish_ok (st := { st with pos := pos, status := .next }) (h := ⟨acc, hdone⟩)
        hw hu hs ho hdone
      have hsz : HSize st → HSize (clFinish { st with pos := pos, status := .next } ⟨acc, hdone⟩) := fun h =>
        h7 ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
      generalize clFinish { st with pos := pos, status := .next } ⟨acc, hdone⟩ = r2 at h1 h2 h3 h4 h5 h6 hsz
      refine HStepOk.ofNext (hm := HMove.ofD h6 hsz (Nat.le_refl _)) h2 h1 (by rw [h5]; exact Nat.le_refl _) (by rw [h5]; exact hp)
        (fun F => ?_) (fun F => ?_)
      · rw [hrest_clens_nil, ite_eq_left hlen1, avail_mk, avail_mk, h3, h4, h5]
      · show (if (acc.filter (·.2 != 0)).length = 1 then _ else _) = _
        rw [ite_eq_left hlen1, avail_mk, avail_mk, h3, h4, h5]
    · rw [dite_eq_right hnz]
      have hlen1 : ¬ (acc.filter (·.2 != 0)).length = 1 := by
        rw [← hc.nz]
        exact fun e => hnz (UInt64.toNat_inj.mp e)
      exact HStepOk.ofBad rfl (fun F => by rw [hrest_clens_nil, ite_eq_right hlen1])
  rw [dite_eq_right h18]
  have hidx18 : st.clIdx.toNat ≠ 18 := fun e => h18 (UInt64.toNat_inj.mp e)
  have hidxLt : st.clIdx.toNat < 18 := by omega
  obtain ⟨x, hx, hx18, hlut⟩ := clOrderLut_at hidxLt
  obtain ⟨hL1, hL2⟩ := List.getElem?_eq_some_iff.mp hx
  have horder' : order = x :: codeLengthOrder.drop (st.clIdx.toNat + 1) := by
    rw [horder, List.drop_eq_getElem_cons hL1, hL2]
  have hnodup : (x :: codeLengthOrder.drop (st.clIdx.toNat + 1)).Nodup := by
    rw [← horder', horder]
    exact codeOrder_ok'.1.sublist (List.drop_sublist _ _)
  generalize hrest' : codeLengthOrder.drop (st.clIdx.toNat + 1) = rest at horder' hnodup
  subst horder'
  have hidx1 : (st.clIdx + 1).toNat = st.clIdx.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have horderN : rest = codeLengthOrder.drop (st.clIdx + 1).toNat := by rw [hidx1, hrest']
  have R := cclFast_ok hw
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.clens o size (x :: rest) acc sum)) (N := fun v b =>
    if v = 0 then hrest K g (.clens o size rest (acc ++ [(x, v)]) sum) b
    else if sum + (32 >>> v) = 32 then hrest K g (.syms o size (codeLengthCode (acc ++ [(x, v)])) ⟨[], 8, none⟩) b
    else if 32 < sum + (32 >>> v) then none
    else hrest K g (.clens o size rest (acc ++ [(x, v)]) (sum + (32 >>> v))) b) (fun bs => hrest_clens_cons K g o size x rest acc sum bs)
  have hval := R.ok
  have hsh0 := R.short
  generalize hrr : cclFastS ⟨st.word, st.count⟩ = rr
  obtain ⟨r, hr5⟩ := rr
  have er : r = cclFast ⟨st.word, st.count⟩ := by rw [← cclFastS_val, hrr]
  rw [← er] at Rok Rshort Rbad hval hsh0
  dsimp only
  cases hsr : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    exact HStepOk.ofShortRead (X := 4) hrel hfull (by omega) h3 h4
      (by show readIn 4 readCodeLengthCodeLength _ _ = _; exact readIn_short h5 (by rw [held_len]; exact h3))
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hsr _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    have hval2 := (hval hsr).2 []
    have hlen5 : r.a.toNat ≤ 5 := (readCodeLengthCodeLength_width hval2).1
    have happ := apart_push hx18 hnodup hc.apart hlen5
    have hkeys := keys_push hc.keys (fun p hp => (hc.apart p hp).2.1) r.a.toNat
    by_cases h0 : r.a = 0
    · rw [dite_eq_left h0]
      have h0' : r.a.toNat = 0 := by rw [h0]; rfl
      rw [h0'] at happ hkeys
      have hrelN : ClRel { st with word := r.word, count := r.count, pos := pos, status := .next, clIdx := st.clIdx + 1 } rest (acc ++ [(x, 0)]) sum :=
        { orderOk := horderN
          le := by show (st.clIdx + 1).toNat ≤ 18; omega
          sumOk := hc.sumOk
          sumLt := hc.sumLt
          sumEq := by rw [sum_push]; simpa using hc.sumEq
          size := hc.size
          lens := (LensIs.pushZero ⟨hc.size, hc.lens⟩ x).at_
          keys := hkeys
          apart := happ
          nz := by
            show st.clNz.toNat = _
            rw [hc.nz]
            simp
          nzLe := by
            show st.clNz.toNat ≤ (st.clIdx + 1).toNat
            have := hc.nzLe
            omega
          nzOne := by
            intro hone
            have e : (acc ++ [(x, 0)]).filter (·.2 != 0) = acc.filter (·.2 != 0) := by simp
            rw [e] at hone ⊢
            exact hc.nzOne hone
          symLt := hc.symLt }
      refine HStepOk.ofNext (g' := g) (p' := .clens o size rest (acc ++ [(x, 0)]) sum) rfl ⟨hw2, hu, ht, hs, ho, hrelN⟩ (Nat.le_refl _) hp
        (fun F => ?_) (fun F => ?_)
      · rw [avail_mk, hN]
        simp only [h0', ↓reduceIte]
        rfl
      · rw [avail_mk]
        show readIn 4 readCodeLengthCodeLength _ _ = _
        rw [readIn_some ((hval hsr).2 _)]
        simp only [h0', ↓reduceIte]
        rfl
    · rw [dite_eq_right h0]
      have h0' : r.a.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
      have hsym : (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat = x := by
        rw [UInt8.toNat_toUInt64, getU_toNat, word_toUSize (by omega), hlut]
      have hus : (getU clOrderLut st.clIdx.toUSize).toUInt64.toUSize.toNat = x := by
        rw [word_toUSize (by omega), hsym]
      have hsh : ((32 : UInt64) >>> r.a).toNat = 32 >>> r.a.toNat := by
        rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega)]
        rfl
      have hshLt : 32 >>> r.a.toNat ≤ 32 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_le_self _ _
      have hsumU : (st.clSum + ((32 : UInt64) >>> r.a)).toNat = sum + 32 >>> r.a.toNat := by
        rw [UInt64.toNat_add, hc.sumOk, hsh]
        exact Nat.mod_eq_of_lt (by have := hc.sumLt; omega)
      have hnz1 : (st.clNz + 1).toNat = (acc.filter (·.2 != 0)).length + 1 := by
        have hle := hc.nzLe
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega), hc.nz]
      have hfilt : (acc ++ [(x, r.a.toNat)]).filter (·.2 != 0) = acc.filter (·.2 != 0) ++ [(x, r.a.toNat)] := by
        simp [h0']
      have hlensP : LensIs (setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a) 18 (acc ++ [(x, r.a.toNat)]) := by
        have := LensIs.push (⟨hc.size, hc.lens⟩ : LensIs st.clLens 18 acc) (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a (by rw [hsym]; exact hx18)
          (by decide) (by omega) (fun p hp e => (hc.apart p hp).2.1 (by rw [e, hsym]; simp))
        rwa [hsym] at this
      have hsumP : lengthSum ((acc ++ [(x, r.a.toNat)]).map (·.2)) = 1024 * (sum + 32 >>> r.a.toNat) := by
        rw [sum_push, ite_eq_right h0', hc.sumEq, len_scale _ (by omega) h0', Nat.mul_add]
      by_cases h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32
      · rw [dite_eq_left h32]
        have h32' : sum + 32 >>> r.a.toNat = 32 := by
          rw [← hsumU, h32]
          rfl
        have hdone : ClDone { st with
            word := r.word, count := r.count, pos := pos, status := .next
            clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
            clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } (acc ++ [(x, r.a.toNat)]) :=
          { symLt := by show (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat < 18; rw [hsym]; exact hx18
            one := by
              intro h
              have h1 : (st.clNz + 1).toNat = 1 := by rw [show st.clNz + 1 = 1 from h]; rfl
              rw [hnz1] at h1
              have hz : acc.filter (·.2 != 0) = [] := List.length_eq_zero_iff.mp (by omega)
              refine ⟨r.a.toNat, ?_⟩
              rw [hfilt, hz, hsym]
              rfl
            sz := by
              intro h
              rw [hfilt]
              simp only [List.length_append, List.length_singleton]
              intro h2
              have h1 : (st.clNz + 1).toNat = 1 := by rw [hnz1]; omega
              exact h (UInt64.toNat_inj.mp h1)
            sum := fun _ => by rw [hsumP, h32']
            lens := fun _ => hlensP
            keys := hkeys
            small := fun p hp => ⟨(happ p hp).1, (happ p hp).2.2⟩ }
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := clFinish_ok (st := { st with
            word := r.word, count := r.count, pos := pos, status := .next
            clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
            clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 })
          (h := ⟨_, hdone⟩) hw2 hu hs ho hdone
        have hsz : HSize st → HSize (clFinish { st with
            word := r.word, count := r.count, pos := pos, status := .next
            clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
            clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } ⟨_, hdone⟩) := fun h =>
          h7 ⟨h.fill, h.lens, Nat.le_of_eq hlensP.sz, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩
        generalize clFinish { st with
            word := r.word, count := r.count, pos := pos, status := .next
            clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
            clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } ⟨_, hdone⟩ = r2
          at h1 h2 h3 h4 h5 h6 hsz
        refine HStepOk.ofNext (hm := HMove.ofD h6 hsz (Nat.le_refl _)) h2 h1 (by rw [h5]; exact Nat.le_refl _) (by rw [h5]; exact hp)
          (fun F => ?_) (fun F => ?_)
        · rw [avail_mk, hN]
          simp only [h0', h32', ↓reduceIte]
          rw [avail_mk, h3, h4, h5]
          rfl
        · rw [avail_mk]
          show readIn 4 readCodeLengthCodeLength _ _ = _
          rw [readIn_some ((hval hsr).2 _)]
          simp only [h0', h32', ↓reduceIte]
          rw [avail_mk, h3, h4, h5]
          rfl
      · rw [dite_eq_right h32]
        have h32' : ¬ sum + 32 >>> r.a.toNat = 32 := by
          rw [← hsumU]
          exact fun e => h32 (UInt64.toNat_inj.mp e)
        by_cases hgt : 32 < st.clSum + ((32 : UInt64) >>> r.a)
        · rw [ite_eq_left hgt]
          have hgt' : 32 < sum + 32 >>> r.a.toNat := by
            rw [← hsumU]
            exact UInt64.lt_iff_toNat_lt.mp hgt
          refine HStepOk.ofBad rfl (fun F => ?_)
          rw [avail_mk, hN]
          simp only [h0', h32', hgt', ↓reduceIte]
        · rw [ite_eq_right hgt]
          have hgt' : ¬ 32 < sum + 32 >>> r.a.toNat := by
            rw [← hsumU]
            exact fun e => hgt (UInt64.lt_iff_toNat_lt.mpr e)
          have hrelN : ClRel { clearClLens st with
              word := r.word, count := r.count, pos := pos, status := .next
              clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
              clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } rest (acc ++ [(x, r.a.toNat)])
              (sum + 32 >>> r.a.toNat) :=
            { orderOk := horderN
              le := by show (st.clIdx + 1).toNat ≤ 18; omega
              sumOk := hsumU
              sumLt := by omega
              sumEq := hsumP
              size := hlensP.sz
              lens := hlensP.at_
              keys := hkeys
              apart := happ
              nz := by
                show (st.clNz + 1).toNat = _
                rw [hnz1, hfilt]
                simp
              nzLe := by
                show (st.clNz + 1).toNat ≤ (st.clIdx + 1).toNat
                have := hc.nzLe
                rw [hnz1, ← hc.nz]
                omega
              nzOne := by
                intro hone
                rw [hfilt] at hone ⊢
                simp only [List.length_append, List.length_singleton] at hone
                have hz : acc.filter (·.2 != 0) = [] := List.length_eq_zero_iff.mp (by omega)
                refine ⟨r.a.toNat, ?_⟩
                rw [hz]
                show [(x, r.a.toNat)] = [((getU clOrderLut st.clIdx.toUSize).toUInt64.toNat, r.a.toNat)]
                rw [hsym]
              symLt := by show (getU clOrderLut st.clIdx.toUSize).toUInt64.toNat < 18; rw [hsym]; exact hx18 }
          refine HStepOk.ofNext (g' := g) (p' := .clens o size rest (acc ++ [(x, r.a.toNat)]) (sum + 32 >>> r.a.toNat))
            (hm := HMove.ofD rfl (fun h => ⟨h.fill, h.lens, Nat.le_of_eq hlensP.sz, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩) (Nat.le_refl _)) rfl
            ⟨hw2, hu, ht, hs, ho, hrelN⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
          · rw [avail_mk, hN]
            simp only [h0', h32', hgt', ↓reduceIte]
            rfl
          · rw [avail_mk]
            show readIn 4 readCodeLengthCodeLength _ _ = _
            rw [readIn_some ((hval hsr).2 _)]
            simp only [h0', h32', hgt', ↓reduceIte]
            rfl

end

end Brotli.Decoder
