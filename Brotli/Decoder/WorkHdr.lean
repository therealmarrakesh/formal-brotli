import Brotli.Decoder.Progress
import Brotli.Decoder.CostHeader

/-!
# The work of a header

A header step's work, counted by `stepHW`, is paid for by the bits the header reads. Most steps do little and read at least
one bit. The few that do much (building a table, zero-filling a context map, the inverse move-to-front transform) or read
nothing are paid for in advance: a potential on the places of the header read in order holds what is still to do once the
bits that settle its size are read, and rises only when bits are read.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Tables -/

/-- At most one length for each symbol is longer than eight. -/
theorem longCount_le (L : List Nat) : longCount L ≤ L.length := by
  have hs := countP_split (fun l => 9 ≤ l && l < 16) (fun l => l - 9) 7 L (fun a _ h => by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    omega)
  have he : sumR (fun r => L.countP (fun a => (9 ≤ a && a < 16) && (a - 9 == r))) 7 = longCount L := by
    unfold longCount
    apply sumR_congr
    intro r hr
    unfold blCount
    rw [ite_eq_right (by omega), ← List.countP_eq_length_filter]
    apply List.countP_congr
    intro a _
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega
  rw [← he, ← hs]
  exact List.countP_le_length

/-- A table's work, with its lengths complete: thirteen for each symbol and 11000 more, and for a context map's code its
check and the map's zeros. -/
theorem tableDoneW_le {st : Hd} {single : Bool} (hn : st.size.toNat ≤ 704) (hlens : st.size.toNat ≤ st.lens.size)
    (hC : single = false → Complete (.canonical (lensOf st.lens st.size.toNat))) :
    tableDoneW st single ≤ 13 * st.size.toNat + 11001 + (if st.role = .map then 257 + zbW (mapSizeFast st) else 0) := by
  have hu : st.size.toUSize.toNat = st.size.toNat := word_toUSize (by omega)
  unfold tableDoneW
  dsimp only
  have hnle : st.size.toUSize.toNat ≤ st.lens.size := by rw [hu]; exact hlens
  rw [dite_eq_left hnle]
  have hb : (if single then buildSingleW else buildFastW st.lens st.size.toUSize hnle) ≤ 13 * st.size.toNat + 11000 := by
    cases hs : single with
    | true => show buildSingleW ≤ _; unfold buildSingleW; omega
    | false =>
      show buildFastW st.lens st.size.toUSize hnle ≤ _
      have hC' := hC hs
      rw [← hu] at hC'
      have h1 := buildFastW_le (hn := hnle) (by omega) hC'
      have h2 := longCount_le (lensOf st.lens st.size.toUSize.toNat)
      rw [lensOf_length hnle, hu] at h2
      rw [hu] at h1
      omega
  cases hr : st.role with
  | map =>
    simp only [↓reduceIte]
    unfold fitsW
    omega
  | type => simp only [reduceCtorEq, ↓reduceIte]; omega
  | count => simp only [reduceCtorEq, ↓reduceIte]; omega
  | codes => simp only [reduceCtorEq, ↓reduceIte]; omega

/-- The code length code's table's work, with its lengths complete when it has two symbols or more. -/
theorem clTableW_le {st : Hd} (hC : st.clNz ≠ 1 → Complete (.canonical (lensOf st.clLens 18))) : clTableW st ≤ 11234 := by
  have h18 : (USize.ofNat 18).toNat = 18 := usize_ofNat' (by decide)
  unfold clTableW
  by_cases h1 : st.clNz = 1
  · rw [ite_eq_left h1]
    unfold buildSingleW
    omega
  · rw [ite_eq_right h1]
    by_cases hn : (USize.ofNat 18).toNat ≤ st.clLens.size
    · rw [dite_eq_left hn]
      have hC' := hC h1
      rw [← h18] at hC'
      have b1 := buildFastW_le (hn := hn) (by rw [h18]; decide) hC'
      have b2 := longCount_le (lensOf st.clLens (USize.ofNat 18).toNat)
      rw [lensOf_length hn, h18] at b2
      rw [h18] at b1
      omega
    · rw [dite_eq_right hn]
      omega

/-! ### The inverse move-to-front transform -/

/-- How many values are not 0. -/
def nzL (l : List Nat) : Nat := l.countP (· != 0)

/-- What the transform's work is bounded by on a context map of `S` values for `ntrees` trees: by the values that are not
0, or, when all values are the same, by the number of trees. -/
def imtfB (S ntrees : Nat) (vals : List Nat) : Nat :=
  if vals = List.replicate vals.length (vals.headD 0) then min (8 * S + 515 * nzL vals + 1) (8 * S + 515 * ntrees + 8)
  else 8 * S + 515 * nzL vals + 1

theorem imtfB_le (S ntrees : Nat) (vals : List Nat) : imtfB S ntrees vals ≤ 8 * S + 515 * nzL vals + 1 := by
  unfold imtfB
  split <;> omega

theorem nzL_le (l : List Nat) : nzL l ≤ l.length := List.countP_le_length

theorem nzL_append (a b : List Nat) : nzL (a ++ b) = nzL a + nzL b := List.countP_append

theorem nzL_replicate (n v : Nat) : nzL (List.replicate n v) ≤ n := by
  have := nzL_le (List.replicate n v)
  rwa [List.length_replicate] at this

/-- A map's values, from its bytes. -/
theorem MapOk.vals_eq {b : ByteArray} {l : List Nat} {S n : Nat} (h : MapOk b l S n) :
    l = (List.range S).map fun j => (b.data[j]?.getD 0).toNat := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < S
  · rw [h.at_ i hi, List.getElem?_map, List.getElem?_range hi]
    rfl
  · rw [List.getElem?_eq_none (by rw [h.length]; omega), List.getElem?_eq_none (by simp; omega)]

/-- The transform's work on a context map's bytes. -/
theorem imtfGoW_map {m fill : ByteArray} {vals : List Nat} {S ntrees : Nat} (h : MapOk fill vals S ntrees) (hS : S ≤ 16384) :
    imtfGoW m fill 0 (UInt64.ofNat fill.size) ≤ imtfB S ntrees vals := by
  have hsz : fill.size = S := h.sz
  have hn : (UInt64.ofNat fill.size).toNat = S := by rw [hsz]; exact u64_lit (by omega)
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hnz : nzC fill 0 S = nzL vals := by
    rw [h.vals_eq]
    unfold nzC nzL
    rw [List.countP_map]
    apply List.countP_congr
    intro j _
    simp only [Function.comp, Nat.zero_add]
    generalize fill.data[j]?.getD 0 = x
    have : x.toNat = 0 ↔ x = 0 := ⟨fun e => UInt8.toNat_inj.mp (by rw [e]; rfl), fun e => by rw [e]; rfl⟩
    simp only [bne_iff_ne, ne_eq, this]
  have hgen : imtfGoW m fill 0 (UInt64.ofNat fill.size) ≤ 8 * S + 515 * nzL vals + 1 := by
    have := imtfGoW_le S m fill 0 (UInt64.ofNat fill.size) hn (by rw [h0]; omega) (by rw [h0, hsz]; omega)
    rw [h0, hnz] at this
    exact this
  unfold imtfB
  split
  · rename_i hc
    refine Nat.le_min.mpr ⟨hgen, ?_⟩
    have hlen : vals.length = S := h.length
    by_cases hS0 : S = 0
    · have := nzL_le vals
      have : nzL vals = 0 := by omega
      omega
    generalize hv : vals.headD 0 = v at hc
    have hmem : v ∈ vals := by
      rw [hc]
      exact List.mem_replicate.mpr ⟨by omega, rfl⟩
    have hvt : v < ntrees := h.lt v hmem
    have hall : ∀ j, j < S → fill.data[0 + j]?.getD 0 = UInt8.ofNat v := by
      intro j hj
      have e := h.at_ j hj
      rw [hc, List.getElem?_replicate, ite_eq_left (by omega)] at e
      have e' : (fill.data[j]?.getD 0).toNat = v := (Option.some.inj e).symm
      rw [Nat.zero_add]
      apply UInt8.toNat_inj.mp
      rw [e', UInt8.toNat_ofNat']
      have := (fill.data[j]?.getD 0).toNat_lt
      omega
    have hv8 : (UInt8.ofNat v).toNat = v := by
      rw [UInt8.toNat_ofNat']
      have := (fill.data[0]?.getD 0).toNat_lt
      have e := hall 0 (by omega)
      have e2 := h.at_ 0 (by omega)
      rw [hc, List.getElem?_replicate, ite_eq_left (by omega)] at e2
      have e3 : (fill.data[0]?.getD 0).toNat = v := (Option.some.inj e2).symm
      omega
    by_cases hlt : v + 1 < S
    · have := imtfGoW_const (m := m) (out := fill) (i := 0) (n := UInt64.ofNat fill.size) (v := UInt8.ofNat v) hn
        (by rw [h0]; omega) (by rw [h0]; exact hall) (by rw [hv8]; exact hlt)
      rw [hv8] at this
      omega
    · have : nzL vals ≤ ntrees := by
        have := nzL_le vals
        omega
      have : 515 * nzL vals ≤ 515 * ntrees := Nat.mul_le_mul_left _ this
      omega
  · exact hgen

/-! ### The potential

On the header's places read in order. A number of block types or trees not yet read counts as 0, so the potential rises
by what that number brings when it is read. -/

/-- The rate at which a header's bits pay for its work: the most a bit pays for is the literal context map that a
literal category's number of block types brings, 960 for each type, when that number takes 11 bits. -/
def hdrRate : Nat := 22343

/-- A bound on the work of zero-filling `k` bytes (`zbW_le`). -/
def zb (k : Nat) : Nat := 5 * k + 66

/-- What a context map of `S` values costs besides its code and the values read: its zeros, its table's check, the values
a code gives without reading, the transform's rounds, and the check that every tree occurs. -/
def mapPre (S : Nat) : Nat := 15 * S + 2244

/-- What follows the second context map: the groups' steps, their arrays' zeros and the header's last step. -/
def afterD (nI tL tD : Nat) : Nat := 10 * tL + zb (4 * nI) + 11 + 10 * nI + zb (4 * tD) + 11 + 10 * tD + 11

/-- What follows the first context map. -/
def afterL (nI nD tL : Nat) : Nat := mapPre (4 * nD) + zb (4 * tL) + 1 + afterD nI tL 0

/-- What is still to do from the context modes on, with the numbers of block types known so far. -/
def beforeMaps (nL nI nD : Nat) : Nat := 10 + mapPre (64 * nL) + 1 + afterL nI nD 0

/-- The potential once category `i` is known to have `n` block types. -/
def catPot (g : Gh) : Cat → Nat → Nat
  | .L, n => beforeMaps n 0 0
  | .I, n => beforeMaps g.m.literal.n n 0
  | .D, n => beforeMaps g.m.literal.n g.m.insertCopy.n n

/-- What a context map's last step does to the next group's array. -/
def mapFin (g : Gh) (isL : Bool) : Nat := if isL then 1 else zb (4 * g.treesL) + 1

/-- What follows a context map of `t` trees. -/
def mapAfter (g : Gh) (isL : Bool) (t : Nat) : Nat :=
  if isL then afterL g.m.insertCopy.n g.m.distance.n t else afterD g.m.insertCopy.n g.treesL t

/-- From a context map's last bit on, besides the transform. -/
def imtfTail (g : Gh) (isL : Bool) (t : Nat) : Nat := 1881 + mapSize g isL + mapFin g isL + mapAfter g isL t

/-- From a context map's values on, for whatever its code. -/
def mapOwner (g : Gh) (isL : Bool) (t : Nat) : Nat := 39 + 9 * mapSize g isL + imtfTail g isL t + 515 * t

/-- From a group's next code on. -/
def codesPot (g : Gh) : CK → Nat → Nat
  | .L, left => afterD g.m.insertCopy.n left g.treesD
  | .I, left => 10 * left + zb (4 * g.treesD) + 22 + 10 * g.treesD
  | .D, left => 10 * left + 11

/-- What a code's table's step does for its owner: for a context map, the table's check and the map's zeros. -/
def ownerX (g : Gh) : Owner → Nat
  | .map isL _ _ => 258 + zb (mapSize g isL)
  | _ => 0

/-- From where a code's owner goes on to. -/
def ownerPot (g : Gh) : Owner → Nat
  | .type i n => catPot g i n
  | .count i n _ => catPot g i n
  | .map isL t _ => mapOwner g isL t
  | .codes k _ left => codesPot g k left

/-- The potential of a header's place. A code's lengths carry its tables' work, prepaid by its first two bits. -/
def hpot (g : Gh) : HPhase → Nat
  | .cat i => catPot g i 0
  | .code o _ => ownerX g o + ownerPot g o
  | .clens o n _ _ _ => 30 * n + 22579 + ownerX g o + ownerPot g o
  | .syms o n _ ls => 12 * (n - ls.lens.length) + 13 * n + 11011 + ownerX g o + ownerPot g o
  | .first i n _ _ => catPot g i n
  | .np => beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n
  | .modes _ _ => beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n
  | .trees isL => mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0
  | .rlemax isL t => 258 + zb (mapSize g isL) + mapOwner g isL t
  | .vals isL t r code done left =>
    if left = 0 then 10 + imtfTail g isL t + imtfB (mapSize g isL) t done
    else match runOf r code with
      | some v => left + 31 + imtfTail g isL t + imtfB (mapSize g isL) t (done ++ List.replicate left v)
      | none => 11 + imtfTail g isL t + 8 * mapSize g isL + 515 * nzL done
  | .imtf isL t vals => imtfTail g isL t + imtfB (mapSize g isL) t vals
  | .codes k _ left => codesPot g k left

/-- A bound on a header step's work, with its refill, by where it goes. -/
def hcost (g : Gh) : HPhase → HPhase → Nat
  | .cat _, _ => 10
  | .code _ _, .clens .. => 166
  | .code o n, _ => 18 * n + 11077 + ownerX g o
  | .clens _ n _ _ _, .syms .. => 5 * n + 11568
  | .clens .., _ => 10
  | .syms _ _ _ ls, .syms _ _ _ ls' => ls'.lens.length - ls.lens.length + 11
  | .syms o n _ _, _ => 13 * n + 11011 + ownerX g o
  | .first .., _ => 268
  | .np, _ => 1356
  | .modes .., _ => 10
  | .trees _, .rlemax .. => 10
  | .trees isL, _ => 10 + zb (mapSize g isL) + mapFin g isL
  | .rlemax .., _ => 10
  | .vals _ _ r code _ left, _ => if left = 0 then 10 else match runOf r code with | some _ => left + 11 | none => 10
  | .imtf isL t vals, _ => 1871 + mapSize g isL + mapFin g isL + imtfB (mapSize g isL) t vals
  | .codes _ _ (_ + 1), _ => 10
  | .codes .L _ 0, _ => zb (4 * g.m.insertCopy.n) + 11
  | .codes .I _ 0, _ => zb (4 * g.treesD) + 11
  | .codes .D _ 0, _ => 11

/-- A prefix code's alphabet, at the places reading one. -/
def psize : HPhase → Nat
  | .code _ n => n
  | .clens _ n .. => n
  | .syms _ n .. => n
  | _ => 0

/-! ### What reads pay -/

theorem hdrRate_eq : hdrRate = 22343 := rfl

private theorem pow_pay : ∀ n, n < 8 → 1 ≤ n → 1920 * 2 ^ n + 10 ≤ 22343 * (4 + n) := by decide

/-- A number of block types or trees pays for 960 for each, and 10. -/
theorem varLen_pay {bs b : List Bool} {v : Nat} (h : readVarLen bs = some (v, b)) :
    960 * v + 10 + hdrRate * b.length ≤ hdrRate * bs.length := by
  rw [hdrRate_eq]
  unfold readVarLen at h
  cases h1 : readInt 1 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨first, bs1⟩ := p
    have l1 := readInt_length _ _ _ _ h1
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
    · cases h2 : readInt 3 bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨n, bs2⟩ := q
        have l2 := readInt_length _ _ _ _ h2
        have n8 : n < 8 := readInt_lt _ _ _ _ h2
        rw [h2] at h
        dsimp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          omega
        · rename_i hn0
          cases h3 : readInt n bs2 with
          | none => rw [h3] at h; simp at h
          | some r =>
            obtain ⟨x, bs3⟩ := r
            have l3 := readInt_length _ _ _ _ h3
            have x8 := readInt_lt _ _ _ _ h3
            rw [h3] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [Nat.shiftLeft_eq, Nat.one_mul]
            have key := pow_pay n n8 (by omega)
            have hm : 22343 * bs.length = 22343 * bs3.length + 22343 * (4 + n) := by
              rw [← Nat.mul_add]
              congr 1
              omega
            rw [hm]
            generalize 2 ^ n = P at x8 key
            omega

theorem catPot_le (g : Gh) (i : Cat) (v : Nat) : catPot g i v ≤ catPot g i 0 + 960 * v := by
  cases i <;> simp only [catPot, beforeMaps, afterL, afterD, mapPre, zb] <;> omega

theorem mapAfter_le (g : Gh) (isL : Bool) (v : Nat) : mapAfter g isL v ≤ mapAfter g isL 0 + 30 * v := by
  cases isL <;> simp only [mapAfter, afterL, afterD, zb, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem hpot_catNext (g : Gh) (i : Cat) (c : BlockCategory) : hpot (g.setCat i c) (catNextPhase i) = catPot g i c.n := by
  cases i <;> rfl

theorem hpot_mapNext (g : Gh) (isL : Bool) (t : Nat) (m : List Nat) :
    hpot (g.setMap isL t m) (mapNextPhase (g.setMap isL t m) isL) = mapAfter g isL t := by
  cases isL with
  | true =>
    simp only [Gh.setMap, mapNextPhase, hpot, mapSize, mapFin, mapAfter, afterL, distanceContextMapSize, Bool.false_eq_true,
      ↓reduceIte]
    omega
  | false => rfl

theorem imtfB_rep (S t n v : Nat) : imtfB S t (List.replicate n v) ≤ 8 * S + 515 * t + 8 := by
  unfold imtfB
  have hc : List.replicate n v = List.replicate (List.replicate n v).length ((List.replicate n v).headD 0) := by
    cases n with
    | zero => rfl
    | succ n => rw [List.length_replicate]; rfl
  rw [ite_eq_left hc]
  exact Nat.min_le_right _ _

theorem hpot_owner_le (g : Gh) (o : Owner) (c : PrefixCode) : hpot g (ownerPlace g o c) ≤ ownerPot g o := by
  cases o with
  | type i n => exact Nat.le_of_eq (by simp only [ownerPlace, hpot, ownerX, ownerPot, Nat.zero_add])
  | count i n tc => exact Nat.le_refl _
  | codes k done left => exact Nat.le_refl _
  | map isL t r =>
    simp only [ownerPlace, hpot, ownerPot, mapOwner]
    split
    · have := imtfB_le (mapSize g isL) t []
      simp only [nzL, List.countP_nil] at this
      omega
    · cases runOf r c with
      | some v =>
        dsimp only
        have := imtfB_rep (mapSize g isL) t (mapSize g isL) v
        rw [List.nil_append]
        omega
      | none =>
        dsimp only
        simp only [nzL, List.countP_nil]
        omega

theorem hcost_code_owner (g : Gh) (o : Owner) (n : Nat) (c : PrefixCode) :
    hcost g (.code o n) (ownerPlace g o c) = 18 * n + 11077 + ownerX g o := by
  cases o <;> rfl

theorem hcost_syms_owner (g : Gh) (o : Owner) (n : Nat) (clc : PrefixCode) (ls : LengthState) (c : PrefixCode) :
    hcost g (.syms o n clc ls) (ownerPlace g o c) = 13 * n + 11011 + ownerX g o := by
  cases o <;> rfl

private theorem grow_aux (old e mult : Nat) (hm : mult = 4 ∨ mult = 8) :
    1 ≤ (if old = 0 then 3 + e else mult * (old - 2) + (3 + e)) - old := by
  rcases hm with rfl | rfl <;> split <;> omega

/-- A code length symbol adds at least one length. -/
theorem applyCodeLength_grow (ls : LengthState) (s e : Nat) :
    ∃ l, (applyCodeLength ls s e).lens = ls.lens ++ l ∧ 1 ≤ l.length := by
  unfold applyCodeLength
  split
  · exact ⟨[s], rfl, by simp⟩
  · dsimp only
    refine ⟨_, rfl, ?_⟩
    rw [List.length_replicate]
    exact grow_aux _ _ _ (by split <;> simp)

/-- A context map's symbol gives a value that is not 0 only on its own. -/
theorem mapSym_nz {rlemax : Nat} {code : PrefixCode} {bs b : List Bool} {x r : Nat} (h : mapSym rlemax code bs = some ((x, r), b)) :
    nzL (List.replicate r x) ≤ 1 := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    cases hc : contextMapValue rlemax p.1 with
    | some v =>
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact nzL_replicate 1 _
    | none =>
      rw [hc] at h
      dsimp only at h
      cases hi : readInt p.1 p.2 with
      | none => rw [hi] at h; cases h
      | some q =>
        rw [hi] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h
        have : nzL (List.replicate ((1 <<< p.1) + q.1) 0) = 0 :=
          List.countP_eq_zero.mpr fun a ha => by rw [(List.mem_replicate.mp ha).2]; decide
        omega

theorem hstage_pos (g : Gh) (p : HPhase) : 1 ≤ hstage g p := by
  cases p with
  | modes done n => cases n <;> simp only [hstage] <;> omega
  | codes k done n =>
    simp only [hstage]
    cases n with
    | succ => simp only [ckStage]; omega
    | zero => cases k <;> simp only [ckStage] <;> (repeat' split) <;> omega
  | clens o size order acc sum => cases order <;> simp only [hstage] <;> omega
  | _ => simp only [hstage] <;> omega

/-- A header step's work, as `hcost` bounds it, is paid for by the potential and the bits the step reads. -/
theorem hpay {g : Gh} {p : HPhase} {bs c : List Bool} {g' : Gh} {p' : HPhase} (hsz : psize p ≤ 704)
    (h : hStepP (g, p) bs = .next (g', p') c) :
    hcost g p p' + hpot g' p' + hdrRate * c.length ≤ hpot g p + hdrRate * bs.length := by
  rw [hdrRate_eq]
  cases p with
  | cat i =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.cat i) bs = _ from h)
    have hpay := varLen_pay e1
    rw [hdrRate_eq] at hpay
    have hle := catPot_le g i v
    split at e2 <;> cases e2
    · rw [hpot_catNext]
      show 10 + catPot g i v + _ ≤ catPot g i 0 + _
      omega
    · show 10 + (0 + catPot g i v) + _ ≤ catPot g i 0 + _
      omega
  | code o n =>
    obtain ⟨hv, b, e1, e2⟩ := readIn_next' (show hStep g (.code o n) bs = _ from h)
    have l1 := readInt_length _ _ _ _ e1
    have hn : n ≤ 704 := hsz
    have e0 : hpot g (.code o n) = ownerX g o + ownerPot g o := rfl
    rw [e0]
    split at e2
    · obtain ⟨cd, b', e3, e4⟩ := readIn_next' e2
      have l2 := faith_le (faith_simpleChain _ _) e3
      cases e4
      have hle := hpot_owner_le g o cd
      rw [hcost_code_owner]
      omega
    · cases e2
      show 166 + (30 * n + 22579 + ownerX g o + ownerPot g o) + _ ≤ _
      omega
  | clens o n order acc sum =>
    have e0 : hpot g (.clens o n order acc sum) = 30 * n + 22579 + ownerX g o + ownerPot g o := rfl
    have es : ∀ clc, hpot g (.syms o n clc ⟨[], 8, none⟩) = 12 * n + 13 * n + 11011 + ownerX g o + ownerPot g o :=
      fun _ => by show 12 * (n - 0) + _ + _ + _ + _ = _; rw [Nat.sub_zero]
    rw [e0]
    cases order with
    | nil =>
      have h' : (if (acc.filter (·.2 != 0)).length = 1 then ORes.next (g, HPhase.syms o n (codeLengthCode acc) ⟨[], 8, none⟩) bs
          else .bad) = .next (g', p') c := h
      split at h' <;> cases h'
      rw [es]
      show 5 * n + 11568 + _ + _ ≤ _
      omega
    | cons x rest =>
      obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.clens o n (x :: rest) acc sum) bs = _ from h)
      have hl := takes_one faith_readCodeLengthCodeLength rfl e1
      split at e2
      · cases e2
        show 10 + (30 * n + 22579 + ownerX g o + ownerPot g o) + _ ≤ _
        omega
      · split at e2
        · cases e2
          rw [es]
          show 5 * n + 11568 + _ + _ ≤ _
          omega
        · split at e2
          · cases e2
          · cases e2
            show 10 + (30 * n + 22579 + ownerX g o + ownerPot g o) + _ ≤ _
            omega
  | syms o n clc ls =>
    have e0 : hpot g (.syms o n clc ls) = 12 * (n - ls.lens.length) + 13 * n + 11011 + ownerX g o + ownerPot g o := rfl
    rw [e0]
    have h' : (if n < ls.lens.length then ORes.bad
        else if lengthSum ls.lens = 32768 then
          .next (g, ownerPlace g o (.canonical (ls.lens ++ List.replicate (n - ls.lens.length) 0))) bs
        else if ls.lens.length = n then .bad
        else readIn 18 (lenSym clc) bs fun v b =>
          if n < (applyCodeLength ls v.1 v.2).lens.length then .bad
          else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then .bad
          else .next (g, .syms o n clc (applyCodeLength ls v.1 v.2)) b) = .next (g', p') c := h
    split at h'
    · cases h'
    · split at h'
      · cases h'
        have hle := hpot_owner_le g o (.canonical (ls.lens ++ List.replicate (n - ls.lens.length) 0))
        rw [hcost_syms_owner]
        omega
      · split at h'
        · cases h'
        · obtain ⟨v, b, e1, e2⟩ := readIn_next' h'
          have l1 := faith_le (faith_lenSym clc) e1
          split at e2
          · cases e2
          · split at e2
            · cases e2
            · cases e2
              rename_i hle _
              obtain ⟨l, hl, hl1⟩ := applyCodeLength_grow ls v.1 v.2
              show (applyCodeLength ls v.1 v.2).lens.length - ls.lens.length + 11 +
                (12 * (n - (applyCodeLength ls v.1 v.2).lens.length) + 13 * n + 11011 + ownerX g o + ownerPot g o) + _ ≤ _
              rw [hl] at hle ⊢
              rw [List.length_append] at hle ⊢
              omega
  | first i n tc cc =>
    have hm := hStep_moves g (.first i n tc cc) bs _ _ h
    have hs := hstage_pos g' p'
    have h1 : hstage g (.first i n tc cc) = 1 := rfl
    rw [h1] at hm
    have hl : c.length + 1 ≤ bs.length := by
      rcases hm with hm | hm
      · exact hm
      · exact absurd hm (Nat.not_lt.mpr hs)
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.first i n tc cc) bs = _ from h)
    cases e2
    rw [hpot_catNext]
    show 268 + catPot g i n + _ ≤ catPot g i n + _
    omega
  | np =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g .np bs = _ from h)
    have l1 : b.length + 6 = bs.length := by
      unfold readNp at e1
      cases h1 : readInt 2 bs with
      | none => rw [h1] at e1; cases e1
      | some p =>
        rw [h1] at e1
        dsimp only [bind, Option.bind] at e1
        cases h2 : readInt 4 p.2 with
        | none => rw [h2] at e1; cases e1
        | some q =>
          rw [h2] at e1
          simp only [Option.some.injEq, Prod.mk.injEq] at e1
          obtain ⟨-, rfl⟩ := e1
          have := readInt_length _ _ _ _ h1
          have := readInt_length _ _ _ _ h2
          omega
    cases e2
    show 1356 + beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n + _ ≤ beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n + _
    omega
  | modes done left =>
    cases left with
    | zero =>
      cases h
      show 10 + (mapPre (64 * g.m.literal.n) + 1 + mapAfter _ true 0) + _ ≤ beforeMaps _ _ _ + _
      unfold beforeMaps mapAfter
      simp only [↓reduceIte]
      omega
    | succ n =>
      obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.modes done (n + 1)) bs = _ from h)
      have hl := takes_one (faith_readInt 2) rfl e1
      cases e2
      show 10 + beforeMaps _ _ _ + _ ≤ beforeMaps _ _ _ + _
      omega
  | trees isL =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.trees isL) bs = _ from h)
    have hpay := varLen_pay e1
    rw [hdrRate_eq] at hpay
    have hle := mapAfter_le g isL v
    have e0 : hpot g (.trees isL) = mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0 := rfl
    rw [e0]
    unfold mapPre
    split at e2 <;> cases e2
    · have e := hpot_mapNext g isL v (List.replicate (mapSize g isL) 0)
      have hc : hcost g (.trees isL) (mapNextPhase (g.setMap isL v (List.replicate (mapSize g isL) 0)) isL) =
          10 + zb (mapSize g isL) + mapFin g isL := by cases isL <;> rfl
      rw [hc, e]
      unfold zb
      omega
    · show 10 + (258 + zb (mapSize g isL) + (39 + 9 * mapSize g isL + (1881 + mapSize g isL + mapFin g isL + mapAfter g isL v) +
        515 * v)) + _ ≤ _
      unfold zb
      omega
  | rlemax isL t =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.rlemax isL t) bs = _ from h)
    have hl := takes_one faith_readRLEMAX rfl e1
    cases e2
    show 10 + (258 + zb (mapSize g isL) + mapOwner g isL t) + _ ≤ 258 + zb (mapSize g isL) + mapOwner g isL t + _
    omega
  | vals isL t r code done left =>
    rcases hStep_vals_next h with ⟨h0, e, rfl⟩ | ⟨h0, v, hr, e, rfl⟩ | ⟨h0, hr, h'⟩
    · cases e
      simp only [hcost, hpot, h0, ↓reduceIte]
      omega
    · cases e
      simp only [hcost, hpot, h0, hr, ↓reduceIte]
      omega
    · obtain ⟨v, b, e1, e2⟩ := readIn_next' h'
      have l1 := faith_le (faith_mapSym r code) e1
      have l2 : b.length ≠ bs.length := fun e => by
        have := (mapSym_noRead e1 e).1
        rw [hr] at this
        cases this
      have hnz := mapSym_nz e1
      have hnz2 := nzL_append done (List.replicate v.2 v.1)
      have hb := imtfB_le (mapSize g isL) t (done ++ List.replicate v.2 v.1)
      split at e2
      · cases e2
      · cases e2
        simp only [hcost, hpot, h0, hr, ↓reduceIte]
        split <;> omega
  | imtf isL t vals =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.imtf isL t vals) bs = _ from h)
    have l1 := faith_le (faith_readInt 1) e1
    generalize (if v = 0 then vals else inverseMoveToFront vals) = fin at e2
    split at e2
    · cases e2
      rw [hpot_mapNext]
      show 1871 + mapSize g isL + mapFin g isL + imtfB (mapSize g isL) t vals + mapAfter g isL t + _ ≤
        1881 + mapSize g isL + mapFin g isL + mapAfter g isL t + imtfB (mapSize g isL) t vals + _
      omega
    · cases e2
  | codes k done left =>
    cases left with
    | succ n =>
      cases h
      dsimp only
      cases k
      · show 10 + (0 + afterD _ n _) + _ ≤ afterD _ (n + 1) _ + _
        unfold afterD
        omega
      · show 10 + (0 + (10 * n + zb (4 * g.treesD) + 22 + 10 * g.treesD)) + _ ≤
          10 * (n + 1) + zb (4 * g.treesD) + 22 + 10 * g.treesD + _
        omega
      · show 10 + (0 + (10 * n + 11)) + _ ≤ 10 * (n + 1) + 11 + _
        omega
    | zero =>
      cases k with
      | L =>
        cases h
        dsimp only
        show zb (4 * g.m.insertCopy.n) + 11 + (10 * g.m.insertCopy.n + zb (4 * g.treesD) + 22 + 10 * g.treesD) + _ ≤
          afterD g.m.insertCopy.n 0 g.treesD + _
        unfold afterD
        omega
      | I =>
        cases h
        dsimp only
        show zb (4 * g.treesD) + 11 + (10 * g.treesD + 11) + _ ≤ 10 * 0 + zb (4 * g.treesD) + 22 + 10 * g.treesD + _
        omega
      | D => cases h

/-! ### The header machine's work, by where a step goes -/

/-- The tag of a state at a place. -/
def ptag : HPhase → HTag
  | .cat _ => .cat
  | .code .. => .code
  | .clens .. => .clens
  | .syms .. => .syms
  | .first .. => .first
  | .np => .np
  | .modes .. => .modes
  | .trees _ => .trees
  | .rlemax .. => .rlemax
  | .vals .. => .vals
  | .imtf .. => .imtf
  | .codes .. => .codes

theorem HRel.tag_eq {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) : st.tag = ptag p := by
  cases p
  case np => exact h.2.2
  all_goals exact h.2.2.1

theorem hcost_ge (g : Gh) (p p' : HPhase) : 10 ≤ hcost g p p' := by
  cases p with
  | code o n => cases p' <;> simp only [hcost] <;> omega
  | clens o n ord acc sum => cases p' <;> simp only [hcost] <;> omega
  | syms o n clc ls => cases p' <;> simp only [hcost] <;> omega
  | trees isL => cases p' <;> simp only [hcost] <;> omega
  | vals isL t r code done left =>
    simp only [hcost]
    split
    · omega
    · split <;> omega
  | imtf => simp only [hcost]; omega
  | codes k done left =>
    cases left with
    | succ => simp only [hcost]; omega
    | zero => cases k <;> simp only [hcost] <;> omega
  | _ => simp only [hcost]; omega

theorem hcost_code (g : Gh) (o : Owner) (n : Nat) (p' : HPhase) :
    hcost g (.code o n) p' = if ptag p' = .clens then 166 else 18 * n + 11077 + ownerX g o := by
  cases p' <;> rfl

theorem hcost_clens (g : Gh) (o : Owner) (n : Nat) (order : List Nat) (acc : List (Nat × Nat)) (sum : Nat) (p' : HPhase) :
    hcost g (.clens o n order acc sum) p' = if ptag p' = .syms then 5 * n + 11568 else 10 := by
  cases p' <;> rfl

theorem hcost_trees (g : Gh) (isL : Bool) (p' : HPhase) :
    hcost g (.trees isL) p' = if ptag p' = .rlemax then 10 else 10 + zb (mapSize g isL) + mapFin g isL := by
  cases p' <;> rfl

theorem hcost_syms_other (g : Gh) (o : Owner) (n : Nat) (clc : PrefixCode) (ls : LengthState) {p' : HPhase}
    (h : ptag p' ≠ .syms) : hcost g (.syms o n clc ls) p' = 13 * n + 11011 + ownerX g o := by
  cases p' <;> first | rfl | exact absurd rfl h

/-- Where a finished table's step goes, when it goes on. -/
theorem tableDone_tag {st : Hd} {s : Bool} {y : UInt64} (h : (tableDone st s y).status = .next) :
    (tableDone st s y).tag ≠ .clens ∧ (tableDone st s y).tag ≠ .syms := by
  have key : ∀ (x : Hd) (b : UInt64), (installTable x b).tag ≠ .clens ∧ (installTable x b).tag ≠ .syms := by
    intro x b
    unfold installTable
    split <;> exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
  unfold tableDone at h ⊢
  dsimp only at h ⊢
  by_cases hn : st.size.toUSize.toNat ≤ st.lens.size
  · rw [dite_eq_left hn] at h ⊢
    cases hr : st.role with
    | map =>
      simp only [hr] at h ⊢
      unfold mapTableDone at h ⊢
      generalize (if s = true then buildSingleFast ByteArray.empty y else buildFast ByteArray.empty st.lens st.size.toUSize hn) = t at h ⊢
      by_cases hf : fitsFast t 0 = true
      · rw [dite_eq_left hf]
        exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
      · rw [dite_eq_right hf] at h
        exact absurd h (fun e => HStatus.noConfusion e)
    | type | count | codes =>
      simp only [hr] at h ⊢
      cases s
      · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
        by_cases c : UInt64.ofNat st.d.arena.size + (planFast st.lens st.size.toUSize hn).bytes ≤ st.d.arenaMax
        · rw [ite_eq_left c]
          exact key _ _
        · rw [ite_eq_right c] at h
          exact absurd h (fun e => HStatus.noConfusion e)
      · simp only [↓reduceIte] at h ⊢
        by_cases c : UInt64.ofNat st.d.arena.size + 1024 ≤ st.d.arenaMax
        · rw [ite_eq_left c]
          exact key _ _
        · rw [ite_eq_right c] at h
          exact absurd h (fun e => HStatus.noConfusion e)
  · rw [dite_eq_right hn] at h
    exact absurd h (fun e => HStatus.noConfusion e)

theorem mapFin_ge {st : Hd} {g : Gh} {isL : Bool} (hi : st.isL = isL) (hu : Upto st.d g (mapIdx isL)) :
    mapFinishW st ≤ mapFin g isL := by
  unfold mapFinishW mapFin
  rw [hi]
  cases isL with
  | true => exact Nat.le_refl _
  | false =>
    obtain ⟨hT, _⟩ := hu.lmap (by decide)
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hT]
    have := zbW_le (4 * g.treesL)
    unfold zb
    omega

theorem wTrees {st : Hd} {g : Gh} {isL : Bool} {pos : USize} {g' : Gh} {p' : HPhase} (hrel : HRel st g (.trees isL))
    (hr : HRel (stepHTrees st pos) g' p') : stepHTreesW st + 9 ≤ hcost g (.trees isL) p' := by
  obtain ⟨hw, hu, ht, hi⟩ := hrel
  have htag := hr.tag_eq
  obtain ⟨hmf, -⟩ := mapSizeFast_eq (g := g) hi hu
  have hfin := mapFin_ge hi hu
  have hge := hcost_ge g (.trees isL) p'
  unfold stepHTreesW
  unfold stepHTrees at htag
  dsimp only at htag ⊢
  generalize varLenFast ⟨st.word, st.count⟩ = r at htag ⊢
  cases hs : r.status with
  | short => dsimp only; omega
  | bad => dsimp only; omega
  | ok =>
    rw [hs] at htag
    dsimp only at htag ⊢
    by_cases ha : r.a < 2
    · rw [ite_eq_left ha] at htag ⊢
      have hne : ptag p' ≠ .rlemax := by
        rw [← htag]
        unfold mapFinish
        split <;> exact fun e => HTag.noConfusion e
      rw [hcost_trees, ite_eq_right hne, hmf]
      have := zbW_le (mapSize g isL)
      unfold zb
      omega
    · rw [ite_eq_right ha]
      omega

theorem wImtf {st : Hd} {g : Gh} {isL : Bool} {t : Nat} {vals : List Nat} {p' : HPhase} (hrel : HRel st g (.imtf isL t vals)) :
    stepHImtfW st + 9 ≤ hcost g (.imtf isL t vals) p' := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩ := hrel
  obtain ⟨hmf, hml⟩ := mapSizeFast_eq (g := g) hi hu
  have hfin := mapFin_ge hi hu
  have hg := imtfGoW_map (m := mtfInitLut) hm hml
  have hsz : st.fill.size = mapSize g isL := hm.sz
  have hu1 : (UInt64.ofNat st.fill.size).toNat = mapSize g isL := by rw [hsz]; exact u64_lit (by omega)
  have hz := zbW_le 256
  unfold stepHImtfW
  show _ ≤ 1871 + mapSize g isL + mapFin g isL + imtfB (mapSize g isL) t vals
  split
  · dsimp only
    unfold allOccurW
    rw [hu1, hn]
    split <;> omega
  · omega

theorem wCodes {st : Hd} {g : Gh} {k : CK} {done : List PrefixCode} {left : Nat} {p' : HPhase} (hrel : HRel st g (.codes k done left)) :
    stepHCodesW st + 9 ≤ hcost g (.codes k done left) p' := by
  obtain ⟨hw, hu, ht, hck, hidx, hleft, hsum, h256, hpart⟩ := hrel
  have hge := hcost_ge g (.codes k done left) p'
  unfold stepHCodesW
  cases left with
  | succ n =>
    have hne : st.left ≠ 0 := fun e => by rw [e] at hleft; exact Nat.succ_ne_zero _ hleft.symm
    rw [ite_eq_right hne]
    omega
  | zero =>
    have he : st.left = 0 := UInt64.toNat_inj.mp (by rw [hleft]; rfl)
    rw [ite_eq_left he]
    unfold ckFinishW
    rw [hck]
    cases k with
    | L =>
      have hI : st.d.nI.toNat = g.m.insertCopy.n := (hu.cat .I (by show 1 < 7; decide)).n
      show zbW (4 * st.d.nI.toNat) + 1 + 1 + 9 ≤ zb (4 * g.m.insertCopy.n) + 11
      rw [hI]
      have := zbW_le (4 * g.m.insertCopy.n)
      unfold zb
      omega
    | I =>
      obtain ⟨hT, _⟩ := hu.dmap (by show 6 < 8; decide)
      show zbW (4 * st.d.treesD.toNat) + 1 + 1 + 9 ≤ zb (4 * g.treesD) + 11
      rw [hT]
      have := zbW_le (4 * g.treesD)
      unfold zb
      omega
    | D => show 1 + 1 + 9 ≤ 11; omega

theorem wNp {st : Hd} {g : Gh} {p' : HPhase} (hrel : HRel st g .np) : stepHNpW st + 9 ≤ hcost g .np p' := by
  obtain ⟨hw, hu, ht⟩ := hrel
  have hL := hu.cat .L (by show 0 < 3; decide)
  have h1 : st.d.nL.toNat ≤ 256 := by
    show (st.d.nOf .L).toNat ≤ 256
    rw [hL.n]
    exact hL.wf.2.1
  have := zbW_le st.d.nL.toNat
  unfold stepHNpW
  show _ ≤ 1356
  split <;> omega

/-- A context map's values: the run a code gives without reading is written only when the code reads nothing. -/
theorem valsW_shape (st : Hd) (pos : USize) : stepHValsW st ≤ 1 ∨ ((stepHVals st pos).word = st.word ∧
    (stepHVals st pos).count = st.count ∧ (stepHVals st pos).pos = pos ∧ stepHValsW st ≤ st.left.toNat + 2) := by
  unfold stepHValsW stepHVals
  dsimp only
  by_cases hl : st.left = 0
  · rw [ite_eq_left hl]
    exact Or.inl (Nat.le_refl _)
  · rw [ite_eq_right hl, ite_eq_right hl]
    generalize mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ = r
    cases r.status with
    | short => exact Or.inl (Nat.le_refl _)
    | bad => exact Or.inl (Nat.le_refl _)
    | ok =>
      dsimp only
      by_cases h1 : st.left < r.b
      · rw [ite_eq_left h1]
        exact Or.inl (Nat.le_refl _)
      · rw [ite_eq_right h1, ite_eq_right h1]
        by_cases h2 : r.count = st.count
        · rw [ite_eq_left h2, ite_eq_left h2]
          by_cases h3 : r.a = 0
          · rw [ite_eq_left h3]
            exact Or.inl (Nat.le_refl _)
          · rw [ite_eq_right h3, ite_eq_right h3]
            exact Or.inr ⟨rfl, rfl, rfl, Nat.le_refl _⟩
        · rw [ite_eq_right h2]
          exact Or.inl (Nat.le_refl _)

theorem wVals {st : Hd} {g : Gh} {isL : Bool} {t r : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} {pos : USize}
    {g' : Gh} {p' : HPhase} {a : ByteArray} {stop : USize} {F : List Bool} (hrel : HRel st g (.vals isL t r code done left))
    (hj : hStepP (g, .vals isL t r code done left) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepHVals st pos).word (stepHVals st pos).count a (stepHVals st pos).pos stop F)) :
    stepHValsW st + 9 ≤ hcost g (.vals isL t r code done left) p' := by
  have hleft : st.left.toNat = left := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hge := hcost_ge g (.vals isL t r code done left) p'
  rcases valsW_shape st pos with hW | ⟨e1, e2, e3, hW⟩
  · omega
  · rw [e1, e2, e3] at hj
    have hc : hcost g (.vals isL t r code done left) p' =
        if left = 0 then 10 else match runOf r code with | some _ => left + 11 | none => 10 := rfl
    rw [hc]
    by_cases h0 : left = 0
    · rw [ite_eq_left h0] at hc ⊢
      have := valsW_shape st pos
      unfold stepHValsW at hW ⊢
      have hl : st.left = 0 := UInt64.toNat_inj.mp (by rw [hleft, h0]; rfl)
      rw [ite_eq_left hl]
      omega
    · rw [ite_eq_right h0]
      cases hr : runOf r code with
      | some v =>
        show stepHValsW st + 9 ≤ left + 11
        omega
      | none =>
        exfalso
        rcases hStep_vals_next hj with ⟨h0', _, _⟩ | ⟨_, v, hv, _, _⟩ | ⟨_, _, h'⟩
        · exact h0 h0'
        · rw [hr] at hv; cases hv
        · obtain ⟨v, b, e4, e5⟩ := readIn_next' h'
          split at e5
          · cases e5
          · cases e5
            have := (mapSym_noRead e4 rfl).1
            rw [hr] at this
            cases this

/-- What a table's step does for its owner, against `ownerX`. -/
theorem ownerX_ge {st : Hd} {g : Gh} {n : Nat} {o : Owner} (ho : OwnerRel st g n o) (hu : Upto st.d g (ownerStage o)) :
    (if st.role = .map then 257 + zbW (mapSizeFast st) else 0) ≤ ownerX g o := by
  cases o with
  | type i k => rw [ho.1]; simp
  | count i k tc => rw [ho.1]; simp
  | codes k done left => rw [ho.1]; simp
  | map isL t r =>
    obtain ⟨hr, hi, _⟩ := ho
    obtain ⟨hmf, _⟩ := mapSizeFast_eq (g := g) hi hu
    rw [hr, hmf]
    have := zbW_le (mapSize g isL)
    simp only [↓reduceIte, ownerX, zb]
    omega

theorem writeSimple_size (t : ByteArray) (r : Rd) : (writeSimple t r).size = t.size := by
  unfold writeSimple setLen
  split
  · rw [size_setU, size_setU]
  · split
    · rw [size_setU, size_setU, size_setU]
    · split
      · rw [size_setU, size_setU, size_setU, size_setU]
      · rw [size_setU, size_setU, size_setU, size_setU]

theorem wCode {st : Hd} {g : Gh} {o : Owner} {n : Nat} {pos : USize} {g' : Gh} {p' : HPhase} (hrel : HRel st g (.code o n))
    (hn : (stepHCode st pos).status = .next) (hr : HRel (stepHCode st pos) g' p') :
    stepHCodeW st pos + 9 ≤ hcost g (.code o n) p' := by
  obtain ⟨hw, hu, ht, hs, ho⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have htag := hr.tag_eq
  have hge := hcost_ge g (.code o n) p'
  have hX := ownerX_ge ho hu
  unfold stepHCodeW
  unfold stepHCode at htag hn
  dsimp only at htag hn ⊢
  by_cases h2 : 2 ≤ st.count
  · rw [ite_eq_left h2] at htag hn ⊢
    by_cases h1 : (BitBuffer.mk st.word st.count).peek 2 = 1
    · rw [ite_eq_left h1] at htag hn ⊢
      have hcomp := simple_complete hw (by omega) h2 h1
      generalize simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) = r at htag hn hcomp ⊢
      cases hsr : r.status with
      | short => dsimp only; omega
      | bad => dsimp only; omega
      | ok =>
        rw [hsr] at htag hn
        dsimp only at htag hn ⊢
        have hnc : ptag p' ≠ .clens := by rw [← htag]; exact (tableDone_tag hn).1
        have hsz : st.size.toNat ≤ (writeSimple (zeroBytes st.size.toNat) r).size := by
          rw [writeSimple_size, zeroBytes_size (by omega)]
          exact Nat.le_refl _
        have hT := tableDoneW_le (st := { st with
            word := r.word, count := r.count, pos := pos, status := .next
            lens := writeSimple (zeroBytes st.size.toNat) r }) (single := r.e == 0) (by show st.size.toNat ≤ 704; omega) hsz
          (fun hsg => hcomp hsr (fun e => by
            have : r.e = 0 := UInt64.toNat_inj.mp e
            rw [this] at hsg
            cases hsg))
        have hz := zbW_le st.size.toNat
        rw [hcost_code, ite_eq_right hnc]
        have hT' : tableDoneW { st with
            word := r.word, count := r.count, pos := pos, status := .next
            lens := writeSimple (zeroBytes st.size.toNat) r } (r.e == 0) ≤
            13 * st.size.toNat + 11001 + (if st.role = .map then 257 + zbW (mapSizeFast st) else 0) := hT
        omega
    · rw [ite_eq_right h1] at htag ⊢
      have hc : ptag p' = .clens := htag.symm
      rw [hcost_code, ite_eq_left hc]
      have := zbW_le 18
      omega
  · rw [ite_eq_right h2]
    omega

theorem clFinish_tag {st : Hd} (h : (clFinish st).status = .next) : (clFinish st).tag = .syms := by
  unfold clFinish at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · rename_i hf
    rw [dite_eq_right hf] at h
    exact absurd h (fun e => HStatus.noConfusion e)

theorem clFinishW_le {st : Hd} (hC : st.clNz ≠ 1 → Complete (.canonical (lensOf st.clLens 18))) :
    clFinishW st ≤ 5 * st.size.toNat + 11558 := by
  unfold clFinishW fitsW
  have := clTableW_le hC
  have := zbW_le st.size.toNat
  omega

theorem wClens {st : Hd} {g : Gh} {o : Owner} {n : Nat} {order : List Nat} {acc : List (Nat × Nat)} {sum : Nat} {pos : USize}
    {g' : Gh} {p' : HPhase} (hrel : HRel st g (.clens o n order acc sum)) (hn : (stepHClens st pos).status = .next)
    (hr : HRel (stepHClens st pos) g' p') : stepHClensW st pos + 9 ≤ hcost g (.clens o n order acc sum) p' := by
  obtain ⟨hw, hu, ht, hs, ho, hc⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have htag := hr.tag_eq
  have hge := hcost_ge g (.clens o n order acc sum) p'
  unfold stepHClensW
  unfold stepHClens at htag hn
  dsimp only at htag hn ⊢
  by_cases h18 : st.clIdx = 18
  · rw [ite_eq_left h18] at htag hn ⊢
    by_cases hnz : st.clNz = 1
    · rw [ite_eq_left hnz] at htag hn ⊢
      have hsy : ptag p' = .syms := by rw [← htag]; exact clFinish_tag hn
      rw [hcost_clens, ite_eq_left hsy]
      have := clFinishW_le (st := { st with pos := pos, status := .next }) (fun h => absurd hnz h)
      have e : ({ st with pos := pos, status := .next } : Hd).size = st.size := rfl
      rw [e] at this
      omega
    · rw [ite_eq_right hnz]
      omega
  · rw [ite_eq_right h18] at htag hn ⊢
    have hcomp := clens_complete hw hc h18
    generalize cclFast ⟨st.word, st.count⟩ = r at htag hn hcomp ⊢
    cases hsr : r.status with
    | short => dsimp only; omega
    | bad => dsimp only; omega
    | ok =>
      rw [hsr] at htag hn
      dsimp only at htag hn ⊢
      by_cases h0 : r.a = 0
      · rw [ite_eq_left h0]
        omega
      · rw [ite_eq_right h0] at htag hn ⊢
        by_cases h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32
        · rw [ite_eq_left h32] at htag hn ⊢
          have hsy : ptag p' = .syms := by rw [← htag]; exact clFinish_tag hn
          rw [hcost_clens, ite_eq_left hsy]
          have := clFinishW_le (st := { st with
              word := r.word, count := r.count, pos := pos, status := .next
              clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
              clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 })
            (fun _ => hcomp hsr h0 h32)
          have e : ({ st with
              word := r.word, count := r.count, pos := pos, status := .next
              clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
              clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 } : Hd).size = st.size := rfl
          rw [e] at this
          omega
        · rw [ite_eq_right h32]
          omega

/-- A code's lengths only grow while it stays at its lengths. -/
theorem syms_grow {g : Gh} {o : Owner} {n : Nat} {clc : PrefixCode} {ls : LengthState} {bs c : List Bool} {g' : Gh} {o' : Owner}
    {n' : Nat} {clc' : PrefixCode} {ls' : LengthState} (h : hStepP (g, .syms o n clc ls) bs = .next (g', .syms o' n' clc' ls') c) :
    ls.lens.length < ls'.lens.length := by
  have h' : (if n < ls.lens.length then ORes.bad
      else if lengthSum ls.lens = 32768 then
        .next (g, ownerPlace g o (.canonical (ls.lens ++ List.replicate (n - ls.lens.length) 0))) bs
      else if ls.lens.length = n then .bad
      else readIn 18 (lenSym clc) bs fun v b =>
        if n < (applyCodeLength ls v.1 v.2).lens.length then .bad
        else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then .bad
        else .next (g, .syms o n clc (applyCodeLength ls v.1 v.2)) b) = .next (g', .syms o' n' clc' ls') c := h
  split at h'
  · cases h'
  · split at h'
    · cases o <;> cases h'
    · split at h'
      · cases h'
      · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
        split at e2
        · cases e2
        · split at e2
          · cases e2
          · cases e2
            obtain ⟨l, hl, hl1⟩ := applyCodeLength_grow ls v.1 v.2
            rw [hl, List.length_append]
            omega

/-- An index that grew by an addition grew by what was added. -/
private theorem add_grew {a d : UInt64} {m : Nat} (h : (a + d).toNat = m) (hm : a.toNat < m) : d.toNat = m - a.toNat := by
  rw [UInt64.toNat_add] at h
  have h1 := a.toNat_lt
  have h2 := d.toNat_lt
  generalize (2 : Nat) ^ 64 = M at h h1 h2
  by_cases hov : a.toNat + d.toNat < M
  · rw [Nat.mod_eq_of_lt hov] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem wSyms {st : Hd} {g : Gh} {o : Owner} {n : Nat} {clc : PrefixCode} {ls : LengthState} {pos : USize} {g' : Gh} {p' : HPhase}
    {bs c : List Bool} (hrel : HRel st g (.syms o n clc ls)) (hn : (stepHSyms st pos).status = .next)
    (hr : HRel (stepHSyms st pos) g' p') (hj : hStepP (g, .syms o n clc ls) bs = .next (g', p') c) :
    stepHSymsW st pos + 9 ≤ hcost g (.syms o n clc ls) p' := by
  obtain ⟨hw, hu, ht, hs, ho, hy⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hge := hcost_ge g (.syms o n clc ls) p'
  have hX := ownerX_ge ho hu
  unfold stepHSymsW
  unfold stepHSyms at hr hn
  by_cases hsum : st.symSum = 32768
  · rw [ite_eq_left hsum] at hr hn ⊢
    have hns : ptag p' ≠ .syms := by rw [← hr.tag_eq]; exact (tableDone_tag hn).2
    rw [hcost_syms_other g o n clc ls hns]
    have hC : Complete (.canonical (lensOf st.lens st.size.toNat)) := by
      rw [hs1, lens_full hy.sz hy.le hy.at_ hy.zero]
      refine ⟨fun l hl => ?_, ?_⟩
      · rcases List.mem_append.mp hl with h | h
        · exact hy.small l h
        · rw [(List.mem_replicate.mp h).2]
          omega
      · rw [lengthSum_append, lengthSum_replicate_zero, Nat.add_zero, ← hy.sumOk, hsum]
        rfl
    have hT := tableDoneW_le (st := { st with pos := pos, status := .next }) (single := false) (show st.size.toNat ≤ 704 by omega)
      (show st.size.toNat ≤ st.lens.size by rw [hy.sz, hs1]; exact Nat.le_refl _) (fun _ => hC)
    have hT' : tableDoneW { st with pos := pos, status := .next } false ≤
        13 * st.size.toNat + 11001 + (if st.role = .map then 257 + zbW (mapSizeFast st) else 0) := hT
    omega
  · rw [ite_eq_right hsum] at hr hn ⊢
    by_cases hln : st.ln = st.size
    · rw [ite_eq_left hln]
      omega
    · rw [ite_eq_right hln] at hr hn ⊢
      dsimp only at hr hn ⊢
      generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at hr hn ⊢
      cases hsr : r.status with
      | short => dsimp only; omega
      | bad => dsimp only; omega
      | ok =>
        rw [hsr] at hr hn
        dsimp only at hr hn ⊢
        by_cases h16 : r.a < 16
        · rw [ite_eq_left h16]
          omega
        · rw [ite_eq_right h16] at hr hn ⊢
          generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hr hn ⊢
          generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hr hn ⊢
          generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at hr hn ⊢
          by_cases hover : st.size < st.ln + (new - old)
          · rw [ite_eq_left hover]
            omega
          · rw [ite_eq_right hover] at hr hn ⊢
            generalize (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
              else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))) = sum at hr hn ⊢
            by_cases hbig : 32768 < sum
            · rw [ite_eq_left hbig] at hn
              exact absurd hn (fun e => HStatus.noConfusion e)
            · rw [ite_eq_right hbig] at hr ⊢
              have htg : ptag p' = .syms := by rw [← hr.tag_eq]; exact ht
              cases p' with
              | syms o' n' clc' ls' =>
                obtain ⟨_, _, _, _, _, hy'⟩ := hr
                have hg := syms_grow hj
                have hl := hy.ln
                have key := add_grew hy'.ln (by rw [hl]; exact hg)
                rw [hl] at key
                show _ + 2 + 9 ≤ ls'.lens.length - ls.lens.length + 11
                omega
              | _ => cases htg

/-- A header step's work, once the buffer is refilled, by where it goes. -/
theorem stepAtHW_cost {st : Hd} {g : Gh} {p : HPhase} {pos : USize} {g' : Gh} {p' : HPhase} {a : ByteArray} {stop : USize}
    {F : List Bool} (hrel : HRel st g p) (hn : (stepAtH st pos).status = .next) (hr : HRel (stepAtH st pos) g' p')
    (hj : hStepP (g, p) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepAtH st pos).word (stepAtH st pos).count a (stepAtH st pos).pos stop F)) :
    stepAtHW st pos + 9 ≤ hcost g p p' := by
  have htag := hrel.tag_eq
  have hge := hcost_ge g p p'
  cases p with
  | cat i =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | code o n =>
    have e1 : stepAtH st pos = stepHCode st pos := by unfold stepAtH; rw [htag] <;> rfl
    have e2 : stepAtHW st pos = stepHCodeW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wCode hrel hn hr
  | clens o n order acc sum =>
    have e1 : stepAtH st pos = stepHClens st pos := by unfold stepAtH; rw [htag] <;> rfl
    have e2 : stepAtHW st pos = stepHClensW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wClens hrel hn hr
  | syms o n clc ls =>
    have e1 : stepAtH st pos = stepHSyms st pos := by unfold stepAtH; rw [htag] <;> rfl
    have e2 : stepAtHW st pos = stepHSymsW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wSyms hrel hn hr hj
  | first i n tc cc =>
    have e : stepAtHW st pos = stepHFirstW := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    show 259 + 9 ≤ 268
    omega
  | np =>
    have e : stepAtHW st pos = stepHNpW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wNp hrel
  | modes done left =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | trees isL =>
    have e1 : stepAtH st pos = stepHTrees st pos := by unfold stepAtH; rw [htag] <;> rfl
    have e2 : stepAtHW st pos = stepHTreesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hr
    rw [e2]
    exact wTrees hrel hr
  | rlemax isL t =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | vals isL t r code done left =>
    have e1 : stepAtH st pos = stepHVals st pos := by unfold stepAtH; rw [htag] <;> rfl
    have e2 : stepAtHW st pos = stepHValsW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hj
    rw [e2]
    exact wVals hrel hj
  | imtf isL t vals =>
    have e : stepAtHW st pos = stepHImtfW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wImtf hrel
  | codes k done left =>
    have e : stepAtHW st pos = stepHCodesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wCodes hrel

/-- A header step's work, by where it goes. -/
theorem stepHW_cost {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} {g : Gh} {p : HPhase}
    {g' : Gh} {p' : HPhase} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat) (hn : (stepH a stop hs st pos).status = .next)
    (hr : HRel (stepH a stop hs st pos) g' p')
    (hj : ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepH a stop hs st pos).word (stepH a stop hs st pos).count a (stepH a stop hs st pos).pos stop F)) :
    stepHW a stop hs st pos ≤ hcost g p p' := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  have eH : stepH a stop hs st pos = stepAtH { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepH
    rw [dite_eq_left hp']
  have eW : stepHW a stop hs st pos = refillW st.word st.count a pos stop hs + stepAtHW { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepHW
    rw [dite_eq_left hp']
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  have hR := refillW_le (word := st.word) (count := st.count) hs hp
  rw [eH] at hn hr hj
  rw [eW]
  have hj1 := hj []
  have ha : availBits st.word st.count a pos stop [] = availBits (refill st.word st.count a pos stop hs hp).word
      (refill st.word st.count a pos stop hs hp).count a (refill st.word st.count a pos stop hs hp).pos stop [] := by
    show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ []) =
      (refill st.word st.count a pos stop hs hp).buf.held ++ (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ [])
    rw [← List.append_assoc, ← List.append_assoc, h4]
  rw [ha] at hj1
  have := stepAtHW_cost (hrel.withBits h1) hn hr hj1
  omega

end Brotli.Decoder
