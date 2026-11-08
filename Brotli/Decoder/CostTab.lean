module

public import Brotli.Decoder.HeaderDone
public import Brotli.Decoder.Cost

@[expose] public section

/-!
# The work of a header's derived tables

At a header's end `mkHdr` writes the shared distance table into the arena's prefix and builds the fast command loop's
derived tables (`buildArena`): the pair-table policy (`tabPolicy`), then the fused insert-and-copy entries, the resolved
maps, the trees' bases, the pair tables and their positions (`buildTab`). Each function here mirrors the loop of the same
name without its `W`: a pass that writes `n` entries of `w` bytes (`pushLoop`) zero-fills `w * n` bytes (`zeroExtend`)
and goes round `n + 1` times; a loop over the types goes round once a type and once more; a type's own work is counted
where it is done. `mkHdrW_le` bounds the whole by `tabCost` of the numbers of block types: the pair tables are at most
eight (`tabPolicy_pairs`), since the policy looks only at the first eight literal types.
-/

namespace Brotli.Decoder

/-! ### The pair-table policy sets at most the first eight literal types' flags -/

theorem setFlag_lt {q w : UInt64} (hq : q.toNat < 8) (hw : w.toNat < 256) : (setFlag q 0 w).toNat < 256 := by
  unfold setFlag
  split
  · have h1 : ((1 : UInt64) <<< (q &&& 63)).toNat < 2 ^ 8 := by
      have hq63 : (q &&& 63).toNat % 64 = q.toNat := by
        rw [UInt64.toNat_and, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
        omega
      have hp : 2 ^ q.toNat < 2 ^ 8 := Nat.pow_lt_pow_right (by decide) hq
      rw [UInt64.toNat_shiftLeft, hq63, show (1 : UInt64).toNat = 1 from rfl, Nat.one_shiftLeft,
        Nat.mod_eq_of_lt (Nat.lt_trans hp (by decide))]
      exact hp
    rw [UInt64.toNat_or]
    exact Nat.or_lt_two_pow (show w.toNat < 2 ^ 8 from hw) h1
  · exact hw

theorem pairFlags_lt {t : ByteArray} {s : t.size < 2 ^ 32} {lTriv : ByteArray} {nL : Nat} {ht : lTriv.size = 4 * nL}
    {hl32 : lTriv.size < 2 ^ 32} {hr : PairReady lTriv nL t} {n : USize} {hn : n.toNat ≤ nL} (hn8 : n.toNat ≤ 8) :
    ∀ (N : Nat) (ti : USize) (w0 : UInt64), n.toNat - ti.toNat = N → w0.toNat < 256 →
      (pairFlags t s lTriv nL ht hl32 hr n hn ti w0).toNat < 256 := by
  intro N
  induction N with
  | zero =>
    intro ti w0 hN hw
    have hti : ¬ ti < n := fun e => by have := USize.lt_iff_toNat_lt.mp e; omega
    rw [pairFlags, dite_eq_right hti]
    exact hw
  | succ N ih =>
    intro ti w0 hN hw
    have hti : ti < n := USize.lt_iff_toNat_lt.mpr (by omega)
    have hs := fastIdx_succ hti
    have hq : ti.toUInt64.toNat < 8 := by
      rw [USize.toNat_toUInt64]
      have := USize.lt_iff_toNat_lt.mp hti
      omega
    rw [pairFlags, dite_eq_left hti]
    dsimp only
    split
    · exact ih _ _ (by rw [hs]; omega) hw
    · split
      · exact ih _ _ (by rw [hs]; omega) (setFlag_lt hq hw)
      · exact ih _ _ (by rw [hs]; omega) hw

/-- A type from 8 on has no pair table when only the first word's low byte of flags can be set. -/
theorem pairOnN_hi {w0 : UInt64} (hw : w0.toNat < 256) (lTriv : ByteArray) {k : Nat} (hk8 : 8 ≤ k) (hk : k < 256) :
    pairOnN w0 0 0 0 lTriv k = false := by
  have hkU : (UInt64.ofNat k).toNat = k := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have h63 : (UInt64.ofNat k &&& 63).toNat = k % 64 := by
    rw [UInt64.toNat_and, hkU, show (63 : UInt64).toNat = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hz : ∀ x : UInt64, x.toNat < 2 ^ (k % 64) → (x >>> (UInt64.ofNat k &&& 63)) &&& 1 = 0 := fun x hx => by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, h63, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide)),
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hx]
    rfl
  unfold pairOnN flagBit
  by_cases h64 : UInt64.ofNat k < 64
  · have hk64 : k < 64 := by rw [← hkU]; exact UInt64.lt_iff_toNat_lt.mp h64
    rw [ite_eq_left h64, hz w0 (by
      have : (2 : Nat) ^ 8 ≤ 2 ^ (k % 64) := Nat.pow_le_pow_right (by decide) (by omega)
      omega)]
    rfl
  · rw [ite_eq_right h64]
    have hz0 : ∀ c₁ c₂ : Prop, ∀ [Decidable c₁] [Decidable c₂],
        ((if c₁ then (0 : UInt64) else if c₂ then 0 else 0) >>> (UInt64.ofNat k &&& 63)) &&& 1 = 0 := by
      intro c₁ c₂ _ _
      split <;> (try split) <;> exact hz 0 (Nat.two_pow_pos _)
    rw [hz0]
    rfl

/-- A count of the values from `a` of a test false from `b` on is at most `b - a`. -/
theorem cntOn_hi (fl : Nat → Bool) (b : Nat) : ∀ (a len : Nat), (∀ k, b ≤ k → k < a + len → fl k = false) →
    cntOn fl a len ≤ b - a
  | _, 0, _ => Nat.zero_le _
  | a, len + 1, h => by
    rw [cntOn_succ]
    have ih := cntOn_hi fl b (a + 1) len (fun k h1 h2 => h k h1 (by omega))
    by_cases hab : a < b
    · split <;> omega
    · rw [h a (by omega) (by omega)]
      have := cntOn_hi fl b (a + 1) len (fun k h1 h2 => h k h1 (by omega))
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega

/-- The policy chooses at most eight literal types for pair tables. -/
theorem tabPolicy_pairs {A : ByteArray} {s : A.size < 2 ^ 32} {icBase : ByteArray} {nI : Nat}
    {hic : icBase.size = 4 * nI} {hi32 : icBase.size < 2 ^ 32} {hI : ICReady icBase nI A} {lTriv : ByteArray} {nL : Nat}
    {ht : lTriv.size = 4 * nL} {hn : nL ≤ 256} {hP : PairReady lTriv nL A} {mlen : UInt64} :
    cntOn (pairOnN (tabPolicy A s icBase nI hic hi32 hI lTriv nL ht hn hP mlen).1.1.1
      (tabPolicy A s icBase nI hic hi32 hI lTriv nL ht hn hP mlen).1.1.2.1
      (tabPolicy A s icBase nI hic hi32 hI lTriv nL ht hn hP mlen).1.1.2.2.1
      (tabPolicy A s icBase nI hic hi32 hI lTriv nL ht hn hP mlen).1.1.2.2.2 lTriv) 0 nL ≤ 8 := by
  have key : ∀ w0 : UInt64, w0.toNat < 256 → cntOn (pairOnN w0 0 0 0 lTriv) 0 nL ≤ 8 := fun w0 hw =>
    Nat.le_trans (cntOn_hi _ 8 0 nL fun k h1 h2 => pairOnN_hi hw lTriv h1 (by omega)) (by omega)
  unfold tabPolicy
  dsimp only
  split
  · exact key _ (pairFlags_lt (by rw [fastLit (by unfold pairTypes; omega)]; unfold pairTypes; omega) _ _ _ rfl
      (by decide))
  · exact key 0 (by decide)

/-! ### The work, pass by pass -/

/-- `fillLoop` over `n` entries: a round each and the one that ends it. -/
def fillW (n : Nat) : Nat := n + 1

/-- `pushLoop` of `n` entries of `w` bytes: the zero-fill, then the writes. -/
def pushLoopW (w n : Nat) : Nat := zeroExtendW (w * n) + fillW n

/-- `pushLE` of `n` bytes. -/
def pushLEW (n : Nat) : Nat := n + 1

/-- `pairCount` and `expLits`: a round for each of 256 root slots and the one that ends it. -/
def rootsW : Nat := 257

/-- `pairFlags` over the first `n` literal types: a round each, a tree's root slots counted for each type whose contexts
share one, and the one that ends it. -/
def pairFlagsW (lTriv : ByteArray) (n : Nat) : Nat :=
  n + 1 + rootsW * cntOn (fun k => u32At lTriv k != 4294967295) 0 n

/-- `bigLits`: the insert-and-copy tree's root slots when there is one. -/
def bigLitsW (nI : Nat) : Nat := if 0 < nI then rootsW + 1 else 1

/-- `tabPolicy`: `bigLits`, then `pairFlags` over the first `pairTypes` literal types when it chose to. -/
def tabPolicyW (big : Bool) (lTriv : ByteArray) (nL nI : Nat) : Nat :=
  bigLitsW nI + if big then pairFlagsW lTriv (min nL pairTypes) else 0

/-- `pairsPass`: a round for each literal type and the one that ends it, and a 256-entry pass (`pushPair`) for each type
chosen. -/
def pairsPassW (w0 w1 w2 w3 : UInt64) (lTriv : ByteArray) (nL : Nat) : Nat :=
  nL + 1 + pushLoopW 4 256 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL

/-- `ixPass`: a 4-byte position for each literal type, and the round that ends it. -/
def ixPassW (nL : Nat) : Nat := nL + 1 + nL * pushLEW 4

/-- A `copySlice` of `n` bytes, as `++` appends an array. -/
def appendW (n : Nat) : Nat := n + 1

/-- `buildTab`: the padding, the fused entries (256 of 8 bytes for each insert-and-copy tree), the resolved literal map
(64 of 4 bytes for each literal type) and distance map (4 of 4 bytes for each distance type), the insert-and-copy trees'
bases appended, the pair tables and their positions. -/
def buildTabW (pad nL nI nD : Nat) (w0 w1 w2 w3 : UInt64) (lTriv : ByteArray) : Nat :=
  pushLEW pad + pushLoopW 8 (256 * nI) + pushLoopW 4 (64 * nL) + pushLoopW 4 (4 * nD) + appendW (4 * nI) +
    pairsPassW w0 w1 w2 w3 lTriv nL + ixPassW nL

/-- `writeDsh`: 520 entries. -/
def writeDshW : Nat := fillW 520

/-- `buildArena`: the policy, then the derived tables, with the flags the policy chose. -/
def buildArenaW (A : ByteArray) (d : Done) (lTriv : ByteArray) (mlen : UInt64)
    (h : TabArgs A d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
      d.treesD.toNat) : Nat :=
  let P := tabPolicy A (by have := h.size; omega) d.icBase d.nI.toNat h.arrs.icSize
      (by have := h.arrs.icSize; have := h.arrs.nI256; omega) (fun ti hti => (h.icFits ti hti).root) lTriv d.nL.toNat
      h.arrs.trivSize h.arrs.nL256 h.trivFits mlen
  tabPolicyW (bigLits A (by have := h.size; omega) d.icBase d.nI.toNat h.arrs.icSize
      (by have := h.arrs.icSize; have := h.arrs.nI256; omega) (fun ti hti => (h.icFits ti hti).root) mlen) lTriv
      d.nL.toNat d.nI.toNat +
    buildTabW (padOf A.size) d.nL.toNat d.nI.toNat d.nD.toNat P.1.1.1 P.1.1.2.1 P.1.1.2.2.1 P.1.1.2.2.2 lTriv

/-- `mkHdrOf`'s derived tables: `buildArena` with the literal types' shared tables. -/
def mkHdrOfW (A : ByteArray) (d : Done) (mlen : UInt64) (h : ∃ g, Upto { d with arena := A } g 10) : Nat :=
  have hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A } := by
    obtain ⟨g, hu⟩ := h
    exact hdr_facts hu
  buildArenaW A d
    (trivBuild d.lMap d.litBase d.treesL.toNat d.nL hf.1.2.2.2.2.2.2.1 hf.1.2.2.1 hf.1.2.2.2.1 hf.1.2.1 hf.2.treeLt) mlen
    (by obtain ⟨g, hu⟩ := h; exact tabArgs_of hu trivBuild_spec.1 trivBuild_spec.2)

/-- `mkHdr`'s tables: the shared distance table written into the arena's prefix, then the derived tables. -/
def mkHdrW (d : Done) (mlen : UInt64) (h : ∃ g, Upto d g 10) : Nat :=
  match hT : takeArena d with
  | (A, d0) =>
    have hr := upto_dshRoom (takeArena_upto hT h)
    writeDshW + mkHdrOfW (writeDsh d0.npostfix d0.ndirect A hr.1 hr.2) d0 mlen (upto_dsh (takeArena_upto hT h))

/-! ### The bound -/

/-- The most a header's derived tables take, by its numbers of block types: about 2,300 for each insert-and-copy type
(its fused entries), 330 for each literal type (its resolved map and position), 22 for each distance type, and 13,300
for the rest (the policy, at most eight pair tables, the shared distance table, the padding). -/
def tabCost (nL nI nD : Nat) : Nat := 13300 + 2310 * nI + 330 * nL + 22 * nD

theorem buildTabW_le {pad nL nI nD : Nat} {w0 w1 w2 w3 : UInt64} {lTriv : ByteArray} (hp : pad ≤ 15) (hL : nL ≤ 256)
    (hI : nI ≤ 256) (hD : nD ≤ 256) (hc : cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL ≤ 8) :
    buildTabW pad nL nI nD w0 w1 w2 w3 lTriv ≤ 10300 + 2310 * nI + 330 * nL + 22 * nD := by
  have e1 := zeroExtendW_le (8 * (256 * nI))
  have e2 := zeroExtendW_le (4 * (64 * nL))
  have e3 := zeroExtendW_le (4 * (4 * nD))
  have hA : pushLoopW 4 256 ≤ 1282 := by
    have e4 := zeroExtendW_le (4 * 256)
    unfold pushLoopW fillW
    generalize zeroExtendW (4 * 256) = z at e4 ⊢
    omega
  have hP : pushLoopW 4 256 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL ≤ 1282 * 8 := Nat.mul_le_mul hA hc
  unfold buildTabW pairsPassW
  generalize pushLoopW 4 256 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL = P at hP ⊢
  unfold ixPassW appendW pushLEW pushLoopW fillW
  omega

theorem tabPolicyW_le {big : Bool} {lTriv : ByteArray} {nL nI : Nat} : tabPolicyW big lTriv nL nI ≤ 2400 := by
  have hc := cntOn_le (fun k => u32At lTriv k != 4294967295) 0 (min nL pairTypes)
  have hm : min nL pairTypes ≤ 8 := by unfold pairTypes; omega
  have hm2 : rootsW * cntOn (fun k => u32At lTriv k != 4294967295) 0 (min nL pairTypes) ≤ rootsW * 8 :=
    Nat.mul_le_mul_left _ (Nat.le_trans hc hm)
  unfold tabPolicyW bigLitsW pairFlagsW at *
  unfold rootsW at *
  split <;> split <;> omega

theorem buildArenaW_le {A : ByteArray} {d : Done} {lTriv : ByteArray} {mlen : UInt64}
    {h : TabArgs A d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
      d.treesD.toNat} :
    buildArenaW A d lTriv mlen h ≤ 12700 + 2310 * d.nI.toNat + 330 * d.nL.toNat + 22 * d.nD.toNat := by
  unfold buildArenaW
  dsimp only
  have e : 12700 + 2310 * d.nI.toNat + 330 * d.nL.toNat + 22 * d.nD.toNat =
      2400 + (10300 + 2310 * d.nI.toNat + 330 * d.nL.toNat + 22 * d.nD.toNat) := by omega
  rw [e]
  exact Nat.add_le_add tabPolicyW_le
    (buildTabW_le (padOf_spec A.size).2.1 h.arrs.nL256 h.arrs.nI256 h.arrs.nD256 tabPolicy_pairs)

theorem mkHdrOfW_le {A : ByteArray} {d : Done} {mlen : UInt64} {h : ∃ g, Upto { d with arena := A } g 10} :
    mkHdrOfW A d mlen h ≤ 12700 + 2310 * d.nI.toNat + 330 * d.nL.toNat + 22 * d.nD.toNat := by
  unfold mkHdrOfW
  exact buildArenaW_le

/-- The tables a header's end builds take at most `tabCost` of its numbers of block types. -/
theorem mkHdrW_le {d : Done} {mlen : UInt64} {h : ∃ g, Upto d g 10} :
    mkHdrW d mlen h ≤ tabCost d.nL.toNat d.nI.toNat d.nD.toNat := by
  unfold mkHdrW
  split
  rename_i A d0 hT
  have hb := takeArena_back hT
  have e1 : d0.nL.toNat = d.nL.toNat := by rw [← hb]
  have e2 : d0.nI.toNat = d.nI.toNat := by rw [← hb]
  have e3 : d0.nD.toNat = d.nD.toNat := by rw [← hb]
  have := mkHdrOfW_le (A := writeDsh d0.npostfix d0.ndirect A (upto_dshRoom (takeArena_upto hT h)).1
    (upto_dshRoom (takeArena_upto hT h)).2) (d := d0) (mlen := mlen) (h := upto_dsh (takeArena_upto hT h))
  dsimp only
  unfold tabCost writeDshW fillW
  omega

end Brotli.Decoder
