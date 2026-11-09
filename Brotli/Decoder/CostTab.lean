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
where it is done. `mkHdrW_le` bounds the whole by `tabCost` of the numbers of block types: the policy may examine and
choose every literal type, so each literal type is charged its tree's root slots and a pair table.
-/

namespace Brotli.Decoder

/-! ### The work, pass by pass -/

/-- `fillLoop` over `n` entries: a round each and the one that ends it. -/
def fillW (n : Nat) : Nat := n + 1

/-- `pushLoop` of `n` entries of `w` bytes: the zero-fill, then the writes. -/
def pushLoopW (w n : Nat) : Nat := zeroExtendW (w * n) + fillW n

/-- `pushLE` of `n` bytes. -/
def pushLEW (n : Nat) : Nat := n + 1

/-- `pairCount` and `expLits`: a round for each of 256 root slots and the one that ends it. -/
def rootsW : Nat := 257

/-- `pairFlags` over `n` literal types: a round each, a tree's root slots counted for each type whose contexts share
one, and the one that ends it. -/
def pairFlagsW (lTriv : ByteArray) (n : Nat) : Nat :=
  n + 1 + rootsW * cntOn (fun k => u32At lTriv k != 4294967295) 0 n

/-- `bigLits`: the insert-and-copy tree's root slots when there is one. -/
def bigLitsW (nI : Nat) : Nat := if 0 < nI then rootsW + 1 else 1

/-- `tabPolicy`: `bigLits`, then `pairFlags` over the literal types when it chose to. -/
def tabPolicyW (big : Bool) (lTriv : ByteArray) (nL nI : Nat) : Nat :=
  bigLitsW nI + if big then pairFlagsW lTriv nL else 0

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
      (by have := h.arrs.icSize; have := h.arrs.nI256; omega) (fun ti hti => (h.icFits ti hti).root) mlen d.nL.toNat) lTriv
      d.nL.toNat d.nI.toNat +
    buildTabW (padOf A.size) d.nL.toNat d.nI.toNat d.nD.toNat P.1.1.1 P.1.1.2.1 P.1.1.2.2.1 P.1.1.2.2.2 lTriv

/-- `implSel`: a round for each insert-and-copy tree with its 64 sampled root slots and the round that ends them, and the
one that ends it. -/
def implSelW (nI : Nat) : Nat := nI + 1 + 65 * nI

/-- `mkHdrOf`'s derived tables: `buildArena` with the literal types' shared tables, then the loop's choice. -/
def mkHdrOfW (A : ByteArray) (d : Done) (mlen : UInt64) (h : ∃ g, Upto { d with arena := A } g 10) : Nat :=
  have hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A } := by
    obtain ⟨g, hu⟩ := h
    exact hdr_facts hu
  buildArenaW A d
    (trivBuild d.lMap d.litBase d.treesL.toNat d.nL hf.1.2.2.2.2.2.2.1 hf.1.2.2.1 hf.1.2.2.2.1 hf.1.2.1 hf.2.treeLt) mlen
    (by obtain ⟨g, hu⟩ := h; exact tabArgs_of hu trivBuild_spec.1 trivBuild_spec.2) + implSelW d.nI.toNat

/-- `mkHdr`'s tables: the shared distance table written into the arena's prefix, then the derived tables. -/
def mkHdrW (d : Done) (mlen : UInt64) (h : ∃ g, Upto d g 10) : Nat :=
  match hT : takeArena d with
  | (A, d0) =>
    have hr := upto_dshRoom (takeArena_upto hT h)
    writeDshW + mkHdrOfW (writeDsh d0.npostfix d0.ndirect A hr.1 hr.2) d0 mlen (upto_dsh (takeArena_upto hT h))

/-! ### The bound -/

/-- The most a header's derived tables take, by its numbers of block types: 2,376 for each insert-and-copy type (its
fused entries, and its tree's sampled root slots for the loop's choice), 1,870 for each literal type (its resolved map
and position, its tree's root slots examined and its pair table), 22 for each distance type, and 900 for the rest (the
shared distance table, the padding, the passes' ends). -/
def tabCost (nL nI nD : Nat) : Nat := 900 + 2376 * nI + 1870 * nL + 22 * nD

theorem buildTabW_le {pad nL nI nD : Nat} {w0 w1 w2 w3 : UInt64} {lTriv : ByteArray} (hp : pad ≤ 15) (hD : nD ≤ 256) :
    buildTabW pad nL nI nD w0 w1 w2 w3 lTriv ≤ 30 + 2310 * nI + 1610 * nL + 22 * nD := by
  have e1 := zeroExtendW_le (8 * (256 * nI))
  have e2 := zeroExtendW_le (4 * (64 * nL))
  have e3 := zeroExtendW_le (4 * (4 * nD))
  have hA : pushLoopW 4 256 ≤ 1282 := by
    have e4 := zeroExtendW_le (4 * 256)
    unfold pushLoopW fillW
    generalize zeroExtendW (4 * 256) = z at e4 ⊢
    omega
  have hP : pushLoopW 4 256 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL ≤ 1282 * nL :=
    Nat.mul_le_mul hA (cntOn_le _ 0 nL)
  unfold buildTabW pairsPassW
  generalize pushLoopW 4 256 * cntOn (pairOnN w0 w1 w2 w3 lTriv) 0 nL = P at hP ⊢
  unfold ixPassW appendW pushLEW pushLoopW fillW
  omega

theorem tabPolicyW_le {big : Bool} {lTriv : ByteArray} {nL nI : Nat} : tabPolicyW big lTriv nL nI ≤ 259 + 258 * nL := by
  have hc := cntOn_le (fun k => u32At lTriv k != 4294967295) 0 nL
  have hm2 : rootsW * cntOn (fun k => u32At lTriv k != 4294967295) 0 nL ≤ rootsW * nL := Nat.mul_le_mul_left _ hc
  unfold tabPolicyW bigLitsW pairFlagsW at *
  unfold rootsW at *
  split <;> split <;> omega

theorem buildArenaW_le {A : ByteArray} {d : Done} {lTriv : ByteArray} {mlen : UInt64}
    {h : TabArgs A d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
      d.treesD.toNat} :
    buildArenaW A d lTriv mlen h ≤ 289 + 2310 * d.nI.toNat + 1868 * d.nL.toNat + 22 * d.nD.toNat := by
  unfold buildArenaW
  dsimp only
  have e : 289 + 2310 * d.nI.toNat + 1868 * d.nL.toNat + 22 * d.nD.toNat =
      (259 + 258 * d.nL.toNat) + (30 + 2310 * d.nI.toNat + 1610 * d.nL.toNat + 22 * d.nD.toNat) := by omega
  rw [e]
  exact Nat.add_le_add tabPolicyW_le (buildTabW_le (padOf_spec A.size).2.1 h.arrs.nD256)

theorem mkHdrOfW_le {A : ByteArray} {d : Done} {mlen : UInt64} {h : ∃ g, Upto { d with arena := A } g 10} :
    mkHdrOfW A d mlen h ≤ 290 + 2376 * d.nI.toNat + 1868 * d.nL.toNat + 22 * d.nD.toNat := by
  unfold mkHdrOfW
  dsimp only
  have hs : implSelW d.nI.toNat ≤ 1 + 66 * d.nI.toNat := by unfold implSelW; omega
  exact Nat.le_trans (Nat.add_le_add buildArenaW_le hs) (by omega)

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
