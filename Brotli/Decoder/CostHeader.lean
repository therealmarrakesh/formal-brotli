import Brotli.Decoder.HeaderDone
import Brotli.Decoder.Cost

/-!
# The work of a header step

Each function here mirrors the header step or helper of the same name without its `W`, branch by branch, and counts
the rounds of its loops. A loop that can stop early counts all the rounds it could take.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

private theorem cusize_ofNat {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
  exact Nat.mod_eq_of_lt (by have := USize.le_size; omega)

private theorem cusize_add {p : USize} {n : Nat} (hn : n < 2 ^ 32) (h : p.toNat + n < USize.size) :
    (p + USize.ofNat n).toNat = p.toNat + n := by
  rw [USize.toNat_add, cusize_ofNat hn]
  exact Nat.mod_eq_of_lt h

/-! ### Refills -/

/-- The work of `fillSlow`: a round for each byte it takes. -/
def fillSlowW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (word count : UInt64) (p : USize) : Nat :=
  if h : count ≤ 56 ∧ p < stop then
    have hlt := USize.lt_iff_toNat_lt.mp h.2
    have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
      cusize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
    let b := (BitBuffer.mk word count).push (a.uget p (by omega))
    1 + fillSlowW a stop hs b.word b.count (p + USize.ofNat 1)
  else 1
termination_by stop.toNat - p.toNat
decreasing_by omega

theorem fillSlowW_le {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) : ∀ (N : Nat) (word count : UInt64) (p : USize),
    stop.toNat - p.toNat = N → fillSlowW a stop hs word count p ≤ N + 1 := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro word count p hN
    rw [fillSlowW]
    split
    · rename_i h
      have hlt := USize.lt_iff_toNat_lt.mp h.2
      have hnext : (p + USize.ofNat 1).toNat = p.toNat + 1 :=
        cusize_add (by decide) (Nat.lt_of_le_of_lt (by omega) stop.toNat_lt_size)
      have key : ∀ w c, fillSlowW a stop hs w c (p + USize.ofNat 1) ≤ stop.toNat - (p + USize.ofNat 1).toNat + 1 :=
        fun w c => ih _ (by omega) w c _ rfl
      refine Nat.le_trans (Nat.add_le_add_left (key _ _) 1) ?_
      omega
    · omega

/-- The work of `refill`: one load, or a round for each of the fewer than eight bytes left. -/
def refillW (word count : UInt64) (a : ByteArray) (pos stop : USize) (hs : stop.toNat ≤ a.size) : Nat :=
  if 56 < count then 1
  else if USize.ofNat 8 ≤ stop - pos then 1
  else fillSlowW a stop hs word count pos

theorem refillW_le {word count : UInt64} {a : ByteArray} {pos stop : USize} (hs : stop.toNat ≤ a.size)
    (hp : pos.toNat ≤ stop.toNat) : refillW word count a pos stop hs ≤ 9 := by
  unfold refillW
  split
  · omega
  · split
    · omega
    · rename_i h
      have h1 : ¬ 8 ≤ stop.toNat - pos.toNat := by
        intro e
        apply h
        apply USize.le_iff_toNat_le.mpr
        rw [cusize_ofNat (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hp)]
        exact e
      have := fillSlowW_le hs _ word count pos rfl
      omega

/-! ### Tables -/

/-- The work of `tableDone`: the table built, and for a context map's code the check of its table and the map's zeros. -/
def tableDoneW (st : Hd) (single : Bool) : Nat :=
  let n := st.size.toUSize
  let lens := st.lens
  if hn : n.toNat ≤ lens.size then
    (if single then buildSingleW else buildFastW lens n hn) +
      match st.role with
      | .map => fitsW + zbW (mapSizeFast st)
      | _ => 1
  else 1

/-- The work of `clTable`. -/
def clTableW (st : Hd) : Nat :=
  if st.clNz = 1 then buildSingleW
  else if hn : (USize.ofNat 18).toNat ≤ st.clLens.size then buildFastW st.clLens (USize.ofNat 18) hn
  else 1

/-- The work of `clFinish`: the code length code's table, its check, and the code's lengths' zeros. -/
def clFinishW (st : Hd) : Nat := clTableW st + fitsW + zbW st.size.toNat

/-- The work of `mapFinish`: the next group of codes' zeros, after the second map. -/
def mapFinishW (st : Hd) : Nat := if st.isL then 1 else zbW (4 * st.d.treesL.toNat) + 1

/-- The work of `ckFinish`: the next group of codes' zeros. -/
def ckFinishW (st : Hd) : Nat :=
  match st.ck with
  | .L => zbW (4 * st.d.nI.toNat) + 1
  | .I => zbW (4 * st.d.treesD.toNat) + 1
  | .D => 1

/-! ### The inverse move-to-front transform -/

/-- The work of `imtfGo`: the run's count, then one step with its shift, or a round of the run, its copy and the turn. -/
def imtfGoW (m out : ByteArray) (i n : UInt64) : Nat :=
  if _hn : n = 0 then 1
  else
    let index := (getU out i.toUSize).toUInt64
    let r := runCount out i (getU out i.toUSize) 1 (n - 1)
    r.toNat + 1 +
    if _hr : r ≤ index + 1 then
      match imtfPlain m out i 1 with
      | (m1, out1) => index.toNat + 3 + imtfGoW m1 out1 (i + 1) (n - 1)
    else
      let p := index + 1
      let out2 := copyPeriod (revOut m out i index 0 p) (i + p) (r - p) p
      let k := (r - p) % p
      p.toNat + 1 + ((r - p).toNat + 1) + (k.toNat + 1) + ((p - k).toNat + 1) +
        imtfGoW (rotFrom out2 (rotFrom out2 m i 0 (k - 1) k) i k index (p - k)) out2 (i + r) (n - r)
termination_by n.toNat
decreasing_by
  · have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (1 : UInt64).toNat = 1 from rfl]
      omega))
    omega
  · have hne : n.toNat ≠ 0 := fun e => _hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
    have h1 : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
      rw [show (1 : UInt64).toNat = 1 from rfl]
      omega))
    have hn64 : n.toNat < 2 ^ 64 := n.toNat_lt
    obtain ⟨c1, c2, _⟩ := runCount_spec out i (getU out i.toUSize) _ 1 (n - 1) rfl
      (by rw [h1, show (1 : UInt64).toNat = 1 from rfl]; omega)
    rw [show (1 : UInt64).toNat = 1 from rfl] at c1 c2
    rw [h1] at c2
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]
    omega

/-- The work of `allOccur`: 256 zeros, a mark for each value, a look at each tree. -/
def allOccurW (size n : UInt64) : Nat := zbW 256 + size.toNat + 1 + n.toNat + 1

/-! ### The steps -/

/-- The work of `stepHCode`. -/
def stepHCodeW (st : Hd) (pos : USize) : Nat :=
  let b0 : BitBuffer := ⟨st.word, st.count⟩
  if 2 ≤ st.count then
    let hskip := b0.peek 2
    let b1 := b0.drop 2
    if hskip = 1 then
      let size := st.size
      let r := simpleFast size (alphabetBitsFast size) b1
      match r.status with
      | .ok =>
        zbW size.toNat + 1 + tableDoneW { st with
            word := r.word, count := r.count, pos := pos, status := .next
            lens := writeSimple (zeroBytes size.toNat) r } (r.e == 0)
      | _ => 1
    else zbW 18 + 1
  else 1

/-- The work of `stepHClens`. -/
def stepHClensW (st : Hd) (pos : USize) : Nat :=
  let idx := st.clIdx
  if idx = 18 then
    if st.clNz = 1 then clFinishW { st with pos := pos, status := .next } + 1 else 1
  else
    let r := cclFast ⟨st.word, st.count⟩
    match r.status with
    | .ok =>
      let len := r.a
      if len = 0 then 1
      else
        let sym := (getU clOrderLut idx.toUSize).toUInt64
        let sum := st.clSum + ((32 : UInt64) >>> len)
        if sum = 32 then
          clFinishW { st with
            word := r.word, count := r.count, pos := pos, status := .next, clLens := setLen st.clLens sym len, clSum := sum,
            clNz := st.clNz + 1, clSym := sym, clIdx := idx + 1 } + 1
        else 1
    | _ => 1

/-- The work of `stepHSyms`. -/
def stepHSymsW (st : Hd) (pos : USize) : Nat :=
  if st.symSum = 32768 then tableDoneW { st with pos := pos, status := .next } false + 1
  else if st.ln = st.size then 1
  else
    let r := lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩
    match r.status with
    | .ok =>
      let sym := r.a
      let ln := st.ln
      if sym < 16 then 1
      else
        let mult : UInt64 := if sym = 16 then 4 else 8
        let old := if st.repCount ≠ 0 ∧ st.repSym = sym then st.repCount else 0
        let new := if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)
        let delta := new - old
        if st.size < ln + delta then 1 else delta.toNat + 2
    | _ => 1

/-- The work of `stepHFirst`: the table's check. -/
def stepHFirstW : Nat := fitsW + 1

/-- The work of `stepHNp`: the modes' zeros. -/
def stepHNpW (st : Hd) : Nat :=
  match (npFast ⟨st.word, st.count⟩).status with
  | .ok => zbW st.d.nL.toNat + 1
  | _ => 1

/-- The work of `stepHTrees`: with one tree, the map's zeros. -/
def stepHTreesW (st : Hd) : Nat :=
  let r := varLenFast ⟨st.word, st.count⟩
  match r.status with
  | .ok => if r.a < 2 then zbW (mapSizeFast st) + mapFinishW st + 1 else 1
  | _ => 1

/-- The work of `stepHVals`: with a code that gives a value without reading, the values left written. -/
def stepHValsW (st : Hd) : Nat :=
  let left := st.left
  if left = 0 then 1
  else
    let r := mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩
    match r.status with
    | .ok =>
      if left < r.b then 1
      else if r.count = st.count then (if r.a = 0 then 1 else left.toNat + 2)
      else 1
    | _ => 1

/-- The work of `stepHImtf`: the transform, its first list copied from the shared one, and the check that every tree
occurs. -/
def stepHImtfW (st : Hd) : Nat :=
  if 1 ≤ st.count then
    let b : BitBuffer := ⟨st.word, st.count⟩
    let size := UInt64.ofNat st.fill.size
    (if b.peek 1 = 0 then 0 else 257 + imtfGoW mtfInitLut st.fill 0 size) + allOccurW size st.ntrees + mapFinishW st + 1
  else 1

/-- The work of `stepHCodes`: at a group's end, the next group's zeros. -/
def stepHCodesW (st : Hd) : Nat := if st.left = 0 then ckFinishW st + 1 else 1

/-- The work of a header step, once the buffer is refilled. -/
def stepAtHW (st : Hd) (pos : USize) : Nat :=
  match st.tag with
  | .cat => 1
  | .code => stepHCodeW st pos
  | .clens => stepHClensW st pos
  | .syms => stepHSymsW st pos
  | .first => stepHFirstW
  | .np => stepHNpW st
  | .modes => 1
  | .trees => stepHTreesW st
  | .rlemax => 1
  | .vals => stepHValsW st
  | .imtf => stepHImtfW st
  | .codes => stepHCodesW st
  | .ready => 1

/-- The work of a header step: the refill, then the step. -/
def stepHW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Hd) (pos : USize) : Nat :=
  if hp : pos ≤ stop then
    let r := refill st.word st.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    refillW st.word st.count a pos stop hs + stepAtHW { st with word := r.word, count := r.count } r.pos
  else 1

end Brotli.Decoder
