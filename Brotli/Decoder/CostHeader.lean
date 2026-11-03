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

/-- How many of `n` bytes from `i` are not 0. -/
def nzC (out : ByteArray) (i n : Nat) : Nat := (List.range n).countP fun j => out.data[i + j]?.getD 0 != 0

theorem nzC_split (out : ByteArray) (i a : Nat) : ∀ b, nzC out i (a + b) = nzC out i a + nzC out (i + a) b
  | 0 => by simp [nzC]
  | b + 1 => by
    unfold nzC at *
    rw [show a + (b + 1) = (a + b) + 1 by omega, List.range_succ, List.countP_append, List.range_succ, List.countP_append]
    have := nzC_split out i a b
    unfold nzC at this
    rw [this, List.countP_singleton, List.countP_singleton, Nat.add_assoc i a b]
    omega

theorem nzC_congr {out out' : ByteArray} {i n : Nat} (h : ∀ q, i ≤ q → out'.data[q]? = out.data[q]?) : nzC out' i n = nzC out i n := by
  unfold nzC
  apply List.countP_congr
  intro j _
  rw [h (i + j) (by omega)]

theorem nzC_const {out : ByteArray} {i r : Nat} {s : UInt8} (h : ∀ j, j < r → out.data[i + j]?.getD 0 = s) :
    nzC out i r = if s = 0 then 0 else r := by
  unfold nzC
  by_cases hs : s = 0
  · rw [ite_eq_left hs, List.countP_eq_zero]
    intro j hj
    rw [h j (List.mem_range.mp hj), hs]
    decide
  · rw [ite_eq_right hs, List.countP_eq_length.mpr]
    · exact List.length_range
    · intro j hj
      rw [h j (List.mem_range.mp hj)]
      simpa using hs

/-- `imtfPlain` writes only the outputs it gives. -/
theorem imtfPlain_frame : ∀ (N : Nat) (m out : ByteArray) (i n : UInt64), n.toNat = N → i.toNat + N < 2 ^ 32 →
    (imtfPlain m out i n).2.size = out.size ∧ ∀ q, i.toNat + N ≤ q → (imtfPlain m out i n).2.data[q]? = out.data[q]? := by
  intro N
  induction N with
  | zero =>
    intro m out i n hn _
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [imtfPlain, dite_eq_left hz]
    exact ⟨rfl, fun _ _ => rfl⟩
  | succ N ih =>
    intro m out i n hn h32
    have hz : n ≠ 0 := fun e => by rw [e] at hn; exact Nat.succ_ne_zero _ hn.symm
    have hn1 : (n - 1).toNat = N := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
      rfl
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
    rw [imtfPlain, dite_eq_right hz]
    dsimp only
    obtain ⟨a1, a2⟩ := ih _ _ (i + 1) (n - 1) hn1 (by rw [hi1]; omega)
    rw [hi1] at a2
    refine ⟨by rw [a1, size_setU], fun q hq => ?_⟩
    rw [a2 q (by omega), setU_get_ne (by rw [hus]; omega)]

private theorem pos_u8 {b : UInt8} (h : b ≠ 0) : 1 ≤ b.toNat := by
  have : b.toNat ≠ 0 := fun e => h (UInt8.toNat_inj.mp (by rw [e]; rfl))
  omega

/-- The transform's work: eight rounds for each value, and 515 more for each value that is not 0. -/
theorem imtfGoW_le : ∀ (N : Nat) (m out : ByteArray) (i n : UInt64), n.toNat = N → i.toNat + N < 2 ^ 32 →
    i.toNat + N ≤ out.size → imtfGoW m out i n ≤ 8 * N + 515 * nzC out i.toNat N + 1 := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro m out i n hn h32 hs
  by_cases hN : N = 0
  · subst hN
    have hz : n = 0 := UInt64.toNat_inj.mp (by rw [hn]; rfl)
    rw [imtfGoW, dite_eq_left hz]
    omega
  have hz : n ≠ 0 := fun e => hN (by rw [← hn, e]; rfl)
  have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
  have hn1 : (n - 1).toNat = N - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
    rfl
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨c1, c2, c3⟩ := runCount_spec out i (getU out i.toUSize) (N - 1) 1 (n - 1) hn1
    (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
  rw [show (1 : UInt64).toNat = 1 from rfl] at c1 c2 c3
  have hb0 : (getU out i.toUSize).toNat = (out.data[i.toNat]?.getD 0).toNat := by rw [getU_toNat, hus]
  rw [imtfGoW, dite_eq_right hz]
  dsimp only
  generalize hb : getU out i.toUSize = byte at hb0 c1 c2 c3 ⊢
  generalize hr : runCount out i byte 1 (n - 1) = r at c1 c2 c3 ⊢
  have hsb : byte.toNat < 256 := byte.toNat_lt
  have hb64 : byte.toUInt64.toNat = byte.toNat := UInt8.toNat_toUInt64 byte
  have hfirst : out.data[i.toNat]?.getD 0 = byte := UInt8.toNat_inj.mp hb0.symm
  -- The run's bytes are all `byte`.
  have hrun : ∀ j, j < r.toNat → out.data[i.toNat + j]?.getD 0 = byte := by
    intro j hj
    by_cases hj0 : j = 0
    · rw [hj0, Nat.add_zero, hfirst]
    · exact c3 (by omega) j (by omega) hj
  by_cases hle : r ≤ byte.toUInt64 + 1
  · rw [dite_eq_left hle]
    have hle' : r.toNat ≤ byte.toNat + 1 := by
      have := UInt64.le_iff_toNat_le.mp hle
      rw [UInt64.toNat_add, hb64, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)] at this
      exact this
    obtain ⟨p1, p2⟩ := imtfPlain_frame 1 m out i 1 rfl (by omega)
    generalize imtfPlain m out i 1 = pl at p1 p2 ⊢
    obtain ⟨m1, out1⟩ := pl
    dsimp only at p1 p2 ⊢
    have hrec := ih (N - 1) (by omega) m1 out1 (i + 1) (n - 1) hn1 (by rw [hi1]; omega) (by rw [hi1, p1]; omega)
    rw [hi1, nzC_congr (fun q hq => p2 q (by omega))] at hrec
    have hsplit := nzC_split out i.toNat 1 (N - 1)
    rw [show 1 + (N - 1) = N by omega] at hsplit
    have h1 : nzC out i.toNat 1 = if byte = 0 then 0 else 1 := nzC_const (fun j hj => by rw [show j = 0 by omega, Nat.add_zero, hfirst])
    show r.toNat + 1 + (byte.toUInt64.toNat + 3 + imtfGoW m1 out1 (i + 1) (n - 1)) ≤ _
    rw [hb64]
    by_cases hz0 : byte = 0
    · rw [ite_eq_left hz0] at h1
      have : byte.toNat = 0 := by rw [hz0]; rfl
      omega
    · rw [ite_eq_right hz0] at h1
      omega
  · rw [dite_eq_right hle]
    have hp1 : (byte.toUInt64 + 1).toNat = byte.toNat + 1 := by
      rw [UInt64.toNat_add, hb64, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hrp : byte.toNat + 1 < r.toNat := Nat.lt_of_not_le fun e => hle (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; exact e))
    have hz0 : (0 : UInt64).toNat = 0 := rfl
    obtain ⟨o1, -, o3, -⟩ := revOut_spec m i byte.toUInt64 (byte.toNat + 1) 0 (byte.toUInt64 + 1) out hp1
      (by rw [hz0, hb64]; omega) (by rw [hb64]; exact hsb) (by rw [hz0]; omega) (by rw [hz0]; omega)
    rw [hz0, Nat.add_zero] at o3
    generalize revOut m out i byte.toUInt64 0 (byte.toUInt64 + 1) = out1 at o1 o3 ⊢
    have hip : (i + (byte.toUInt64 + 1)).toNat = i.toNat + (byte.toNat + 1) := by
      rw [UInt64.toNat_add, hp1]
      exact Nat.mod_eq_of_lt (by omega)
    have hrs : (r - (byte.toUInt64 + 1)).toNat = r.toNat - (byte.toNat + 1) := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    obtain ⟨q1, -, q3, -⟩ := copyPeriod_spec (byte.toUInt64 + 1) (by rw [hp1]; omega) (r.toNat - (byte.toNat + 1))
      (i + (byte.toUInt64 + 1)) (r - (byte.toUInt64 + 1)) out1 hrs (by rw [hip, hp1]; omega) (by rw [hip]; omega)
      (by rw [hip, o1]; omega)
    rw [hip] at q3
    generalize copyPeriod out1 (i + (byte.toUInt64 + 1)) (r - (byte.toUInt64 + 1)) (byte.toUInt64 + 1) = out2 at q1 q3 ⊢
    have hir : (i + r).toNat = i.toNat + r.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hnr : (n - r).toNat = N - r.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hn]
    have hk : ((r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1)).toNat < byte.toNat + 1 := by
      rw [UInt64.toNat_mod, hp1]
      exact Nat.mod_lt _ (by omega)
    have hpk : (byte.toUInt64 + 1 - (r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1)).toNat =
        byte.toNat + 1 - ((r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1)).toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
    rw [hp1, hrs, hpk]
    generalize (r - (byte.toUInt64 + 1)) % (byte.toUInt64 + 1) = k at hk ⊢
    generalize rotFrom out2 (rotFrom out2 m i 0 (k - 1) k) i k byte.toUInt64 (byte.toUInt64 + 1 - k) = M
    have hrec := ih (N - r.toNat) (by omega) M out2 (i + r) (n - r) hnr (by rw [hir]; omega) (by rw [hir, q1, o1]; omega)
    rw [hir, nzC_congr (out := out) (out' := out2) (i := i.toNat + r.toNat) (n := N - r.toNat)
      (fun q hq => by rw [q3 q (by omega), o3 q (by omega)])] at hrec
    have hsplit := nzC_split out i.toNat r.toNat (N - r.toNat)
    rw [show r.toNat + (N - r.toNat) = N by omega] at hsplit
    have hconst := nzC_const (out := out) (i := i.toNat) hrun
    by_cases hb00 : byte = 0
    · rw [ite_eq_left hb00] at hconst
      have : byte.toNat = 0 := by rw [hb00]; rfl
      omega
    · rw [ite_eq_right hb00] at hconst
      omega

/-- Over bytes that all hold `s`, the run goes to the end. -/
theorem runCount_all (out : ByteArray) (i : UInt64) (s : UInt8) : ∀ (K : Nat) (c k : UInt64), k.toNat = K → c.toNat + K < 2 ^ 64 →
    i.toNat + c.toNat + K < 2 ^ 32 → (∀ j, c.toNat ≤ j → j < c.toNat + K → out.data[i.toNat + j]?.getD 0 = s) →
    (runCount out i s c k).toNat = c.toNat + K := by
  intro K
  induction K with
  | zero =>
    intro c k hk _ _ _
    have hz : k = 0 := UInt64.toNat_inj.mp (by rw [hk]; rfl)
    rw [runCount, dite_eq_left hz]
    omega
  | succ K ih =>
    intro c k hk hc h32 hall
    have hz : k ≠ 0 := fun e => by rw [e] at hk; exact Nat.succ_ne_zero _ hk.symm
    have hk1 : (k - 1).toNat = K := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hk]
      rfl
    have hc1 : (c + 1).toNat = c.toNat + 1 := by
      rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hic : (i + c).toNat = i.toNat + c.toNat := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have he : getU out (i + c).toUSize = s := by
      apply UInt8.toNat_inj.mp
      rw [getU_toNat, word_toUSize (by omega), hic, hall c.toNat (Nat.le_refl _) (by omega)]
    rw [runCount, dite_eq_right hz, ite_eq_left he, ih (c + 1) (k - 1) hk1 (by omega) (by omega)
      (fun j h1 h2 => hall j (by omega) (by omega)), hc1]
    omega

/-- On a run of one value longer than the places it turns round, the transform's work is linear. -/
theorem imtfGoW_const {m out : ByteArray} {i n : UInt64} {N : Nat} {v : UInt8} (hn : n.toNat = N) (h32 : i.toNat + N < 2 ^ 32)
    (hall : ∀ j, j < N → out.data[i.toNat + j]?.getD 0 = v) (hv : v.toNat + 1 < N) :
    imtfGoW m out i n ≤ 2 * N + v.toNat + 8 := by
  have hz : n ≠ 0 := fun e => by rw [e] at hn; simp at hn; omega
  have hus : i.toUSize.toNat = i.toNat := word_toUSize (by omega)
  have hn1 : (n - 1).toNat = N - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hn]
    rfl
  have hb : getU out i.toUSize = v := by
    apply UInt8.toNat_inj.mp
    rw [getU_toNat, hus, ← Nat.add_zero i.toNat, hall 0 (by omega)]
  have hr := runCount_all out i v (N - 1) 1 (n - 1) hn1 (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)
    (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega) (fun j _ h2 => hall j (by rw [show (1 : UInt64).toNat = 1 from rfl] at h2; omega))
  rw [show (1 : UInt64).toNat = 1 from rfl] at hr
  have hb64 : v.toUInt64.toNat = v.toNat := UInt8.toNat_toUInt64 v
  have hsb : v.toNat < 256 := v.toNat_lt
  rw [imtfGoW, dite_eq_right hz]
  dsimp only
  rw [hb]
  generalize hrr : runCount out i v 1 (n - 1) = r at hr ⊢
  have hp1 : (v.toUInt64 + 1).toNat = v.toNat + 1 := by
    rw [UInt64.toNat_add, hb64, show (1 : UInt64).toNat = 1 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hle : ¬ r ≤ v.toUInt64 + 1 := fun e => by
    have := UInt64.le_iff_toNat_le.mp e
    omega
  rw [dite_eq_right hle]
  have hrs : (r - (v.toUInt64 + 1)).toNat = r.toNat - (v.toNat + 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
  have hk : ((r - (v.toUInt64 + 1)) % (v.toUInt64 + 1)).toNat < v.toNat + 1 := by
    rw [UInt64.toNat_mod, hp1]
    exact Nat.mod_lt _ (by omega)
  have hpk : (v.toUInt64 + 1 - (r - (v.toUInt64 + 1)) % (v.toUInt64 + 1)).toNat =
      v.toNat + 1 - ((r - (v.toUInt64 + 1)) % (v.toUInt64 + 1)).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hp1]; omega)), hp1]
  have hnr : n - r = 0 := UInt64.toNat_inj.mp (by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hn]
    show N - r.toNat = 0
    omega)
  rw [hp1, hrs, hpk, hnr]
  generalize (r - (v.toUInt64 + 1)) % (v.toUInt64 + 1) = k at hk ⊢
  have e0 : ∀ M O J, imtfGoW M O J 0 = 1 := fun M O J => by rw [imtfGoW, dite_eq_left rfl]
  rw [e0]
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
