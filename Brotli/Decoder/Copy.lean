module

public import Brotli.Decoder.Window
public import Brotli.Spec.Context
public import Brotli.Spec.Stream

@[expose] public section

/-!
# The copy loops

Backward copies and dictionary words write the window a byte at a time, so that a copy may overlap what it writes.
No bits are read. Their state is plain values, and they return only when their count runs out.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- A copy loop's result, flat. -/
structure CopyRun where
  ring : ByteArray
  wpos : USize
  p1 : UInt8
  p2 : UInt8

/-- The bytes before a new byte are shifted by it. -/
theorem contextBytes_push (b : Nat) (out : List Nat) : contextBytes (b :: out) = (b, (contextBytes out).1) := by
  cases out with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys => rfl

/-- A loop's count going down by one. -/
theorem usize_pred {n : USize} (h : n ≠ 0) : (n - USize.ofNat 1).toNat = n.toNat - 1 := by
  have hz : n.toNat ≠ 0 := fun e => h (USize.toNat_inj.mp (by rw [e]; rfl))
  have h1 : (USize.ofNat 1).toNat = 1 := by
    rw [USize.toNat_ofNat', ← USize.size_eq_two_pow]
    have := USize.le_size
    exact Nat.mod_eq_of_lt (by omega)
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h1]; omega)), h1]

theorem usize_zero {n : USize} (h : n.toNat = 0) : n = 0 :=
  USize.toNat_inj.mp (by rw [h]; rfl)

theorem usize_ne {n : USize} (h : n ≠ 0) : n.toNat ≠ 0 := fun e => h (usize_zero e)

/-- Copies `n` bytes from `d` back. -/
def copyRun (d mask size : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k)
    (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : CopyRun :=
  if hn : n = 0 then ⟨ring, wpos, p1, p2⟩
  else
    have hb : (ringBack wpos d mask size).toNat < ring.size := by
      rw [ringBack_toNat hk hmask hsz hwp hd1 hd2, hsize]
      exact ringIdx_lt hwp (by omega)
    let byte := ring.uget (ringBack wpos d mask size) hb
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    copyRun d mask size k hk hmask hsz hd1 hd2 (n - USize.ofNat 1) (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1
      ((size_ringWrite ring wpos byte hr).trans hsize) hnext
termination_by n.toNat
decreasing_by
  have := usize_pred hn
  have := usize_ne hn
  omega

/-- What the copy loop does: exactly the spec's `copyBytes`. -/
theorem copyRun_spec {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k) (out : List Nat), n.toNat = N → d.toNat ≤ out.length → RingOk ring k wpos.toNat out →
      contextBytes out = (p1.toNat, p2.toNat) → (∀ b ∈ out, b < 256) →
      let r := copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp
      RingOk r.ring k r.wpos.toNat (copyBytes d.toNat N out) ∧
        contextBytes (copyBytes d.toNat N out) = (r.p1.toNat, r.p2.toNat) ∧
        (∀ b ∈ copyBytes d.toNat N out, b < 256) ∧ (copyBytes d.toNat N out).length = out.length + N := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp out hN _ hr hc hb
    rw [copyRun, dite_eq_left (usize_zero hN)]
    exact ⟨hr, hc, hb, rfl⟩
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp out hN hd hr hc hb
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRun, dite_eq_right hn]
    dsimp only
    have hback := ringBack_toNat (pos := wpos) (d := d) hk hmask hsz hwp hd1 hd2
    have hbl : (ringBack wpos d mask size).toNat < ring.size := by
      rw [hback, hsize]
      exact ringIdx_lt hwp (by omega)
    have hval := hr.read hd1 hd2 hd hback hbl
    have hr' := hr.write (v := ring.uget (ringBack wpos d mask size) hbl) hk hmask (by omega)
    have hih := ih (n - USize.ofNat 1) (ringWrite ring wpos _ (by omega)) (ringNext wpos mask)
      (ring.uget (ringBack wpos d mask size) hbl) p1
      hr'.size hr'.pos_lt ((ring.uget (ringBack wpos d mask size) hbl).toNat :: out) (by rw [usize_pred hn]; omega)
      (by simp only [List.length_cons]; omega) hr' (by rw [contextBytes_push, hc]) (by
        intro b hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact UInt8.toNat_lt _
        · exact hb b hm)
    simp only [copyBytes]
    rw [← hval]
    obtain ⟨h1, h2, h3, h4⟩ := hih
    refine ⟨h1, h2, h3, ?_⟩
    rw [h4]
    simp only [List.length_cons]
    omega

/-- Writes the next `n` bytes of a dictionary word. -/
def wordRun (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (n idx : USize)
    (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
    (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : CopyRun :=
  if hn : n = 0 then ⟨ring, wpos, p1, p2⟩
  else
    have hnz := usize_ne hn
    have hpred := usize_pred hn
    let byte := buf.uget idx (by omega)
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    wordRun buf mask k hk hmask (n - USize.ofNat 1) (idx + USize.ofNat 1) (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1
      (by rw [hi]; omega) (by rw [hi]; omega) ((size_ringWrite ring wpos byte hr).trans hsize) hnext
termination_by n.toNat
decreasing_by
  omega

/-- What the word loop does: writes the next bytes of the word, newest first in the output. -/
theorem wordRun_spec {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
      (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (out : List Nat),
      n.toNat = N → RingOk ring k wpos.toNat out → contextBytes out = (p1.toNat, p2.toNat) → (∀ b ∈ out, b < 256) →
      let r := wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp
      let moved := ((buf.data.toList.drop idx.toNat).take N).map UInt8.toNat
      RingOk r.ring k r.wpos.toNat (moved.reverse ++ out) ∧
        contextBytes (moved.reverse ++ out) = (r.p1.toNat, r.p2.toNat) ∧ (∀ b ∈ moved.reverse ++ out, b < 256) := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp out hN hr hc hbytes
    rw [wordRun, dite_eq_left (usize_zero hN)]
    simp only [List.take_zero, List.map_nil, List.reverse_nil, List.nil_append]
    exact ⟨hr, hc, hbytes⟩
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp out hN hr hc hbytes
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [wordRun, dite_eq_right hn]
    dsimp only
    have hbl : idx.toNat < buf.size := by omega
    have hr' := hr.write (v := buf.uget idx hbl) hk hmask (by omega)
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    have hih := ih (n - USize.ofNat 1) (idx + USize.ofNat 1) (ringWrite ring wpos _ (by omega)) (ringNext wpos mask) (buf.uget idx hbl) p1
      (by rw [hi]; omega) (by rw [hi]; omega) hr'.size hr'.pos_lt ((buf.uget idx hbl).toNat :: out) (by omega) hr'
      (by rw [contextBytes_push, hc]) (by
        intro b hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact UInt8.toNat_lt _
        · exact hbytes b hm)
    dsimp only at hih
    have hl : idx.toNat < buf.data.toList.length := by
      have : buf.size = buf.data.size := rfl
      simp only [Array.length_toList]
      omega
    have hdrop : buf.data.toList.drop idx.toNat = buf.data.toList[idx.toNat] :: buf.data.toList.drop (idx.toNat + 1) :=
      List.drop_eq_getElem_cons hl
    have huget : buf.uget idx hbl = buf.data.toList[idx.toNat] := by
      cases buf with
      | mk bs => simp [ByteArray.uget]
    generalize wordRun buf mask k hk hmask (n - USize.ofNat 1) (idx + USize.ofNat 1) _ _ _ _ _ _ _ _ = r at hih ⊢
    rw [hi] at hih
    rw [hdrop, List.take_succ_cons, List.map_cons, List.reverse_cons, List.append_assoc, ← huget]
    exact hih

end Brotli.Decoder
