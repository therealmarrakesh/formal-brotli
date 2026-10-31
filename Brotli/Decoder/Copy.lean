import Brotli.Decoder.Rest
import Brotli.Decoder.Window

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

/-- Copies `n` bytes from `d` back. -/
def copyRun (d mask size : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k)
    (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    (n : Nat) → (ring : ByteArray) → (wpos : USize) → (p1 p2 : UInt8) → ring.size = 2 ^ k → wpos.toNat < 2 ^ k → CopyRun
  | 0, ring, wpos, p1, p2, _, _ => ⟨ring, wpos, p1, p2⟩
  | n + 1, ring, wpos, p1, _, hsize, hwp =>
    have hb : (ringBack wpos d mask size).toNat < ring.size := by
      rw [ringBack_toNat hk hmask hsz hwp hd1 hd2, hsize]
      exact ringIdx_lt hwp (by omega)
    let byte := ring.uget (ringBack wpos d mask size) hb
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    copyRun d mask size k hk hmask hsz hd1 hd2 n (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1
      ((size_ringWrite ring wpos byte hr).trans hsize) hnext

/-- What the copy loop does: exactly the spec's `copyBytes`. -/
theorem copyRun_spec {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (n : Nat) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k)
      (out : List Nat), d.toNat ≤ out.length → RingOk ring k wpos.toNat out → contextBytes out = (p1.toNat, p2.toNat) →
      (∀ b ∈ out, b < 256) →
      let r := copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp
      RingOk r.ring k r.wpos.toNat (copyBytes d.toNat n out) ∧
        contextBytes (copyBytes d.toNat n out) = (r.p1.toNat, r.p2.toNat) ∧
        (∀ b ∈ copyBytes d.toNat n out, b < 256) ∧ (copyBytes d.toNat n out).length = out.length + n := by
  intro n
  induction n with
  | zero =>
    intro ring wpos p1 p2 hsize hwp out _ hr hc hb
    exact ⟨hr, hc, hb, rfl⟩
  | succ n ih =>
    intro ring wpos p1 p2 hsize hwp out hd hr hc hb
    rw [copyRun]
    dsimp only
    have hback := ringBack_toNat (pos := wpos) (d := d) hk hmask hsz hwp hd1 hd2
    have hbl : (ringBack wpos d mask size).toNat < ring.size := by
      rw [hback, hsize]
      exact ringIdx_lt hwp (by omega)
    have hval := hr.read hd1 hd2 hd hback hbl
    have hr' := hr.write (v := ring.uget (ringBack wpos d mask size) hbl) hk hmask (by omega)
    have hih := ih (ringWrite ring wpos _ (by omega)) (ringNext wpos mask) (ring.uget (ringBack wpos d mask size) hbl) p1
      hr'.size hr'.pos_lt ((ring.uget (ringBack wpos d mask size) hbl).toNat :: out)
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
def wordRun (buf : ByteArray) (mask : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    (n : Nat) → (idx : USize) → (ring : ByteArray) → (wpos : USize) → (p1 p2 : UInt8) → idx.toNat + n ≤ buf.size →
    idx.toNat + n ≤ 2 ^ 32 - 1 → ring.size = 2 ^ k → wpos.toNat < 2 ^ k → CopyRun
  | 0, _, ring, wpos, p1, p2, _, _, _, _ => ⟨ring, wpos, p1, p2⟩
  | n + 1, idx, ring, wpos, p1, _, hb, hb32, hsize, hwp =>
    let byte := buf.uget idx (by omega)
    have hr : wpos.toNat < ring.size := by omega
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    wordRun buf mask k hk hmask n (idx + USize.ofNat 1) (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1
      (by rw [hi]; omega) (by rw [hi]; omega) ((size_ringWrite ring wpos byte hr).trans hsize) hnext

/-- What the word loop does: writes the next bytes of the word, newest first in the output. -/
theorem wordRun_spec {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (n : Nat) (idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n ≤ buf.size)
      (hb32 : idx.toNat + n ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (out : List Nat),
      RingOk ring k wpos.toNat out → contextBytes out = (p1.toNat, p2.toNat) → (∀ b ∈ out, b < 256) →
      let r := wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp
      let moved := ((buf.data.toList.drop idx.toNat).take n).map UInt8.toNat
      RingOk r.ring k r.wpos.toNat (moved.reverse ++ out) ∧
        contextBytes (moved.reverse ++ out) = (r.p1.toNat, r.p2.toNat) ∧ (∀ b ∈ moved.reverse ++ out, b < 256) := by
  intro n
  induction n with
  | zero =>
    intro idx ring wpos p1 p2 hb hb32 hsize hwp out hr hc hbytes
    simp only [wordRun, List.take_zero, List.map_nil, List.reverse_nil, List.nil_append]
    exact ⟨hr, hc, hbytes⟩
  | succ n ih =>
    intro idx ring wpos p1 p2 hb hb32 hsize hwp out hr hc hbytes
    rw [wordRun]
    dsimp only
    have hbl : idx.toNat < buf.size := by omega
    have hr' := hr.write (v := buf.uget idx hbl) hk hmask (by omega)
    have hi : (idx + USize.ofNat 1).toNat = idx.toNat + 1 := usize_succ (by omega)
    have hih := ih (idx + USize.ofNat 1) (ringWrite ring wpos _ (by omega)) (ringNext wpos mask) (buf.uget idx hbl) p1
      (by rw [hi]; omega) (by rw [hi]; omega) hr'.size hr'.pos_lt ((buf.uget idx hbl).toNat :: out) hr'
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
    generalize wordRun buf mask k hk hmask n (idx + USize.ofNat 1) _ _ _ _ _ _ _ _ = r at hih ⊢
    rw [hi] at hih
    rw [hdrop, List.take_succ_cons, List.map_cons, List.reverse_cons, List.append_assoc, ← huget]
    exact hih

end Brotli.Decoder
