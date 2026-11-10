module

@[expose] public section

/-!
# Counting with `UInt64`

What a loop's termination needs of a counter that goes down by one or up by one below a bound.
-/

namespace Brotli.FastDecoder

/-- A counter that is not zero goes down. -/
theorem pred_lt {a : UInt64} (h : a ≠ 0) : (a - 1).toNat < a.toNat := by
  have h1 : (1 : UInt64) ≤ a := by
    rw [UInt64.le_iff_toNat_le]
    have : a.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp e)
    show 1 ≤ a.toNat
    omega
  rw [UInt64.toNat_sub_of_le a 1 h1]
  have : a.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp e)
  show a.toNat - 1 < a.toNat
  omega

/-- A counter below a bound goes up by one. -/
theorem succ_toNat {a b : UInt64} (h : a < b) : (a + 1).toNat = a.toNat + 1 := by
  have h1 := UInt64.lt_iff_toNat_lt.mp h
  have h2 := b.toNat_lt
  rw [UInt64.toNat_add]
  show (a.toNat + 1) % 2 ^ 64 = a.toNat + 1
  omega

/-- A counter below a bound comes nearer to it. -/
theorem succ_nearer {a b : UInt64} (h : a < b) : b.toNat - (a + 1).toNat < b.toNat - a.toNat := by
  have h1 := UInt64.lt_iff_toNat_lt.mp h
  rw [succ_toNat h]
  omega

/-- A mask that is not empty loses its lowest bit. -/
theorem and_pred_lt {m : UInt64} (h : m ≠ 0) : (m &&& (m - 1)).toNat < m.toNat := by
  have h1 := pred_lt h
  have h2 : (m &&& (m - 1)).toNat ≤ (m - 1).toNat := by
    rw [UInt64.toNat_and]
    exact Nat.and_le_right
  omega
