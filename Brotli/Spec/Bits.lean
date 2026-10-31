/-!
# Packing into bytes

RFC 7932 §1.5. Readers return `(value, rest)`, or `none` when the input ends first.
-/

namespace Brotli.Spec

/-- The stream as bits: each byte's bits, least significant first (§1.5). -/
def bits (bs : List UInt8) : List Bool :=
  bs.flatMap fun b => (List.range 8).map b.toNat.testBit

/-- An `n`-bit integer, least significant bit first (§1.5.1). -/
def readInt : Nat → List Bool → Option (Nat × List Bool)
  | 0, s => some (0, s)
  | _ + 1, [] => none
  | n + 1, b :: s => (readInt n s).map fun (v, rest) => (b.toNat + 2 * v, rest)

/-- An `n`-bit prefix code, most significant bit first (§1.5.1). -/
def readCode : Nat → List Bool → Option (Nat × List Bool)
  | 0, s => some (0, s)
  | _ + 1, [] => none
  | n + 1, b :: s => (readCode n s).map fun (v, rest) => (b.toNat * 2 ^ n + v, rest)

/-- An `n`-bit prefix code is less than `2 ^ n`. -/
theorem readCode_lt : ∀ (n : Nat) (bs : List Bool) (v : Nat) (r : List Bool),
    readCode n bs = some (v, r) → v < 2 ^ n
  | 0, _, _, _, h => by simp [readCode] at h; omega
  | _ + 1, [], _, _, h => by simp [readCode] at h
  | n + 1, b :: bs, v, r, h => by
    simp only [readCode] at h
    cases hr : readCode n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨w, r'⟩ := p
      have hw := readCode_lt n bs w r' hr
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [Nat.pow_succ]
      cases b <;> simp at h <;> omega

/-- An integer value of `n` bits is less than `2 ^ n`. -/
theorem readInt_lt : ∀ (n : Nat) (bs : List Bool) (v : Nat) (r : List Bool),
    readInt n bs = some (v, r) → v < 2 ^ n
  | 0, _, _, _, h => by simp [readInt] at h; omega
  | _ + 1, [], _, _, h => by simp [readInt] at h
  | n + 1, b :: bs, v, r, h => by
    simp only [readInt] at h
    cases hr : readInt n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨w, r'⟩ := p
      have hw := readInt_lt n bs w r' hr
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [Nat.pow_succ]
      cases b <;> simp at h <;> omega

/-- Every value below `2 ^ n` is the prefix code read from some `n` bits. -/
theorem readCode_of_lt : ∀ (n c : Nat), c < 2 ^ n → ∃ w, readCode n w = some (c, [])
  | 0, c, h => ⟨[], by simp [readCode]; omega⟩
  | n + 1, c, h => by
    rw [Nat.pow_succ] at h
    by_cases hb : 2 ^ n ≤ c
    · obtain ⟨w, hw⟩ := readCode_of_lt n (c - 2 ^ n) (by omega)
      exact ⟨true :: w, by simp [readCode, hw]; omega⟩
    · obtain ⟨w, hw⟩ := readCode_of_lt n c (by omega)
      exact ⟨false :: w, by simp [readCode, hw]⟩

/-- Reading `a + b` bits as a prefix code reads `a` bits, then `b` more as the lower part. -/
theorem readCode_add (a b : Nat) (s : List Bool) :
    readCode (a + b) s =
      (readCode a s).bind fun (v, r) => (readCode b r).map fun (w, r') => (v * 2 ^ b + w, r') := by
  induction a generalizing s with
  | zero =>
    simp only [Nat.zero_add, readCode, Option.bind_some, Nat.zero_mul]
    cases readCode b s <;> simp
  | succ a ih =>
    rw [Nat.add_right_comm]
    cases s with
    | nil => simp [readCode]
    | cons x s =>
      simp only [readCode, ih]
      cases readCode a s with
      | none => simp
      | some p =>
        obtain ⟨v, r⟩ := p
        simp only [Option.bind_some, Option.map_some]
        cases readCode b r with
        | none => simp
        | some q =>
          obtain ⟨w, r'⟩ := q
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
          rw [Nat.pow_add]
          grind

/-- A prefix code read from `w` alone, with no bits left, reads the same from `w ++ rest`. -/
theorem readCode_append : ∀ (n : Nat) (w : List Bool) (c : Nat) (rest : List Bool),
    readCode n w = some (c, []) → readCode n (w ++ rest) = some (c, rest)
  | 0, w, c, rest, h => by
    simp only [readCode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [readCode]
  | _ + 1, [], _, _, h => by simp [readCode] at h
  | n + 1, b :: w, c, rest, h => by
    simp only [readCode] at h
    cases hr : readCode n w with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v, r⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [readCode, readCode_append n w v rest hr]

/-- The bits a prefix code is read from: `bs` is some `w` followed by what remains, and the code
is read from `w` alone. -/
theorem readCode_split : ∀ (n : Nat) (bs : List Bool) (c : Nat) (r : List Bool),
    readCode n bs = some (c, r) → ∃ w, bs = w ++ r ∧ readCode n w = some (c, [])
  | 0, bs, c, r, h => by
    simp only [readCode, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, rfl⟩
  | _ + 1, [], _, _, h => by simp [readCode] at h
  | n + 1, b :: bs, c, r, h => by
    simp only [readCode] at h
    cases hr : readCode n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v, r'⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨w, hw, hcw⟩ := readCode_split n bs v r' hr
      exact ⟨b :: w, by simp [hw], by simp [readCode, hcw]⟩

/-- Reading `a + b` bits reads `a` bits, then `b` more as the higher part. -/
private theorem readInt_add (a b : Nat) (s : List Bool) :
    readInt (a + b) s =
      (readInt a s).bind fun (v, r) => (readInt b r).map fun (w, r') => (v + 2 ^ a * w, r') := by
  induction a generalizing s with
  | zero =>
    simp only [Nat.zero_add, readInt, Option.bind_some, Nat.pow_zero, Nat.one_mul]
    cases readInt b s <;> simp
  | succ a ih =>
    rw [Nat.add_right_comm]
    cases s with
    | nil => simp [readInt]
    | cons x s =>
      simp only [readInt, ih]
      cases readInt a s with
      | none => simp
      | some p =>
        obtain ⟨v, r⟩ := p
        simp only [Option.bind_some, Option.map_some]
        cases readInt b r with
        | none => simp
        | some q =>
          obtain ⟨w, r'⟩ := q
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
          rw [Nat.pow_succ]
          grind

private theorem readInt_byte (b : UInt8) (s : List Bool) :
    readInt 8 ((List.range 8).map b.toNat.testBit ++ s) = some (b.toNat, s) := by
  have key : ∀ n < 256,
      (n.testBit 0).toNat + 2 * ((n.testBit 1).toNat + 2 * ((n.testBit 2).toNat +
        2 * ((n.testBit 3).toNat + 2 * ((n.testBit 4).toNat + 2 * ((n.testBit 5).toNat +
        2 * ((n.testBit 6).toNat + 2 * ((n.testBit 7).toNat + 2 * 0))))))) = n := by
    decide +kernel
  simp only [List.range, List.range.loop, List.map, List.cons_append, List.nil_append, readInt,
    Option.map_some]
  rw [key b.toNat b.toNat_lt]

private theorem zipIdx_sum_succ (bs : List UInt8) (k : Nat) :
    ((bs.zipIdx (k + 1)).map fun (b, i) => b.toNat * 256 ^ i).sum =
      256 * ((bs.zipIdx k).map fun (b, i) => b.toNat * 256 ^ i).sum := by
  induction bs generalizing k with
  | nil => simp
  | cons b bs ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, ih (k + 1)]
    rw [Nat.pow_succ]
    grind

/-- Multi-byte numbers are least significant byte first (§1.5). -/
theorem readInt_bits (bs rest : List UInt8) :
    readInt (8 * bs.length) (bits (bs ++ rest)) =
      some ((bs.zipIdx.map fun (b, i) => b.toNat * 256 ^ i).sum, bits rest) := by
  induction bs with
  | nil => simp [readInt]
  | cons b bs ih =>
    have h : 8 * (b :: bs).length = 8 + 8 * bs.length := by simp; omega
    rw [h, readInt_add]
    simp only [bits, List.cons_append, List.flatMap_cons] at ih ⊢
    rw [readInt_byte]
    simp only [Option.bind_some, ih, Option.map_some, List.zipIdx_cons, List.map_cons,
      List.sum_cons, Nat.pow_zero, Nat.mul_one, zipIdx_sum_succ]

end Brotli.Spec
