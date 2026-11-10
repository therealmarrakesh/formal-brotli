module

@[expose] public section

/-!
# Primitives

The loads, stores, copies and fills of bytes within one `ByteArray` that the decoder is written with, and the only
place it uses `@[extern]` (`AGENTS.md`, Trust; `DESIGN.md` 2.5).

Each primitive is an ordinary definition. Its body is the model the proofs use, written with one of four small
functions (`leLoad`, `leStore`, `snapCopy`, `leFill`). At compile time its `@[extern c inline]` C replaces the body: a
plain access or one `memcpy` or `memmove` of a fixed or given length, after `lean_sarray_ensure_exclusive` where it
writes (the test `ByteArray.uset` makes, copying the array if it is held more than once, so the result is a new value
exactly as the body's). Every range is inside the array by the primitive's signature, so the C never reads or writes
outside it. The C is trusted to match the body, as the runtime's own `ByteArray` operations are; a load or store wider
than a byte fails to compile on a target that is not little-endian.

Positions and values are `UInt64` throughout, so the decoder's arithmetic has one type. A position that satisfies a
primitive's hypothesis is below the array's size, so the C's conversion to `size_t` loses nothing.
-/

namespace Brotli.FastDecoder

/-! ### The models -/

/-- The `n` bytes from `i` as a number, little-endian (a byte outside the array counts as zero). -/
def leLoad (t : ByteArray) (i : Nat) : Nat → UInt64
  | 0 => 0
  | n + 1 => (t.data[i]?.getD 0).toUInt64 ||| (leLoad t (i + 1) n <<< 8)

/-- The low `n` bytes of `v` written from `i`, little-endian. -/
def leStore (t : ByteArray) (i : Nat) (v : UInt64) : Nat → ByteArray
  | 0 => t
  | n + 1 => leStore ⟨t.data.setIfInBounds i v.toUInt8⟩ (i + 1) (v >>> 8) n

/-- `n` bytes copied from `s` to `d` as a snapshot: every byte written is the byte its source held before the copy. -/
def snapCopy (t : ByteArray) (d s n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := t.size) fun j => t.data[if d ≤ j.val ∧ j.val < d + n then s + (j.val - d) else j.val]?.getD 0⟩

/-- `n` stores of the low `w` bytes of `v`, the first at `i` and each `s` bytes after the last. -/
def leFill (t : ByteArray) (i s : Nat) (v : UInt64) (w : Nat) : Nat → ByteArray
  | 0 => t
  | n + 1 => leFill (leStore t i v w) (i + s) s v w n

theorem leStore_size (t : ByteArray) (i : Nat) (v : UInt64) (n : Nat) : (leStore t i v n).size = t.size := by
  induction n generalizing t i v with
  | zero => rfl
  | succ n ih =>
    rw [leStore, ih]
    show (t.data.setIfInBounds i v.toUInt8).size = t.data.size
    rw [Array.size_setIfInBounds]

theorem snapCopy_size (t : ByteArray) (d s n : Nat) : (snapCopy t d s n).size = t.size :=
  Array.size_ofFn

theorem leFill_size (t : ByteArray) (i s : Nat) (v : UInt64) (w n : Nat) : (leFill t i s v w n).size = t.size := by
  induction n generalizing t i with
  | zero => rfl
  | succ n ih => rw [leFill, ih, leStore_size]

/-! ### Loads -/

/-- The byte at `i`. -/
@[extern c inline "((uint64_t)lean_sarray_cptr(#1)[(size_t)(#2)])"]
def load8 (t : @& ByteArray) (i : UInt64) (_h : i.toNat + 1 ≤ t.size) : UInt64 :=
  leLoad t i.toNat 1

/-- The 2 bytes at `i`, little-endian. One load. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); uint16_t v_; __builtin_memcpy(&v_, lean_sarray_cptr(#1) + (size_t)(#2), 2); (uint64_t)v_; })"]
def load16 (t : @& ByteArray) (i : UInt64) (_h : i.toNat + 2 ≤ t.size) : UInt64 :=
  leLoad t i.toNat 2

/-- The 4 bytes at `i`, little-endian. One load. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); uint32_t v_; __builtin_memcpy(&v_, lean_sarray_cptr(#1) + (size_t)(#2), 4); (uint64_t)v_; })"]
def load32 (t : @& ByteArray) (i : UInt64) (_h : i.toNat + 4 ≤ t.size) : UInt64 :=
  leLoad t i.toNat 4

/-- The 8 bytes at `i`, little-endian. One load. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); uint64_t v_; __builtin_memcpy(&v_, lean_sarray_cptr(#1) + (size_t)(#2), 8); v_; })"]
def load64 (t : @& ByteArray) (i : UInt64) (_h : i.toNat + 8 ≤ t.size) : UInt64 :=
  leLoad t i.toNat 8

/-! ### Stores -/

/-- `v`'s low byte written at `i`. -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); lean_sarray_cptr(r_)[(size_t)(#2)] = (uint8_t)(#3); r_; })"]
def store8 (t : ByteArray) (i v : UInt64) (_h : i.toNat + 1 ≤ t.size) : ByteArray :=
  leStore t i.toNat v 1

/-- `v`'s low 2 bytes written from `i`, little-endian. One store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint16_t v_ = (uint16_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + (size_t)(#2), &v_, 2); r_; })"]
def store16 (t : ByteArray) (i v : UInt64) (_h : i.toNat + 2 ≤ t.size) : ByteArray :=
  leStore t i.toNat v 2

/-- `v`'s low 4 bytes written from `i`, little-endian. One store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint32_t v_ = (uint32_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + (size_t)(#2), &v_, 4); r_; })"]
def store32 (t : ByteArray) (i v : UInt64) (_h : i.toNat + 4 ≤ t.size) : ByteArray :=
  leStore t i.toNat v 4

/-- `v`'s 8 bytes written from `i`, little-endian. One store. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint64_t v_ = (uint64_t)(#3); __builtin_memcpy(lean_sarray_cptr(r_) + (size_t)(#2), &v_, 8); r_; })"]
def store64 (t : ByteArray) (i v : UInt64) (_h : i.toNat + 8 ≤ t.size) : ByteArray :=
  leStore t i.toNat v 8

@[simp] theorem store8_size (t : ByteArray) (i v : UInt64) (h : i.toNat + 1 ≤ t.size) :
    (store8 t i v h).size = t.size := leStore_size ..

@[simp] theorem store16_size (t : ByteArray) (i v : UInt64) (h : i.toNat + 2 ≤ t.size) :
    (store16 t i v h).size = t.size := leStore_size ..

@[simp] theorem store32_size (t : ByteArray) (i v : UInt64) (h : i.toNat + 4 ≤ t.size) :
    (store32 t i v h).size = t.size := leStore_size ..

@[simp] theorem store64_size (t : ByteArray) (i v : UInt64) (h : i.toNat + 8 ≤ t.size) :
    (store64 t i v h).size = t.size := leStore_size ..

/-! ### Copies -/

/-- 8 bytes copied from `s` to `d`, the two ranges apart. One 8-byte load and one store. -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); __builtin_memcpy(lean_sarray_cptr(r_) + (size_t)(#2), lean_sarray_cptr(r_) + (size_t)(#3), 8); r_; })"]
def copy8 (t : ByteArray) (d s : UInt64)
    (_h : d.toNat + 8 ≤ t.size ∧ s.toNat + 8 ≤ t.size ∧ (s.toNat + 8 ≤ d.toNat ∨ d.toNat + 8 ≤ s.toNat)) :
    ByteArray :=
  snapCopy t d.toNat s.toNat 8

/-- 16 bytes copied from `s` to `d`, the two ranges apart. One 16-byte load and one store. -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); __builtin_memcpy(lean_sarray_cptr(r_) + (size_t)(#2), lean_sarray_cptr(r_) + (size_t)(#3), 16); r_; })"]
def copy16 (t : ByteArray) (d s : UInt64)
    (_h : d.toNat + 16 ≤ t.size ∧ s.toNat + 16 ≤ t.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat)) :
    ByteArray :=
  snapCopy t d.toNat s.toNat 16

/-- `n` bytes copied from `s` to `d` as a snapshot, the ranges free to overlap. A `memmove`. -/
@[extern c inline "({ lean_object * r_ = lean_sarray_ensure_exclusive(#1); __builtin_memmove(lean_sarray_cptr(r_) + (size_t)(#2), lean_sarray_cptr(r_) + (size_t)(#3), (size_t)(#4)); r_; })"]
def move (t : ByteArray) (d s n : UInt64) (_h : d.toNat + n.toNat ≤ t.size ∧ s.toNat + n.toNat ≤ t.size) :
    ByteArray :=
  snapCopy t d.toNat s.toNat n.toNat

@[simp] theorem copy8_size (t : ByteArray) (d s : UInt64)
    (h : d.toNat + 8 ≤ t.size ∧ s.toNat + 8 ≤ t.size ∧ (s.toNat + 8 ≤ d.toNat ∨ d.toNat + 8 ≤ s.toNat)) :
    (copy8 t d s h).size = t.size := snapCopy_size ..

@[simp] theorem copy16_size (t : ByteArray) (d s : UInt64)
    (h : d.toNat + 16 ≤ t.size ∧ s.toNat + 16 ≤ t.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat)) :
    (copy16 t d s h).size = t.size := snapCopy_size ..

@[simp] theorem move_size (t : ByteArray) (d s n : UInt64)
    (h : d.toNat + n.toNat ≤ t.size ∧ s.toNat + n.toNat ≤ t.size) :
    (move t d s n h).size = t.size := snapCopy_size ..

/-! ### A strided fill -/

/-- `v`'s low 2 bytes written `n` times, the first at `i` and each `s` bytes after the last, little-endian. One test
that the array is held once, then a loop of 2-byte stores. -/
@[extern c inline "({ _Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, \"little-endian target\"); lean_object * r_ = lean_sarray_ensure_exclusive(#1); uint8_t * p_ = lean_sarray_cptr(r_); uint64_t i_ = (#2), s_ = (#3), n_ = (#4); uint16_t v_ = (uint16_t)(#5); for (uint64_t k_ = 0; k_ < n_; k_++) __builtin_memcpy(p_ + (size_t)(i_ + k_ * s_), &v_, 2); r_; })"]
def fill16 (t : ByteArray) (i s n v : UInt64) (_h : ∀ k, k < n.toNat → i.toNat + k * s.toNat + 2 ≤ t.size) :
    ByteArray :=
  leFill t i.toNat s.toNat v 2 n.toNat

@[simp] theorem fill16_size (t : ByteArray) (i s n v : UInt64)
    (h : ∀ k, k < n.toNat → i.toNat + k * s.toNat + 2 ≤ t.size) :
    (fill16 t i s n v h).size = t.size := leFill_size ..
