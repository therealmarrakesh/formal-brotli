module

public import Brotli.FastDecoder.Dict
public import Brotli.FastDecoder.Num
public import Brotli.FastDecoder.Owed

@[expose] public section

/-!
# A dictionary word

A transformed word of the static dictionary written straight into the ring (`DESIGN.md` 5.6): the prefix, the base
word and the suffix, each by blocks of 8 bytes from the exact end of the one before. A block may write up to 7 bytes
past what it is for; the next part overwrites them, and the last ones fall in the slack.

The command loop works out the word's place in the dictionary and its length; `wordPut` is the one call that writes
it.
-/

namespace Brotli.FastDecoder

/-- The letter at `i` to upper case, as the format defines it for UTF-8: one byte changed, in a character of one, two
or three bytes. A change that falls past the word is overwritten by what is written after the word. -/
@[inline] def upperAt (buf : ByteArray) (i b : UInt64) : ByteArray :=
  if b < 192 then
    if 97 ≤ b ∧ b ≤ 122 then store8 buf i (b ^^^ 32) owed else buf
  else if b < 224 then store8 buf (i + 1) (load8 buf (i + 1) owed ^^^ 32) owed
  else store8 buf (i + 2) (load8 buf (i + 2) owed ^^^ 5) owed

@[simp] theorem upperAt_size (buf : ByteArray) (i b : UInt64) : (upperAt buf i b).size = buf.size := by
  unfold upperAt
  split
  · split <;> simp
  · split <;> simp

/-- The bytes of a letter that starts with `b`: 1, 2 or 3. -/
@[inline] def letterBytes (b : UInt64) : UInt64 :=
  if b < 192 then 1 else if b < 224 then 2 else 3

theorem letterBytes_ne (b : UInt64) : letterBytes b ≠ 0 := by
  unfold letterBytes
  split
  · decide
  · split <;> decide

/-- The bytes a letter that starts with `b` takes of the `n` left: no more than are left. -/
@[inline] def letterLen (b n : UInt64) : UInt64 :=
  if letterBytes b ≤ n then letterBytes b else n

theorem letterLen_le (b n : UInt64) : letterLen b n ≤ n := by
  unfold letterLen
  split
  · assumption
  · exact UInt64.le_refl n

theorem letterLen_ne (b : UInt64) {n : UInt64} (hn : n ≠ 0) : letterLen b n ≠ 0 := by
  unfold letterLen
  split
  · exact letterBytes_ne b
  · exact hn

/-- Taking away some of what is left, and not nothing, leaves less. -/
theorem sub_lt_of_ne {n k : UInt64} (hk : k ≠ 0) (hkn : k ≤ n) : (n - k).toNat < n.toNat := by
  rw [UInt64.toNat_sub_of_le n k hkn]
  have h1 : k.toNat ≠ 0 := fun e => hk (UInt64.toNat_inj.mp e)
  have h2 : k.toNat ≤ n.toNat := UInt64.le_iff_toNat_le.mp hkn
  omega

/-- Every letter of the `n` bytes from `i` to upper case. -/
def upperAll (buf : ByteArray) (i n : UInt64) : ByteArray :=
  if hn : n = 0 then buf
  else
    let b := load8 buf i owed
    have : (n - letterLen b n).toNat < n.toNat := sub_lt_of_ne (letterLen_ne b hn) (letterLen_le b n)
    upperAll (upperAt buf i b) (i + letterLen b n) (n - letterLen b n)
termination_by n.toNat

@[simp] theorem upperAll_size (buf : ByteArray) (i n : UInt64) : (upperAll buf i n).size = buf.size := by
  induction buf, i, n using upperAll.induct with
  | case1 buf i => rw [upperAll]; simp
  | case2 buf i n hn b _ ih => rw [upperAll]; simp only [hn, ↓reduceDIte]; rw [ih]; simp

/-- The word written at `opos`: the transform `tid` of the `n` bytes of the dictionary at `src`. -/
@[noinline] def wordPut (buf : ByteArray) (opos src n tid : UInt64) : ByteArray :=
  let row := tid <<< 5
  let t := load64 transTab row owed
  let buf := store64 buf opos (load64 transTab (row + 8) owed) owed
  let p := opos + ((t >>> 24) &&& 0xFF)
  let buf := store64 buf p (load64 dict src owed) owed
  let buf := if 8 < n then store64 buf (p + 8) (load64 dict (src + 8) owed) owed else buf
  let buf := if 16 < n then store64 buf (p + 16) (load64 dict (src + 16) owed) owed else buf
  let kind := t &&& 0xFF
  let buf :=
    if kind = 0 then buf
    else if kind = 1 then upperAt buf p (load8 buf p owed)
    else upperAll buf p n
  store64 buf (p + n) (load64 transTab (row + 16) owed) owed

@[simp] theorem wordPut_size (buf : ByteArray) (opos src n tid : UInt64) :
    (wordPut buf opos src n tid).size = buf.size := by
  unfold wordPut
  simp only [store64_size]
  repeat' split
  all_goals simp
