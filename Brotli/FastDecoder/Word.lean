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

/-- Every letter from `i` to `stop` to upper case. -/
def upperAll (buf : ByteArray) (i stop : UInt64) : ByteArray :=
  if i < stop then
    let b := load8 buf i owed
    upperAll (upperAt buf i b) (i + (if b < 192 then 1 else if b < 224 then 2 else 3)) stop
  else buf
termination_by stop.toNat - i.toNat
decreasing_by exact owed

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
    else upperAll buf p (p + n)
  store64 buf (p + n) (load64 transTab (row + 16) owed) owed
