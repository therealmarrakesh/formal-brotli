module

public import Brotli.FastDecoder.Prim

@[expose] public section

/-!
# The bit reader

The input is read from `buf` at `bitpos`, the position of the next unread bit (`DESIGN.md` 5.4). A refill is computed
from `bitpos` alone and consuming bits adds to `bitpos`, so no word of bits and no count of them is carried.
-/

namespace Brotli.FastDecoder

/-- The bits from `bitpos` on, the next unread bit lowest: at least 57 of them. One load and one shift. -/
@[inline] def refill (buf : ByteArray) (bitpos : UInt64) (h : (bitpos >>> 3).toNat + 8 ≤ buf.size) : UInt64 :=
  load64 buf (bitpos >>> 3) h >>> (bitpos &&& 7)

/-- The low `n` bits set, for `n` below 64. -/
@[inline] def mask (n : UInt64) : UInt64 :=
  ((1 : UInt64) <<< n) - 1
