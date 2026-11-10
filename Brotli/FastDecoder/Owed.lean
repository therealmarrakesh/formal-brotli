module

@[expose] public section

/-!
# What the prototype owes

The decoder is designed and measured before it is proved (`DESIGN.md` 1, 7). Until then a fact that rests on the
decoder's whole invariant (`DESIGN.md` 6) is written `owed` where it is needed, and the signature of whatever uses it
states exactly what is owed there. A fact that follows from what is visible at the point of use is proved there
instead, never owed.

This is the new decoder's only `sorry` (`AGENTS.md`, Project). Proofs are erased when the code is compiled, so paying
an `owed` changes nothing that runs. The decoder is proved when no use of `owed` is left and this file is gone.
-/

namespace Brotli.FastDecoder

set_option warningAsError false in
/-- A proof owed to the decoder's invariant. -/
theorem owed {P : Prop} : P := sorry
