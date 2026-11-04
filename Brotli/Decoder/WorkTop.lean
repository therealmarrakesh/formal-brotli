import Brotli.Decoder.WorkIface

/-!
# The decoder's work, call by call
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A state at a place holds at most 64 bits. -/
theorem DRel.held_le {D : Dec} {p : SPhase} (h : DRel D p) : D.held.length ≤ 64 := by
  have hw : (BitBuffer.mk D.word D.count).Wf := by
    unfold Dec.word Dec.count
    cases p with
    | wbits => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | mblock => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | skip => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | raw => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
    | hdr => obtain ⟨ht, _, _, _, _, _, hh, _⟩ := h; rw [ht]; exact hh.wf
    | cmds => obtain ⟨ht, _, _, _, hr⟩ := h; rw [ht]; exact hr.wf
    | ended => obtain ⟨ht, hw, _⟩ := h; rw [ht]; exact hw
  unfold Dec.held
  rw [BitBuffer.held_length]
  exact hw.count_le

end Brotli.Decoder
