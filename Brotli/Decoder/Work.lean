import Brotli.Decoder.Progress
import Brotli.Decoder.Waiting

/-!
# Steps of the reading in order

What the work bound's proofs use of the spec's reading in order: a step of the command loop that goes on takes at least one
of its steps, and handing bytes out adds the bytes waiting, or as many as the space takes.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Two places apart take at least one step. -/
theorem Reach.count_pos {P E : Type} {step : P → List Bool → ORes P E} {p q : P} {bs c : List Bool} (h : Reach step p bs q c)
    (hne : ¬ (q = p ∧ c = bs)) : ∃ n, 1 ≤ n ∧ ReachN step n p bs q c := by
  obtain ⟨n, hn⟩ := h.count
  cases hn with
  | refl => exact absurd ⟨rfl, rfl⟩ hne
  | next hs hr => exact ⟨_, by omega, .next hs hr⟩

theorem ReachN.trans {P E : Type} {step : P → List Bool → ORes P E} {n m : Nat} {p q r : P} {a b c : List Bool}
    (h1 : ReachN step n p a q b) (h2 : ReachN step m q b r c) : ReachN step (n + m) p a r c := by
  induction h1 with
  | refl => simpa using h2
  | next hs _ ih =>
    rw [Nat.add_right_comm]
    exact .next hs (ih h2)

/-- A step of the command loop that goes on takes at least one step of the reading in order. -/
theorem stepCmd_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hH : HdrRel H m) (hrel : Rel w k.toNat m st p)
    (hp : pos.toNat ≤ stop.toNat) (hn : (stepCmd H k a stop hs st pos).status = .next) :
    ∃ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' ∧ OutStep p p' st (stepCmd H k a stop hs st pos) ∧
      (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧ pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧
      ∀ F, ∃ n, 1 ≤ n ∧ ReachN (cStep w m) n p (stateBits st a pos stop F) p'
        (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F) := by
  by_cases hc : ∃ s, p = .command s
  · obtain ⟨s, rfl⟩ := hc
    obtain ⟨ic, hR, h1, h2, h0, hne⟩ := (stepCmd_start (hs := hs) hH hrel hp).1 hn
    have hout : OutStep (.command s) (.insertCopy s ic) st (stepCmd H k a stop hs st pos) :=
      ⟨[], rfl, by rw [stepCmd_pend_command hrel.2.1]; rfl⟩
    refine ⟨.insertCopy s ic, hR, hout, h2, h1, fun F => ⟨1, Nat.le_refl _, .next ?_ (.refl _ _)⟩⟩
    rw [cStep_command _ h0]
    have hsw : ¬ (s.insertCopy.count = 0 ∧ m.insertCopy.n < 2) := fun e => by
      have := hne F
      rw [nextElement_single _ e.1 e.2] at this
      cases this
    rw [nextIn_some hsw (hne F)]
  · have hok := stepCmd_ok (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) (hs := hs) hH hrel hp
    obtain ⟨p', hR, h1, h2, _, hd, hout, hj⟩ := hok.next hn
    have hr : (rankC p).1 ≠ 0 := by
      cases p with
      | command s => exact absurd ⟨s, rfl⟩ hc
      | literalSymbol | insertCopy | copyLength | literals | distance | distanceSymbol | copy | word =>
        simp only [rankC]
        omega
    have hlt : LexLt (rankC p') (rankC p) := hd.resolve_left hr
    refine ⟨p', hR, hout, h2, h1, fun F => (hj F).count_pos fun ⟨e1, _⟩ => ?_⟩
    rw [e1] at hlt
    simp only [LexLt] at hlt
    omega

theorem buf_size_of {b b' : ByteArray} {n : List Nat} (h : b'.data.toList.map UInt8.toNat = b.data.toList.map UInt8.toNat ++ n) :
    b'.size = b.size + n.length := by
  have := congrArg List.length h
  simp only [List.length_map, List.length_append] at this
  show b'.data.size = b.data.size + n.length
  rw [← Array.length_toList, ← Array.length_toList]
  exact this

/-- Handing bytes out adds to the buffer all the bytes waiting, or as many as the space takes. -/
theorem flush_len {D : Dec} {p : SPhase} (h : DRel D p) (buf : ByteArray) (space : Nat) :
    ∃ len, (flushD D buf space).buf.size = buf.size + len ∧ (len = D.cmd.pend.toNat ∨ len = space) ∧ len ≤ D.cmd.pend.toNat ∧
      len ≤ space ∧ (flushD D buf space).space = space - len ∧ (flushD D buf space).D.cmd.pend.toNat = D.cmd.pend.toNat - len := by
  obtain ⟨len, a1, a2, a3, _, a5, a6, a7, _⟩ := flushD_spec h buf space
  have hb := buf_size_of a7
  have hpo := h.pendOut
  have hl : (((p.out.take D.cmd.pend.toNat).reverse).take len).length = len := by
    simp only [List.length_take, List.length_reverse]
    omega
  rw [hl] at hb
  exact ⟨len, hb, by omega, a1, a2, a3, a5⟩

end Brotli.Decoder
