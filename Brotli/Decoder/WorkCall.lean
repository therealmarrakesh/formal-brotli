import Brotli.Decoder.WorkRun

/-!
# The work of a call, against the potential

A call runs the decoder's loop and hands the bytes out, in rounds: a round that hands all its bytes out within its space
goes on with the rest of the space. A round that does after waiting at a meta-block's start is paid for by the round
that start holds; one that does after filling the window hands out a whole window, at least 2¹⁰ bytes, and is paid for
by a unit of each byte it hands out.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- WBITS's step that goes on reads the window's size from the stream's bits. -/
theorem stepDWbits_reads {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf) (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status = .next)
    (F : List Bool) : ∃ rest, readWBITS (availBits D.cmd.word D.cmd.count a pos stop F) =
      some ((stepDWbits a stop hs D pos).k.toNat, rest) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  obtain ⟨h1, -, -, h4, -⟩ := refill_spec hs hp hw
  have hok := wbitsFast_ok h1
  have hrange := wbits_range h1
  have hb : availBits D.cmd.word D.cmd.count a pos stop F = (refill D.cmd.word D.cmd.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill D.cmd.word D.cmd.count a pos stop hs hp).pos.toNat stop.toNat ++ F) := by
    show (BitBuffer.mk D.cmd.word D.cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) = _
    rw [← List.append_assoc, ← List.append_assoc, h4]
  rw [hb]
  unfold stepDWbits at hn ⊢
  rw [dite_eq_left hp'] at hn ⊢
  dsimp only at hn ⊢
  split at hn
  · exact absurd hn (fun e => DStatus.noConfusion e)
  · exact absurd hn (fun e => DStatus.noConfusion e)
  · rename_i heq
    obtain ⟨-, ha2⟩ := hrange heq
    obtain ⟨-, hr⟩ := hok.ok heq
    split at hn
    · rename_i hl
      rw [ite_eq_left hl]
      show ∃ rest, _ = some ((wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toUSize.toNat, rest)
      have ha2' : (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
          (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat ≤ 24 := ha2
      rw [word_toUSize (by omega)]
      exact ⟨_, hr _⟩
    · exact absurd hn (fun e => DStatus.noConfusion e)

theorem endCheck_k (D : Dec) (stop : USize) (final : Bool) (buf : ByteArray) :
    (endCheck D stop final buf).status = .needsInput → (endCheck D stop final buf).D.k = D.k := by
  unfold endCheck
  dsimp only
  repeat' (first | split_all | (intro _; rfl) | (intro _; trivial) | (intro h; exact absurd h (fun e => Status.noConfusion e)))

/-- WBITS's step that doesn't go on stays at WBITS. -/
theorem stepDWbits_stay {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hw : D.tag = .wbits) :
    (stepDWbits a stop hs D pos).status ≠ .next → (stepDWbits a stop hs D pos).tag = .wbits := by
  unfold stepDWbits
  repeat' (first | split_all | (intro _; exact hw) | (intro h; exact absurd rfl h))

/-- A loop that has left WBITS has a window of at least 2¹⁰ bytes. -/
theorem runD_k10' {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} (x : RunArg a stop hs) {p : SPhase} (hrel : DRel x.D p)
    (hk : x.D.tag ≠ .wbits → 10 ≤ x.D.k.toNat) (ht : (runD a stop hs x.D x.inv).tag ≠ .wbits) :
    10 ≤ (runD a stop hs x.D x.inv).k.toNat := by
  obtain ⟨D, hinv⟩ := x
  dsimp only at hrel hk ht ⊢
  by_cases hw : D.tag = .wbits
  · have he : D.tag ≠ .ended := by rw [hw]; exact fun e => DTag.noConfusion e
    have e : stepD a stop hs D = stepDWbits a stop hs D D.pos := by unfold stepD; rw [hw]
    rw [runD, dite_eq_right he] at ht ⊢
    dsimp only at ht ⊢
    by_cases h1 : (stepD a stop hs D).status = .next
    · rw [dite_eq_left h1] at ht ⊢
      have hw' : DRel D .wbits := by cases p <;> first | exact hrel | exact absurd hw (by rw [hrel.1]; exact fun e => DTag.noConfusion e)
      have ht1 : (stepD a stop hs D).tag ≠ .wbits := by rw [e]; exact stepDWbits_tag (by rw [← e]; exact h1)
      have hk1 : 10 ≤ (stepD a stop hs D).k.toNat := by
        rw [e]
        exact stepDWbits_k hw'.2.1 hinv.2 (by rw [← e]; exact h1)
      rw [(runD_wk ⟨_, hinv.step he h1⟩ ht1).2]
      exact hk1
    · rw [dite_eq_right h1] at ht
      rw [e] at ht h1
      exact absurd (stepDWbits_stay hw h1) ht
  · rw [(runD_wk ⟨D, hinv⟩ hw).2]
    exact hk hw

/-- A call's work against the potential. A call that pauses leaves the potential of where it pauses and its bits to pay
later, at most one more byte waiting than it found, and pays 22343 for each bit it reads, 284 for each byte it hands out,
282 for each byte it leaves waiting, the window, and 280. Any call pays at most 282 for each byte of its space, and 1
more, for what it may decode and not hand out, and 23760. -/
theorem pay_callD {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} :
    ∀ (space : Nat) (D : Dec) (h : DInv stop D) (p : SPhase) (buf : ByteArray), DRel D p → SInv p →
    (D.tag ≠ .wbits → 10 ≤ D.k.toNat) →
    buf.size ≤ (callD a stop hs final D h buf space).buf.size ∧
    ((callD a stop hs final D h buf space).status = .needsInput ∨ (callD a stop hs final D h buf space).status = .needsOutput →
      ∃ q, DRel (callD a stop hs final D h buf space).D q ∧ SInv q ∧
        ((callD a stop hs final D h buf space).D.tag ≠ .wbits → 10 ≤ (callD a stop hs final D h buf space).D.k.toNat) ∧
        (callD a stop hs final D h buf space).pos = (callD a stop hs final D h buf space).D.pos ∧
        D.pos.toNat ≤ (callD a stop hs final D h buf space).pos.toNat ∧ (callD a stop hs final D h buf space).pos.toNat ≤ stop.toNat ∧
        (callD a stop hs final D h buf space).D.cmd.pend.toNat ≤ D.cmd.pend.toNat + 1 ∧
        ∀ t : List UInt8, callDW a stop hs final D h buf space + dpot q (callD a stop hs final D h buf space).D +
          hdrRate * ((callD a stop hs final D h buf space).D.bits a (callD a stop hs final D h buf space).pos stop (bits t)).length +
          282 * D.cmd.pend.toNat ≤
          dpot p D + hdrRate * (D.bits a D.pos stop (bits t)).length +
            284 * ((callD a stop hs final D h buf space).buf.size - buf.size) +
            282 * (callD a stop hs final D h buf space).D.cmd.pend.toNat +
            winD D (runD a stop hs (withCap D space) (h.withCap space)) + 280) ∧
    (∀ t : List UInt8, callDW a stop hs final D h buf space ≤ dpot p D + hdrRate * (D.bits a D.pos stop (bits t)).length +
      284 * ((callD a stop hs final D h buf space).buf.size - buf.size) + 282 * (space + 1) +
      winD D (runD a stop hs (withCap D space) (h.withCap space)) + 23760) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h p buf hrel hsi hk
    have hrel' : DRel (withCap D space) p := hrel.withCap _
    obtain ⟨P1, P2⟩ := pay_runD ⟨withCap D space, h.withCap space⟩ p hrel' hsi
    dsimp only at P1 P2
    have hpl := runD_pendLe a stop hs ⟨withCap D space, h.withCap space⟩
    dsimp only at hpl
    have hcap := capE_capFor space
    have hRate : hdrRate = 22343 := rfl
    have hpend : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat ≤
        max D.cmd.pend.toNat (min space 16777216 + 1) := by
      have h2 := hpl.2
      rw [show capE (withCap D space).cmd.cap = min space 16777216 + 1 from hcap] at h2
      exact h2
    have hcapr : (runD a stop hs (withCap D space) (h.withCap space)).cmd.cap = capFor space := hpl.1
    rw [callDW, callD]
    dsimp only
    by_cases hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO, dite_eq_left hO]
      obtain ⟨q, hR, ⟨l, hl1, hl2⟩, hp1, hp2, hsiq, hineq⟩ := P1 (Or.inr (Or.inr hO))
      obtain ⟨len, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := flushD_spec hR buf space
      obtain ⟨len', b1, b2, b3, b4, b5, b6⟩ := flush_len hR buf space
      have hll : len' = len := by omega
      subst hll
      have hfw := flushW_le hR buf space
      have hk10 := runD_k10 ⟨withCap D space, h.withCap space⟩ hrel' hk hO
      dsimp only at hk10
      have hlo : q.out.length - p.out.length = l.length := by rw [hl1, List.length_append]; omega
      have hl2' : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat = D.cmd.pend.toNat + l.length := hl2
      by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz, ite_eq_left hz]
        have hz0 : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat = 0 := by
          rw [hz]; rfl
        by_cases hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space
        · rw [dite_eq_left hlt, dite_eq_left hlt]
          have hlen1 : 1 ≤ len' := by omega
          have hlenp : len' = (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat := by omega
          have htw : (runD a stop hs (withCap D space) (h.withCap space)).tag ≠ .wbits := by
            intro e
            cases q with
            | wbits =>
              have h0 : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend = 0 := hR.2.2.2
              rw [h0] at hlenp
              exact absurd hlenp (by rw [show (0 : USize).toNat = 0 from rfl]; omega)
            | _ => exact absurd (hR.1.symm.trans e) (fun e => DTag.noConfusion e)
          -- The round's own work beyond its bytes: paid by the meta-block's round or by a unit of each byte.
          have hov : stopCost (runD a stop hs (withCap D space) (h.withCap space)) + 7 +
              dpot q (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D ≤
              len' + dpot q (runD a stop hs (withCap D space) (h.withCap space)) := by
            by_cases hm : (runD a stop hs (withCap D space) (h.withCap space)).tag = .mblock
            · cases q with
              | mblock w st =>
                have hne : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend ≠ 0 := fun e => by
                  rw [e, show (0 : USize).toNat = 0 from rfl] at hlenp
                  omega
                have e1 : dpot (.mblock w st) (runD a stop hs (withCap D space) (h.withCap space)) = 8 := by
                  unfold dpot spot roundCost
                  dsimp only
                  rw [ite_eq_right hne]
                have e2 : dpot (.mblock w st) (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D = 0 := by
                  unfold dpot spot
                  dsimp only
                  rw [ite_eq_left hz]
                have e3 : stopCost (runD a stop hs (withCap D space) (h.withCap space)) = 2 := by
                  unfold stopCost
                  rw [ite_eq_left hO, ite_eq_left hm]
                omega
              | _ => exact absurd (hR.1.symm.trans hm) (fun e => DTag.noConfusion e)
            · have e3 : stopCost (runD a stop hs (withCap D space) (h.withCap space)) = 118 := stopCost_out hO hm
              have hroom := runD_room ⟨withCap D space, h.withCap space⟩ hO hm
              dsimp only at hroom
              have hk24 : (runD a stop hs (withCap D space) (h.withCap space)).k.toNat ≤ 24 := by
                rcases hR.window with h0 | ⟨-, -, -, hk⟩
                · rw [h0, show (0 : USize).toNat = 0 from rfl] at hlenp
                  omega
                · exact hk
              have hw := room_full hk24 hcapr hroom (by omega)
              have h10 : 2 ^ 10 ≤ 2 ^ (runD a stop hs (withCap D space) (h.withCap space)).k.toNat :=
                Nat.pow_le_pow_right (by decide) hk10
              have hdm := dpot_mono q (D := runD a stop hs (withCap D space) (h.withCap space))
                (D' := (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D) (by omega)
              omega
          have hw0 : winD (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
              (runD a stop hs (withCap (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
                (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space)
                ((flushD_inv (runD_full hO) buf space).withCap _)) = 0 := by
            unfold winD
            show (if (runD a stop hs (withCap D space) (h.withCap space)).tag = DTag.wbits then _ else 0) = 0
            rw [ite_eq_right htw]
          obtain ⟨I0, I1, I2⟩ := ih _ hlt (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
            (flushD_inv (runD_full hO) buf space) q (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf
            a4 (hsiq hsi) (fun _ => hk10)
          rw [hw0] at I1 I2
          rw [a8] at I1 I2
          refine ⟨by omega, fun hs' => ?_, fun t => ?_⟩
          · obtain ⟨q', c1, c2, c3, c4, cp1, cp2, c5, c6⟩ := I1 hs'
            refine ⟨q', c1, c2, c3, c4, Nat.le_trans hp1 cp1, cp2, by omega, fun t => ?_⟩
            have i1 := c6 t
            have i2 := hineq t
            rw [a10] at i1
            have ed : dpot p (withCap D space) = dpot p D := rfl
            have eb : (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) := rfl
            have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
                winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
            rw [ed, eb, ew, hlo] at i2
            rw [hz0] at i1
            omega
          · have i1 := I2 t
            have i2 := hineq t
            rw [a10] at i1
            have ed : dpot p (withCap D space) = dpot p D := rfl
            have eb : (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) := rfl
            have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
                winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
            rw [ed, eb, ew, hlo] at i2
            omega
        · rw [dite_eq_right hlt, dite_eq_right hlt]
          refine ⟨?_, fun hs' => ?_, fun t => ?_⟩
          · dsimp only
            omega
          · rcases hs' with e | e <;> cases e
          have i2 := hineq t
          have ed : dpot p (withCap D space) = dpot p D := rfl
          have eb : (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) := rfl
          have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
              winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
          rw [ed, eb, ew, hlo] at i2
          have := stopCost_ge (runD a stop hs (withCap D space) (h.withCap space))
          have e3 : stopCost (runD a stop hs (withCap D space) (h.withCap space)) ≤ 118 := by
            unfold stopCost
            rw [ite_eq_left hO]
            split <;> omega
          dsimp only
          omega
      · rw [ite_eq_right hz, ite_eq_right hz]
        have hne : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat ≠ 0 :=
          fun e => hz (USize.toNat_inj.mp (by rw [e]; rfl))
        have hsp : space - len' = 0 := a6 (by omega)
        have e3 : stopCost (runD a stop hs (withCap D space) (h.withCap space)) ≤ 118 := by
          unfold stopCost
          rw [ite_eq_left hO]
          split <;> omega
        refine ⟨by dsimp only; omega, fun _ => ⟨q, a4, hsiq hsi, fun _ => hk10, rfl, by dsimp only; rw [a8]; exact hp1,
          by dsimp only; rw [a8]; exact hp2, by dsimp only; omega, fun t => ?_⟩, fun t => ?_⟩
        · have i2 := hineq t
          have ed : dpot p (withCap D space) = dpot p D := rfl
          have eb : (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) := rfl
          have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
              winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
          rw [ed, eb, ew, hlo] at i2
          have hdm := dpot_mono q (D := runD a stop hs (withCap D space) (h.withCap space))
            (D' := (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D) (by omega)
          dsimp only
          rw [a10, a8]
          omega
        · have i2 := hineq t
          have ed : dpot p (withCap D space) = dpot p D := rfl
          have eb : (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) := rfl
          have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
              winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
          rw [ed, eb, ew, hlo] at i2
          dsimp only
          omega
    · rw [dite_eq_right hO, dite_eq_right hO]
      have ed : dpot p (withCap D space) = dpot p D := rfl
      have eb : ∀ t : List UInt8, (withCap D space).bits a (withCap D space).pos stop (bits t) = D.bits a D.pos stop (bits t) :=
        fun _ => rfl
      have ew : winD (withCap D space) (runD a stop hs (withCap D space) (h.withCap space)) =
          winD D (runD a stop hs (withCap D space) (h.withCap space)) := rfl
      unfold afterRun afterRunW
      cases hst : (runD a stop hs (withCap D space) (h.withCap space)).status with
      | needsOutput => exact absurd hst hO
      | bad =>
        obtain ⟨L, hL, hb⟩ := P2 (Or.inl hst)
        refine ⟨Nat.le_refl _, fun hs' => ?_, fun t => ?_⟩
        · rcases hs' with e | e <;> cases e
        · have i := hb t
          rw [ed, eb, ew] at i
          have : capE (withCap D space).cmd.cap = min space 16777216 + 1 := hcap
          rw [this] at hL
          dsimp only
          omega
      | memory =>
        obtain ⟨L, hL, hb⟩ := P2 (Or.inr hst)
        refine ⟨Nat.le_refl _, fun hs' => ?_, fun t => ?_⟩
        · rcases hs' with e | e <;> cases e
        · have i := hb t
          rw [ed, eb, ew] at i
          have : capE (withCap D space).cmd.cap = min space 16777216 + 1 := hcap
          rw [this] at hL
          dsimp only
          omega
      | needsInput =>
        obtain ⟨q, hR, ⟨l, hl1, hl2⟩, hp1, hp2, hsiq, hineq⟩ := P1 (Or.inr (Or.inl hst))
        obtain ⟨len, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := flushD_spec hR buf space
        obtain ⟨len', b1, b2, b3, b4, b5, b6⟩ := flush_len hR buf space
        have hll : len' = len := by omega
        subst hll
        have hfw := flushW_le hR buf space
        have hlo : q.out.length - p.out.length = l.length := by rw [hl1, List.length_append]; omega
        have hl2' : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat = D.cmd.pend.toNat + l.length := hl2
        have hsc : stopCost (runD a stop hs (withCap D space) (h.withCap space)) = 269 := stopCost_in hst
        have htw : (runD a stop hs (withCap D space) (h.withCap space)).tag ≠ .wbits →
            10 ≤ (runD a stop hs (withCap D space) (h.withCap space)).k.toNat :=
          runD_k10' ⟨withCap D space, h.withCap space⟩ hrel' hk
        dsimp only
        by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
        · rw [ite_eq_left hz]
          have hz0 : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat = 0 := by
            rw [hz]; rfl
          cases final with
          | false =>
            rw [ite_eq_right Bool.false_ne_true]
            refine ⟨by dsimp only; omega, fun _ => ⟨q, a4, hsiq hsi, htw, rfl, by dsimp only; rw [a8]; exact hp1,
              by dsimp only; rw [a8]; exact hp2, by dsimp only; omega, fun t => ?_⟩, fun t => ?_⟩
            · have i2 := hineq t
              rw [ed, eb, ew, hlo, hsc] at i2
              have hdm := dpot_mono q (D := runD a stop hs (withCap D space) (h.withCap space))
                (D' := (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D) (by omega)
              dsimp only
              rw [a10, a8]
              omega
            · have i2 := hineq t
              rw [ed, eb, ew, hlo, hsc] at i2
              dsimp only
              omega
          | true =>
            rw [ite_eq_left rfl]
            refine ⟨by dsimp only; omega, fun hs' => ?_, fun t => ?_⟩
            · rcases hs' with e | e <;> cases e
            · have i2 := hineq t
              rw [ed, eb, ew, hlo, hsc] at i2
              dsimp only
              omega
        · rw [ite_eq_right hz]
          have hne : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat ≠ 0 :=
            fun e => hz (USize.toNat_inj.mp (by rw [e]; rfl))
          have hsp : space - len' = 0 := a6 (by omega)
          refine ⟨by dsimp only; omega, fun _ => ⟨q, a4, hsiq hsi, htw, rfl, by dsimp only; rw [a8]; exact hp1,
            by dsimp only; rw [a8]; exact hp2, by dsimp only; omega, fun t => ?_⟩, fun t => ?_⟩
          · have i2 := hineq t
            rw [ed, eb, ew, hlo, hsc] at i2
            have hdm := dpot_mono q (D := runD a stop hs (withCap D space) (h.withCap space))
              (D' := (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D) (by omega)
            dsimp only
            rw [a10, a8]
            omega
          · have i2 := hineq t
            rw [ed, eb, ew, hlo, hsc] at i2
            dsimp only
            omega
      | next =>
        obtain ⟨q, hR, ⟨l, hl1, hl2⟩, hp1, hp2, hsiq, hineq⟩ := P1 (Or.inl hst)
        obtain ⟨len, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := flushD_spec hR buf space
        obtain ⟨len', b1, b2, b3, b4, b5, b6⟩ := flush_len hR buf space
        have hll : len' = len := by omega
        subst hll
        have hfw := flushW_le hR buf space
        have hlo : q.out.length - p.out.length = l.length := by rw [hl1, List.length_append]; omega
        have hl2' : (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat = D.cmd.pend.toNat + l.length := hl2
        have hsc : stopCost (runD a stop hs (withCap D space) (h.withCap space)) = 269 := by
          unfold stopCost
          rw [ite_eq_right (by rw [hst]; exact fun e => DStatus.noConfusion e)]
        have hend := runD_next ⟨withCap D space, h.withCap space⟩ hst
        dsimp only at hend
        have htw : 10 ≤ (runD a stop hs (withCap D space) (h.withCap space)).k.toNat :=
          runD_k10' ⟨withCap D space, h.withCap space⟩ hrel' hk (by rw [hend]; exact fun e => DTag.noConfusion e)
        dsimp only
        by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
        · rw [ite_eq_left hz]
          have hz0 : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat = 0 := by
            rw [hz]; rfl
          cases q with
          | ended st =>
            obtain ⟨e1, e2, e3, -, e5, -, -, e8, -⟩ := endCheck_ok hs a4 (by rw [a8]; exact hp2) final
              (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf
            refine ⟨by rw [e3]; omega, fun hs' => ?_, fun t => ?_⟩
            · have hin : (endCheck (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D stop final
                  (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf).status = .needsInput := by
                rcases hs' with e | e
                · exact e
                · exact absurd e e8
              obtain ⟨-, -, f3, f4, f5, -, ⟨n, f7⟩, -, -⟩ := e5 hin
              have g2 := congrArg USize.toNat f5
              rw [a8] at e1
              refine ⟨.ended st, f4, trivial, fun _ => ?_, f3.symm, Nat.le_trans hp1 e1, e2, by omega, fun t => ?_⟩
              · rw [endCheck_k _ _ _ _ hin]
                exact htw
              · have i2 := hineq t
                rw [ed, eb, ew, hlo, hsc] at i2
                have i3 := f7 t
                rw [a10, a8] at i3
                have g1 := congrArg ByteArray.size e3
                have e0 : dpot (.ended st) (endCheck (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D stop
                    final (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf).D = 0 := rfl
                rw [e0]
                rw [hRate] at i2 ⊢
                omega
            · have i2 := hineq t
              rw [ed, eb, ew, hlo, hsc] at i2
              rw [e3]
              omega
          | _ => exact absurd (hR.1.symm.trans hend) (fun e => DTag.noConfusion e)
        · rw [ite_eq_right hz]
          have hne : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat ≠ 0 :=
            fun e => hz (USize.toNat_inj.mp (by rw [e]; rfl))
          have hsp : space - len' = 0 := a6 (by omega)
          refine ⟨by dsimp only; omega, fun _ => ⟨q, a4, hsiq hsi, fun _ => htw, rfl, by dsimp only; rw [a8]; exact hp1,
            by dsimp only; rw [a8]; exact hp2, by dsimp only; omega, fun t => ?_⟩, fun t => ?_⟩
          · have i2 := hineq t
            rw [ed, eb, ew, hlo, hsc] at i2
            have hdm := dpot_mono q (D := runD a stop hs (withCap D space) (h.withCap space))
              (D' := (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D) (by omega)
            dsimp only
            rw [a10, a8]
            omega
          · have i2 := hineq t
            rw [ed, eb, ew, hlo, hsc] at i2
            dsimp only
            omega

end Brotli.Decoder
