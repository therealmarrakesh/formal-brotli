module

public import Brotli.Decoder.FastPay

@[expose] public section

/-!
# The work of the command loop with the fast loop is paid for

`runCmdKFW` against `runCmdKF`, by induction on the fuel, the two taken apart together: an entry into the fast loop is a
move whose work, with its round, is four for each byte it writes and three (`fastEnter_work`), paid for by the bytes and,
when it writes nothing, by what the place holds for it (`alw`, which the step before it left, `round_pay`, or the caller
gave); a step is paid for as the step machine's are (`round_pay`). The account is `CW`: the step machine's with what a
fresh state holds.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- An entry into the fast loop costs at most four for each byte it writes, and two. -/
theorem fastEnter_work {w : Nat} {mH : MetaBlockHeader}
    {H : Hdr} {kk : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {cap n : USize}
    {word count : UInt64} {ring : ByteArray} {wpos pend written : USize} {p1 p2 : UInt8}
    {remaining iCount lCount dCount : UInt64} {flags : Flags} {x : CmdExt} {tag : Tag} {left lits bEnd : UInt64}
    {pos : USize}
    (hinv : KInv H kk stop word count ring wpos written x.iCur x.iPrev x.lCur x.lPrev x.dCur x.dPrev x.copyBits x.dist
      x.wordBuf x.wordPos tag pos) (hm : pos.toNat + 40 ≤ stop.toNat) {p : Phase}
    (hrel : Rel w kk.toNat mH ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount,
      flags, x, tag, left, pos, .next⟩ p)
    (htag : tag = .literals ∨ tag = .distance)
    (hbE : bEnd = wpos.toUInt64 + umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64))
    (hl : lits ≤ umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64))
    (hcl : x.clen ≤ umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64) - lits) :
    pend.toNat ≤ (fastEnter H kk a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount
        flags x tag lits bEnd pos hinv hm).val.pend.toNat ∧
      fastEnterW H kk a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags x tag
        lits bEnd pos hinv hm ≤
      4 * ((fastEnter H kk a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount flags x
        tag lits bEnd pos hinv hm).val.pend.toNat - pend.toNat) + 2 := by
  generalize hA : umin remaining (if room kk cap ≤ pend then 0 else (room kk cap - pend).toUInt64) = A at hbE hl hcl
  have hk := hinv.k24
  have h16 := hinv.k16
  have hwp := hinv.wpos
  have hwr := hinv.written
  have hR : 2 ^ kk.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have hCx : ∃ out rem ds ic lit dist, Core w kk.toNat mH ⟨word, count, ring, wpos, pend, cap, written, p1, p2,
      remaining, iCount, lCount, dCount, flags, x, tag, left, pos, .next⟩ out rem ds ic lit dist := by
    rcases htag with ht | ht
    · obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hrel.literals_of ht
      exact ⟨_, _, _, _, _, _, hrel.1⟩
    · obtain ⟨_, _, _, rfl⟩ := hrel.distance_of ht
      exact ⟨_, _, _, _, _, _, hrel.1⟩
  obtain ⟨_, _, _, _, _, _, hC⟩ := hCx
  have hpL : pend.toNat + 16 ≤ 2 ^ kk.toNat := hC.pendLe
  have hc1 : 1 ≤ x.clen.toNat := hC.clen1
  have hAN : A.toNat ≤ remaining.toNat ∧ pend.toNat + A.toNat + 16 ≤ 2 ^ kk.toNat := by
    rw [← hA, umin_toNat]
    have hrl := room_le16 (cap := cap) hk h16
    split
    · rw [h0]
      omega
    · rename_i h
      have h' : pend.toNat < (room kk cap).toNat := Nat.lt_of_not_le fun e => h (USize.le_iff_toNat_le.mpr e)
      rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
      omega
  have hlN : lits.toNat ≤ A.toNat := UInt64.le_iff_toNat_le.mp hl
  have hcN : x.clen.toNat ≤ A.toNat - lits.toNat := by
    have := UInt64.le_iff_toNat_le.mp hcl
    rwa [u64_sub_le hlN] at this
  have hbN : bEnd.toNat = wpos.toNat + A.toNat := by
    rw [hbE, u64_add_small (by rw [USize.toNat_toUInt64]; omega), USize.toNat_toUInt64]
  have hl0 : (lits + 0).toNat = lits.toNat := by rw [UInt64.add_zero]
  have N0 : FNum wpos (pend - wpos) (written - wpos) (remaining + wpos.toUInt64) bEnd kk.toNat
      ((lits + 0).toNat + x.clen.toNat) := by
    have e2 : (wpos + (pend - wpos)).toNat = pend.toNat := by rw [USize.add_comm, USize.sub_add_cancel]
    have e3 : (wpos + (written - wpos)).toNat = written.toNat := by rw [USize.add_comm, USize.sub_add_cancel]
    have e4 : (remaining + wpos.toUInt64 - wpos.toUInt64).toNat = remaining.toNat := by rw [UInt64.add_sub_cancel]
    exact ⟨by rw [hl0]; omega, by rw [e4]; omega, by omega, by rw [e2]; omega, by rw [e3]; omega⟩
  unfold fastEnter fastEnterW
  dsimp only
  obtain ⟨o, g3, g1, g2, gw⟩ := fastLoop_work _ n rfl word count pos ring wpos iCount lCount dCount _ _ _ _ _ lits 0 p1 p2
    _ N0 (by have := lCount.toNat_lt; omega) (by omega) hc1
  rw [ite_eq_left rfl] at gw
  rw [g3]
  have e : o + (pend - wpos) = (o - wpos) + pend := by
    conv => rhs; rw [← USize.sub_add_cancel pend wpos]
    rw [← USize.add_assoc, USize.add_comm (o - wpos) (pend - wpos), USize.add_assoc, USize.sub_add_cancel,
      USize.add_comm]
  have hd : (o - wpos).toNat = o.toNat - wpos.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr g1)
  rw [e, fastAdd (by omega), hd]
  omega

/-- A command loop step that goes on, against the potential, holding what its place holds for an entry into the fast
loop. -/
theorem stepCmd_potA {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} (hm : m.ndirect ≤ 120) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st p) (hci : CInv w p) (hp : pos.toNat ≤ stop.toNat) (hn : (stepCmd H k a stop hs st pos).status = .next) :
    ∃ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' ∧ OutStep p p' st (stepCmd H k a stop hs st pos) ∧ CInv w p' ∧
      (stepCmd H k a stop hs st pos).pos.toNat ≤ stop.toNat ∧ pos.toNat ≤ (stepCmd H k a stop hs st pos).pos.toNat ∧
      ∀ F, ∃ n, 1 ≤ n ∧ ReachN (cStep w m) n p (stateBits st a pos stop F) p'
        (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F) ∧
        stepCmdW H k a stop hs st pos + 1 + cpot p' + alw p' +
          200 * (stateBits (stepCmd H k a stop hs st pos) a (stepCmd H k a stop hs st pos).pos stop F).length +
          (stop.toNat - (stepCmd H k a stop hs st pos).pos.toNat) ≤
          cpot p + 200 * (stateBits st a pos stop F).length + (stop.toNat - pos.toNat) + 31 * (p'.out.length - p.out.length) := by
  obtain ⟨p', hR, hout, h2, h1, hj⟩ := stepCmd_count (hs := hs) hH hrel hp hn
  obtain ⟨l, hl1, hl2⟩ := hout
  refine ⟨p', hR, ⟨l, hl1, hl2⟩, ?_, h2, h1, fun F => ?_⟩
  · obtain ⟨n, hn1, hr⟩ := hj []
    exact (creach hm hr hci).1
  obtain ⟨n, hn1, hr⟩ := hj F
  refine ⟨n, hn1, hr, ?_⟩
  have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
  have hb : (stepCmd H k a stop hs st pos).status ≠ .bad := by rw [hn]; exact fun e => StepStatus.noConfusion e
  have := round_pay hm hrel.k24 hp hrel hR hb h1 h2 hl2 hci hr hlo (fun _ => hn1)
  simp only [hn, ↓reduceIte] at this
  have hx : p'.out.length - p.out.length = l.length := by omega
  rw [hx]
  omega

/-- What a copy or a word holds is at most 81. -/
theorem cred_le (p : Phase) : cred p ≤ 81 := by
  cases p with
  | copy s d n =>
    cases n with
    | zero => simp [cred]
    | succ n => simp [cred]; omega
  | word s pending =>
    cases pending with
    | nil => simp [cred]
    | cons x r => simp [cred]; omega
  | _ => simp [cred]

/-- From a command's literals or its distance, a place no higher in rank has no more potential. -/
theorem cpot_mono_LD {p q : Phase} (hp : isLD p = true) (h : crank q ≤ crank p) : cpot q ≤ cpot p := by
  obtain ⟨h1, h2⟩ := isLD_crank hp
  have hc := cred_le q
  by_cases hq1 : crank q = 1
  · unfold cpot
    rw [h2]
    rcases h1 with h1 | h1 <;> rw [h1, hq1] <;> simp only [Nat.reduceLeDiff, ↓reduceIte] <;> omega
  · have hc0 : cred q = 0 := Classical.byContradiction fun h => hq1 (cred_crank h)
    unfold cpot
    rw [h2, hc0]
    rcases h1 with h1 | h1 <;> rw [h1] <;> repeat' split
    all_goals omega

/-- A command's literals or its distance has potential 88 at least. -/
theorem cpot_LD {p : Phase} (hp : isLD p = true) : 88 ≤ cpot p := by
  obtain ⟨h1, h2⟩ := isLD_crank hp
  unfold cpot
  rw [h2]
  rcases h1 with h1 | h1 <;> rw [h1] <;> decide

/-- What the work of the command loop with the fast loop is paid by, from a place, a record and a position, with `A`
held for an entry into the fast loop, to its result `R`, with the fuel it had and whether it started fresh. -/
def CW (w : Nat) (k : USize) (m : MetaBlockHeader) (a : ByteArray) (stop : USize) (p : Phase) (st : Cmd) (pos : USize)
    (A W : Nat) (R : Cmd) (N : Nat) (fresh : Bool) : Prop :=
  ∀ F, ∃ c q st' pos', Rel w k.toNat m st' q ∧ CInv w q ∧ OutStep p q st st' ∧ pos.toNat ≤ pos'.toNat ∧
    pos'.toNat ≤ stop.toNat ∧ ReachN (cStep w m) c p (stateBits st a pos stop F) q (stateBits st' a pos' stop F) ∧
    W + cpot q + 200 * (stateBits st' a pos' stop F).length + (stop.toNat - pos'.toNat) ≤
      cpot p + A + 200 * (stateBits st a pos stop F).length + (stop.toNat - pos.toNat) +
        31 * (q.out.length - p.out.length) + cmdEnd R ∧
    (R.status ≠ .bad → st' = R ∧ pos' = R.pos) ∧
    (R.status = .bad → R.WinSame st' ∧ pos'.toNat ≤ R.pos.toNat) ∧
    (R.status = .done → ∃ s, q = .command s ∧ s.remaining = 0) ∧
    (R.status = .next → N ≤ 2 * c + (if fresh then 1 else 0))

section
variable {w : Nat} {k : USize} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}

/-- The fuel's end. -/
theorem CW.zero {p : Phase} {st : Cmd} {A : Nat} {fresh : Bool} (hrel : Rel w k.toNat m st p) (hci : CInv w p)
    (hs : st.status = .next) (hp : st.pos.toNat ≤ stop.toNat) : CW w k m a stop p st st.pos A 1 st 0 fresh := by
  intro F
  have he : cmdEnd st = 1 := by unfold cmdEnd; rw [hs]; rfl
  refine ⟨0, p, st, st.pos, hrel, hci, ⟨[], rfl, rfl⟩, Nat.le_refl _, hp, .refl _ _, by rw [he]; omega,
    fun _ => ⟨rfl, rfl⟩, fun e => absurd (hs.symm.trans e) (by decide), fun e => absurd (hs.symm.trans e) (by decide),
    fun _ => Nat.zero_le _⟩

/-- A step that goes on, then the loop. -/
theorem CW.next {H : Hdr} {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} {A W : Nat} {R : Cmd}
    {N : Nat} {fresh : Bool} (hm : m.ndirect ≤ 120) (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hci : CInv w p)
    (hp : pos.toNat ≤ stop.toNat) (hst : (stepCmd H k a stop hs st pos).status = .next)
    (ih : ∀ p', Rel w k.toNat m (stepCmd H k a stop hs st pos) p' → CInv w p' →
      CW w k m a stop p' (stepCmd H k a stop hs st pos) (stepCmd H k a stop hs st pos).pos (alw p') W R N true) :
    CW w k m a stop p st pos A (stepCmdW H k a stop hs st pos + 1 + W) R (N + 1) fresh := by
  obtain ⟨p1, hR1, o1, hci1, h2, h1, hj1⟩ := stepCmd_potA (hs := hs) hm hH hrel hci hp hst
  intro F
  obtain ⟨n1, hn1, hr1, hw1⟩ := hj1 F
  obtain ⟨c2, q, st', pos', hq, hciq, o2, g1, g2, hr2, g3, g4, gb, g5, g6⟩ := ih p1 hR1 hci1 F
  have ho1 : p.out.length ≤ p1.out.length := by
    obtain ⟨l, e1, -⟩ := o1
    rw [e1, List.length_append]
    omega
  have ho2 : p1.out.length ≤ q.out.length := by
    obtain ⟨l, e1, -⟩ := o2
    rw [e1, List.length_append]
    omega
  refine ⟨n1 + c2, q, st', pos', hq, hciq, o1.trans o2, by omega, g2, hr1.trans hr2, by omega, g4, gb, g5,
    fun h => by have := g6 h; simp only [↓reduceIte] at this; split <;> omega⟩

/-- A step that stops the loop. -/
theorem CW.halt {H : Hdr} {hs : stop.toNat ≤ a.size} {p : Phase} {st : Cmd} {pos : USize} {A N : Nat} {fresh : Bool}
    (hm : m.ndirect ≤ 120) (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hci : CInv w p)
    (hp : pos.toNat ≤ stop.toNat) (hst : (stepCmd H k a stop hs st pos).status ≠ .next) :
    CW w k m a stop p st pos A (stepCmdW H k a stop hs st pos + 1 + 0) (stepCmd H k a stop hs st pos) (N + 1) fresh := by
  have hk := hrel.k24
  have hok := stepCmd_ok (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) (hs := hs) hH hrel hp
  intro F
  cases hs' : (stepCmd H k a stop hs st pos).status
  case next => exact absurd hs' hst
  case needsInput =>
    obtain ⟨b1, _, p', hR', _, _, _, hout, hj, _⟩ := hok.needsInput hs'
    obtain ⟨c0, hc0⟩ := (hj F).count
    obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
    have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
      (by rw [hs']; decide) (by rw [hs']; decide) (by rw [b1]; exact hp) (by rw [b1]; exact Nat.le_refl _) hl2 hci hc0 hlo
    have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hs']; rfl
    refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, hc0, ?_,
      fun _ => ⟨rfl, rfl⟩, (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide))⟩
    omega
  case needsOutput =>
    obtain ⟨p', hR', b1, b2, _, _, _, hout, hj⟩ := hok.needsOutput hs'
    obtain ⟨c0, hc0⟩ := (hj F).count
    obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
    have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
      (by rw [hs']; decide) (by rw [hs']; decide) b1 b2 hl2 hci hc0 hlo
    have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hs']; rfl
    refine ⟨c0, p', _, _, hR', hci', ⟨l, hl1, hl2⟩, b1, b2, hc0, ?_, fun _ => ⟨rfl, rfl⟩,
      (fun h => absurd h (by decide)), (fun h => absurd h (by decide)),
      (fun h => absurd h (by decide))⟩
    omega
  case done =>
    obtain ⟨s, hR', b1, b2, _, h0, hout, hj⟩ := hok.done hs'
    obtain ⟨c0, hc0⟩ := (hj F).count
    obtain ⟨hci', c1, -, -, -⟩ := creach hm hc0 hci
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : (Phase.command s).out.length = l.length + p.out.length := by rw [hl1, List.length_append]
    have hw := stopRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hm hp hrel hR'
      (by rw [hs']; decide) (by rw [hs']; decide) b1 b2 hl2 hci hc0 hlo
    have he : cmdEnd (stepCmd H k a stop hs st pos) = 84 := by unfold cmdEnd; rw [hs']; rfl
    exact ⟨c0, .command s, _, _, hR', hci', ⟨l, hl1, hl2⟩, b1, b2, hc0, by omega,
      fun _ => ⟨rfl, rfl⟩, (fun h => absurd h (by decide)), fun _ => ⟨s, rfl, h0⟩,
      (fun h => absurd h (by decide))⟩
  case bad =>
    have hw := badRound_pay (H := H) (k := k) (a := a) (hs := hs) (st := st) (pos := pos) hk hp hrel.wf hs'
    have he : cmdEnd (stepCmd H k a stop hs st pos) = 92 := by unfold cmdEnd; rw [hs']; rfl
    exact ⟨0, p, st, pos, hrel, hci, ⟨[], rfl, rfl⟩, Nat.le_refl _, hp, .refl _ _, by omega,
      fun e => absurd rfl e,
      fun _ => ⟨stepCmd_badWin hs', (stepCmd_bad (K := commandsFrom w m) (fun s bs h0 => commandsFrom_step bs h0) hH hrel
        hp hs').1⟩,
      (fun h => absurd h (by decide)), (fun h => absurd h (by decide))⟩

/-- A move of the fast loop from a command's literals or its distance, then the loop. -/
theorem CW.move {α : Type} {K : CommandState → List Bool → Option α} {p p' : Phase} {st r : Cmd} {pos : USize}
    {Wf W : Nat} {R : Cmd} {N : Nat} (hm : m.ndirect ≤ 120) (hci : CInv w p)
    (hld : isLD p = true) (mv : MoveOk w k.toNat m K a stop p st pos p' r)
    (hW : Wf ≤ 4 * (r.pend.toNat - st.pend.toNat) + 3)
    (ih : CInv w p' → CW w k m a stop p' r r.pos 0 W R N false) : CW w k m a stop p st pos (alw p) (Wf + W) R (N + 1) true := by
  intro F
  obtain ⟨c1, hc1⟩ := (mv.reach F).count
  obtain ⟨hci1, b1, o1, cr, -⟩ := creach hm hc1 hci
  obtain ⟨c2, q, st', pos', hq, hciq, o2, g1, g2, hr2, g3, g4, gb, g5, g6⟩ := ih hci1 F
  obtain ⟨l, hl1, hl2⟩ := mv.out
  have hlo : p'.out.length = l.length + p.out.length := by rw [hl1, List.length_append]
  have ho2 : p'.out.length ≤ q.out.length := by
    obtain ⟨l', e1, -⟩ := o2
    rw [e1, List.length_append]
    omega
  have hle := mv.posLe
  have hal : alw p = 3 := by unfold alw; rw [ite_eq_left hld]
  have hcp := cpot_le p'
  have h88 := cpot_LD hld
  have hmono : (stateBits st a pos stop F).length - (stateBits r a r.pos stop F).length = 0 → l.length = 0 →
      cpot p' ≤ cpot p := fun h1 h2 => cpot_mono_LD hld (by omega)
  refine ⟨c1 + c2, q, st', pos', hq, hciq, mv.out.trans o2, by omega, g2, hc1.trans hr2, ?_, g4, gb, g5,
    fun h => by have := g6 h; simp only [Bool.false_eq_true, ↓reduceIte] at this ⊢; omega⟩
  rw [hal]
  by_cases hz : (stateBits st a pos stop F).length - (stateBits r a r.pos stop F).length = 0 ∧ l.length = 0
  · have := hmono hz.1 hz.2
    omega
  · omega

end

open Classical in
/-- The work of the command loop with the fast loop is paid for by the potential, 200 for each bit it reads, 31 for each
byte it adds, a round for each byte its refills take, and its end; a fresh state holds what its place holds for an entry
into the fast loop. -/
theorem runCmdKFW_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} (hm : m.ndirect ≤ 120) (hH : HdrRel H m) :
    ∀ (N : Nat) (n : USize), n.toNat = N → ∀ (fresh : Bool) (cell : RunOut) (word count : UInt64) (ring : ByteArray)
      (wpos pend cap written : USize) (p1 p2 : UInt8) (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize)
      (hinv : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos
        tag pos) (p : Phase),
      Rel w k.toNat m (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
        lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) p →
      CInv w p →
      CW w k m a stop p (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
          lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) pos
        (if fresh then alw p else 0)
        (runCmdKFW H k a stop hs n fresh word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
          hinv)
        (runCmdKF H k a stop hs n fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
          flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left
          pos hinv) N fresh := by
  intro N
  induction N with
  | zero =>
    intro n hn fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv p hrel hci
    rw [runCmdKF, runCmdKFW, dite_eq_left (usize_zero hn), dite_eq_left (usize_zero hn)]
    exact CW.zero hrel hci rfl hinv.pos
  | succ N ih =>
    intro n hn fresh cell word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos hinv p hrel hci
    have hn0 : n ≠ 0 := fun e => by
      rw [e, show (0 : USize).toNat = 0 from rfl] at hn
      omega
    have hnN : (n - USize.ofNat 1).toNat = N := by rw [usize_pred hn0]; omega
    rw [runCmdKF, runCmdKFW, dite_eq_right hn0, dite_eq_right hn0]
    dsimp only
    by_cases hf : fresh = true ∧ (tag = .literals ∨ tag = .distance) ∧ USize.ofNat 40 ≤ stop - pos ∧
        (if tag = .literals then left else 0) ≤
          umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) ∧
        clen ≤ umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64) -
          (if tag = .literals then left else 0)
    · rw [dite_eq_left hf, dite_eq_left hf]
      have hm' : pos.toNat + 40 ≤ stop.toNat := by
        have h1 := USize.le_iff_toNat_le.mp hf.2.2.1
        rw [fastLit (by decide), USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hinv.pos)] at h1
        have := hinv.pos
        omega
      have hld : isLD p = true := by
        rcases hf.2.1 with ht | ht
        · obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hrel.literals_of ht
          rfl
        · obtain ⟨_, _, _, rfl⟩ := hrel.distance_of ht
          rfl
      obtain ⟨p', mv, -, -⟩ := fastEnter_ok (K := commandsFrom w m) (fun _ bs h0 => commandsFrom_step bs h0) (n := n)
        (hs := hs) (cap := cap) (pend := pend) (p1 := p1) (p2 := p2)
        (remaining := remaining) (iCount := iCount) (lCount := lCount) (dCount := dCount) (flags := flags)
        (x := ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩) (left := left) hinv hm' hH hrel hf.2.1 rfl rfl hf.2.2.2.1 hf.2.2.2.2
      obtain ⟨-, hw⟩ := fastEnter_work (n := n) (hs := hs) (cap := cap) (pend := pend) (p1 := p1) (p2 := p2)
        (remaining := remaining) (iCount := iCount) (lCount := lCount) (dCount := dCount) (flags := flags)
        (x := ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩) (left := left) hinv hm' hrel hf.2.1 rfl hf.2.2.2.1 hf.2.2.2.2
      generalize fastEnter H k a stop hs cap n word count ring wpos pend written p1 p2 remaining iCount lCount dCount
        flags ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf,
          wordPos⟩ tag (if tag = .literals then left else 0)
        (wpos.toUInt64 + umin remaining (if room k cap ≤ pend then 0 else (room k cap - pend).toUInt64)) pos hinv hm' = r
        at mv hw
      obtain ⟨⟨word', count', ring', wpos', pend', cap', written', q1, q2, remaining', iCount', lCount', dCount', flags',
        ⟨iCur', iPrev', lCur', lPrev', dCur', dPrev', e0, e1, e2, e3, code', ilen', clen', copyBits', copyBase', dist',
          wordBuf', wordPos'⟩, tag', left', pos', ss'⟩, h'⟩ := r
      have hR := mv.rel.mark pos' .next
      have hfr : fresh = true := hf.1
      subst hfr
      exact CW.move hm hci hld (mv.trans (MoveOk.same (st := mkCmd word' count' ring' wpos' pend' cap' written' q1 q2
          remaining' iCount' lCount' dCount' flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen'
          copyBits' copyBase' dist' wordBuf' wordPos' tag' left' pos' ss') hR rfl rfl rfl rfl mv.posStop))
        (by rw [Nat.add_comm]; exact Nat.succ_le_succ hw)
        (fun hci' => ih _ hnN false cell word' count' ring' wpos' pend' cap' written' q1 q2 remaining' iCount' lCount'
          dCount' flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen' copyBits' copyBase' dist'
          wordBuf' wordPos' tag' left' pos' h' p' hR hci')
    · rw [dite_eq_right hf, dite_eq_right hf]
      have hc : Drops H k stop
          (fun c word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h =>
            runCmdKF H k a stop hs (n - USize.ofNat 1) true c word count ring wpos pend cap written p1 p2 remaining iCount
              lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
              wordBuf wordPos tag left pos h)
          (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
            if h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
                wordPos tag pos then
              runCmdKF H k a stop hs (n - USize.ofNat 1) true cell word count ring wpos pend cap written p1 p2 remaining
                iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase
                dist wordBuf wordPos tag left pos h
            else mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
              lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next) :=
        fun c1 word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h => by
          dsimp only
          rw [dite_eq_left h]
          apply runCmdKF_cell H k a stop hs _ _ rfl
      rw [kstep_eq (sp := pos) (ss := .next) (hcont := hc)]
      by_cases hst : (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          tag left pos .next) pos).status = .next
      · have hstep := stepCmd_ok (hs := hs) (K := commandsFrom w m) (a := a) (fun _ bs h0 => commandsFrom_step bs h0) hH
          hrel hinv.pos
        obtain ⟨_, _, _, h2, -⟩ := hstep.next hst
        refine CW.next hm hH hrel hci hinv.pos hst fun p' hR hci' => ?_
        generalize stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
          flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag
          left pos .next) pos = r at hst h2 hR ⊢
        obtain ⟨word', count', ring', wpos', pend', cap', written', q1, q2, remaining', iCount', lCount', dCount', flags',
          ⟨iCur', iPrev', lCur', lPrev', dCur', dPrev', e0, e1, e2, e3, code', ilen', clen', copyBits', copyBase', dist',
            wordBuf', wordPos'⟩, tag', left', pos', ss'⟩ := r
        have hs' : ss' = .next := hst
        subst hs'
        have hI := KInv.of_rel hH hR h2
        unfold kcase
        dsimp only
        rw [ite_eq_left rfl, ite_eq_left rfl, dite_eq_left hI, dite_eq_left hI]
        exact ih _ hnN true cell word' count' ring' wpos' pend' cap' written' q1 q2 remaining' iCount' lCount' dCount'
          flags' iCur' iPrev' lCur' lPrev' dCur' dPrev' e0 e1 e2 e3 code' ilen' clen' copyBits' copyBase' dist' wordBuf'
          wordPos' tag' left' pos' hI p' hR hci'
      · unfold kcase
        rw [ite_eq_right hst, ite_eq_right hst]
        exact CW.halt hm hH hrel hci hinv.pos hst

/-- What the work is paid by depends on the record it starts from only through its bits and bytes waiting. -/
theorem CW.congr {w : Nat} {k : USize} {m : MetaBlockHeader} {a : ByteArray} {stop : USize} {p : Phase} {st r : Cmd}
    {pos : USize} {A W : Nat} {R : Cmd} {N : Nat} {fresh : Bool} (h : CW w k m a stop p r pos A W R N fresh)
    (hw : r.word = st.word) (hc : r.count = st.count) (hpe : r.pend = st.pend) : CW w k m a stop p st pos A W R N fresh := by
  intro F
  have e : stateBits r a pos stop F = stateBits st a pos stop F := by unfold stateBits; rw [hw, hc]
  obtain ⟨c, q, st', pos', h1, h2, ⟨l, o1, o2⟩, h3, h4, h5, h6, h7⟩ := h F
  rw [e] at h5 h6
  exact ⟨c, q, st', pos', h1, h2, ⟨l, o1, by rw [← hpe]; exact o2⟩, h3, h4, h5, h6, h7⟩

/-- The work of the command loop with the fast loop, from a record, is paid for by the potential, what its place holds
for an entry into the fast loop, 200 for each bit it reads, 31 for each byte it adds, a round for each byte its refills
take, and its end. -/
theorem runCmdFW_count {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} (hm : m.ndirect ≤ 120) (hH : HdrRel H m) (n : USize) {p : Phase} {st : Cmd} {pos : USize}
    (hrel : Rel w k.toNat m st p) (hci : CInv w p) (h : CmdInv H k stop st pos) :
    CW w k m a stop p st pos (alw p) (runCmdFW H k a stop hs n st pos h) (runCmdF H k a stop hs n st pos h) n.toNat true := by
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, sp, ss⟩ := st
  exact (runCmdKFW_count hm hH _ n rfl true _ word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
    flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos h
    p (hrel.mark pos .next) hci).congr rfl rfl rfl

end Brotli.Decoder
