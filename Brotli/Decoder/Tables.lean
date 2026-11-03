import Brotli.Decoder.OrderSpec

/-!
# A header's tables, as far as its bits go

The tables a header's first bits need are those its reading in order completes on them: each step of that reading
completes at most one table, the same one whatever bits follow, and a reading cut short completes no more. So a header's
tables, as far as some of its bits go, are at most those of more of its bits.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### A header's tables, as far as its bits go -/

/-- A header that can't go on needs no more tables. -/
theorem tables_stuck {s : Gh × HPhase} {c : List Bool} (h : ∀ q r, hStepP s c ≠ .next q r) :
    (hrest tableK s.1 s.2 c).getD 0 = 0 := by
  obtain ⟨_, h2, h3, h4⟩ := hAgreeW tableK s.1 s.2 c
  cases e : hStepP s c with
  | next q r => exact absurd e (h q r)
  | exit m r => rw [h2 m r e]; rfl
  | bad => rw [h3 e]; rfl
  | short => rw [h4 e]; rfl

/-- A header's reading takes the same bits whatever follows them. -/
theorem reach_retail {s t : Gh × HPhase} {B c : List Bool} (h : Reach hStepP s B t c) :
    ∃ u, B = u ++ c ∧ ∀ T, Reach hStepP s (u ++ T) t T := by
  induction h with
  | refl => exact ⟨[], rfl, fun T => .refl _ _⟩
  | @next p0 b0 p1 b1 q c0 hst _ ih =>
    obtain ⟨u1, hb1, h1⟩ := ih
    obtain ⟨u0, hu0, hk⟩ := (ufaith_hStep p0.1 p0.2).1 b0 p1 b1 hst
    refine ⟨u0 ++ u1, by rw [hu0, hb1, List.append_assoc], fun T => ?_⟩
    rw [List.append_assoc]
    exact .next (hk (u1 ++ T)) (h1 T)

/-- The tables a header's reading completes on its way, whatever bits follow. -/
theorem chain_tables {s t : Gh × HPhase} {B c : List Bool} (h : Reach hStepP s B t c) :
    ∃ S u, B = u ++ c ∧ ∀ T, (hrest tableK s.1 s.2 (u ++ T)).getD 0 = S + (hrest tableK t.1 t.2 T).getD 0 := by
  induction h with
  | refl => exact ⟨0, [], rfl, fun T => by simp⟩
  | @next p0 b0 p1 b1 q c0 hst _ ih =>
    obtain ⟨S1, u1, hb1, h1⟩ := ih
    obtain ⟨u0, hu0, hk⟩ := (ufaith_hStep p0.1 p0.2).1 b0 p1 b1 hst
    obtain ⟨oc, u0', hu0', hw⟩ := (hAgreeW tableK p0.1 p0.2 b0).1 p1 b1 hst
    have e0 : u0' = u0 := List.append_cancel_right (hu0'.symm.trans hu0)
    refine ⟨tableOf oc + S1, u0 ++ u1, by rw [hu0, hb1, List.append_assoc], fun T => ?_⟩
    have hs1 := hk (u1 ++ T)
    rw [← e0] at hs1
    rw [List.append_assoc, ← e0, hw (u1 ++ T) hs1, wr_tableK, h1 T]
    omega

/-- The tables of a header's first bits, short of a place its reading reaches: at most those completed on the way there. -/
theorem tables_within {s t : Gh × HPhase} {P R Y : List Bool} (h : Reach hStepP s (P ++ R) t Y) (hY : Y.length < R.length) :
    (hrest tableK s.1 s.2 P).getD 0 + (hrest tableK t.1 t.2 Y).getD 0 ≤ (hrest tableK s.1 s.2 (P ++ R)).getD 0 := by
  obtain ⟨s', c', h1, h2, h3, h4⟩ := reach_cut (fun p => ufaith_hStep p.1 p.2) h hY
  obtain ⟨S1, u1, e1, v1⟩ := chain_tables h1
  obtain ⟨S2, u2, e2, v2⟩ := chain_tables h4
  have a1 := v1 c'
  rw [← e1, tables_stuck h2] at a1
  have a2 := v1 (c' ++ R)
  rw [← List.append_assoc, ← e1] at a2
  have a3 := v2 Y
  rw [← e2] at a3
  omega

/-- A meta-block's start, cut short: either it can't be read, or it reads the same. -/
theorem metaStart_prefix {b P R r : List Bool} {v : MetaStart} (hm : metaStart b = some (v, r)) (hb : b = P ++ R) :
    metaStart P = none ∨ ∃ r', r = r' ++ R ∧ metaStart P = some (v, r') := by
  cases e : metaStart P with
  | none => exact Or.inl rfl
  | some p =>
    obtain ⟨v', r'⟩ := p
    obtain ⟨u, hu, hf⟩ := faith_metaStart P v' r' e
    have h2 := hf (r' ++ R)
    rw [← List.append_assoc, ← hu, ← hb, hm] at h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact Or.inr ⟨r', rfl, rfl⟩

/-- The tables of a compressed meta-block's first bits. -/
theorem headerTables_le_of {b P R r : List Bool} {last : Bool} {mlen L : Nat} (hm : metaStart b = some (.data last mlen false, r))
    (hb : b = P ++ R) (hr : ∀ r', r = r' ++ R → (hrest tableK Gh.start (.cat .L) r').getD 0 ≤ L) : headerTables P ≤ L := by
  unfold headerTables
  rcases metaStart_prefix hm hb with e | ⟨r', e1, e2⟩
  · rw [e]
    exact Nat.zero_le _
  · rw [e2]
    exact hr r' e1

/-! ### The demand, as far as a stream's bits go -/

/-- What the meta-blocks from a meta-block's start need: its header's tables, or what the meta-blocks after it need. -/
theorem blocksT_leave (w : Nat) (st : StreamState) (bs : List Bool) :
    blocksT w st bs = max (headerTables bs) ((sLeave demandSem (.mblock w st) bs).getD 0) := by
  rw [blocksT_eq]
  congr 1
  show _ = (metaStart bs >>= fun p => afterStart w (demandSem.after w) st p.1 p.2).getD 0
  rw [← block_start w (demandSem.after w) st bs]
  cases readMetaBlock w st bs with
  | none => rfl
  | some p => rfl

/-- Away from a meta-block's start, leaving a place is worth what the place is. -/
theorem srest_leave {α : Type} (S : Sem α) {p : SPhase} (hp : ∀ w st, p ≠ .mblock w st) (bs : List Bool) :
    srest S p bs = sLeave S p bs := by
  cases p with
  | mblock w st => exact absurd rfl (hp w st)
  | _ => rfl

/-- A place where the reading in order stops leaves nothing more to demand. -/
theorem leave_stuck {p : SPhase} {B : List Bool} (hq : ∀ q' r, sStep p B ≠ .next q' r) :
    (sLeave demandSem p B).getD 0 = 0 := by
  by_cases he : ∃ st, p = .ended st
  · obtain ⟨st, rfl⟩ := he
    rfl
  · obtain ⟨_, h2, h3, h4⟩ := sAgreeS demandSem p (fun st e => he ⟨st, e⟩) B
    cases e : sStep p B with
    | next q' r => exact absurd e (hq q' r)
    | exit y r => rw [h2 y r e]; rfl
    | bad => rw [h3 e]; rfl
    | short => rw [h4 e]; rfl

/-- The demand of bits whose reading in order comes to a stop is at most the most tables any meta-block's start on the way
needs, as far as the bits go. -/
theorem demand_bound {T : Nat} {p q : SPhase} {B c : List Bool} (h : Reach sStep p B q c) (hq : ∀ q' r, sStep q c ≠ .next q' r)
    (hm : ∀ w st b, Reach sStep p B (.mblock w st) b → headerTables b ≤ T) : (srest demandSem p B).getD 0 ≤ T := by
  revert hm
  induction h with
  | refl p B =>
    intro hm
    by_cases hmb : ∃ w st, p = .mblock w st
    · obtain ⟨w, st, rfl⟩ := hmb
      show blocksT w st B ≤ T
      rw [blocksT_leave, leave_stuck hq]
      have := hm w st B (.refl _ _)
      omega
    · rw [srest_leave demandSem (fun w st e => hmb ⟨w, st, e⟩), leave_stuck hq]
      exact Nat.zero_le _
  | @next p0 b0 p1 b1 q c hs _ ih =>
    intro hm
    have ih' := ih hq (fun w st b h => hm w st b (.next hs h))
    have e := sNext demandSem demand_fillFree hs
    by_cases hmb : ∃ w st, p0 = .mblock w st
    · obtain ⟨w, st, rfl⟩ := hmb
      show blocksT w st b0 ≤ T
      rw [blocksT_leave, e]
      have := hm w st b0 (.refl _ _)
      omega
    · rw [srest_leave demandSem (fun w st e' => hmb ⟨w, st, e'⟩), e]
      exact ih'

/-- A meta-block without a compressed header needs no tables, however far its bits go. -/
theorem headerTables_none {b P R r : List Bool} {v : MetaStart} (hm : metaStart b = some (v, r))
    (hv : ∀ l ml, v ≠ .data l ml false) (hb : b = P ++ R) : headerTables P = 0 := by
  unfold headerTables
  rcases metaStart_prefix hm hb with e | ⟨r', _, e2⟩
  · rw [e]
  · rw [e2]
    cases v with
    | lastEmpty => rfl
    | metadata _ _ => rfl
    | data l ml u =>
      cases u with
      | false => exact absurd rfl (hv l ml)
      | true => rfl

end Brotli.Decoder
