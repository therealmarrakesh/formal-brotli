module

public import Brotli.Decoder.OrderSpec

@[expose] public section

/-!
# A header's tables, as far as its bits go

The tables a header's first bits need are what its reading in order reserves on them: a step of that reading reserves at
most once, the same whatever bits follow, and a reading cut short reserves no more. So a header's tables, as far as some
of its bits go, are at most those of more of its bits.
-/

namespace Brotli.Decoder

open Brotli.Spec

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

/-- The tables a header's reading reserves on its way, whatever bits follow. -/
theorem chain_tables {s t : Gh × HPhase} {B c : List Bool} (h : Reach hStepP s B t c) :
    ∃ S u, B = u ++ c ∧ ∀ T, (hrest tableK s.1 s.2 (u ++ T)).getD 0 = S + (hrest tableK t.1 t.2 T).getD 0 := by
  induction h with
  | refl => exact ⟨0, [], rfl, fun T => by simp⟩
  | @next p0 b0 p1 b1 q c0 hst _ ih =>
    obtain ⟨S1, u1, hb1, h1⟩ := ih
    obtain ⟨u0, hu0, hk⟩ := (ufaith_hStep p0.1 p0.2).1 b0 p1 b1 hst
    obtain ⟨oc, u0', hu0', hw⟩ := (hAgreeW tableK p0.1 p0.2 b0).1 p1 b1 hst
    have e0 : u0' = u0 := List.append_cancel_right (hu0'.symm.trans hu0)
    refine ⟨resOf oc + S1, u0 ++ u1, by rw [hu0, hb1, List.append_assoc], fun T => ?_⟩
    have hs1 := hk (u1 ++ T)
    rw [← e0] at hs1
    rw [List.append_assoc, ← e0, hw (u1 ++ T) hs1, wr_tableK, h1 T]
    omega

/-- The tables of a header's first bits, short of a place its reading reaches: at most those reserved on the way there. -/
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

/-! ### Before the stream's first meta-block with data -/

/-- A place before the stream's first meta-block with data. -/
def NoData : SPhase → Prop
  | .wbits => True
  | .mblock _ st | .skip _ st _ _ | .ended st => st.produced = 0
  | .raw .. | .hdr .. | .cmds .. => False

/-- A place in or after the stream's first meta-block with data: bytes produced, or to come in its meta-block. -/
def Past : SPhase → Prop
  | .wbits => False
  | .mblock _ st | .skip _ st _ _ | .ended st => st.produced ≠ 0
  | .raw _ st _ n => 1 ≤ st.produced + n
  | .hdr _ st _ mlen _ _ => 1 ≤ st.produced + mlen
  | .cmds _ _ _ q => CLive q

theorem noData_past {p : SPhase} (h1 : NoData p) (h2 : Past p) : False := by
  cases p with
  | wbits => exact h2
  | mblock => exact h2 h1
  | skip => exact h2 h1
  | ended => exact h2 h1
  | raw => exact h1
  | hdr => exact h1
  | cmds => exact h1

private theorem past_after {w : Nat} {last : Bool} {st : StreamState} (h : st.produced ≠ 0) : Past (afterBlock w last st) := by
  cases last <;> exact h

/-- Once a meta-block with data has started, the reading in order stays past it. -/
theorem past_step : ∀ (p : SPhase) (bs : List Bool) (q : SPhase) (c : List Bool), Past p → sStep p bs = .next q c → Past q
  | .wbits, _, _, _, h, _ => h.elim
  | .mblock w st, bs, q, c, hp, h => by
    obtain ⟨ms, b, _, e2⟩ := readIn_next' h
    have hp' : st.produced ≠ 0 := hp
    cases ms with
    | lastEmpty => cases e2; exact hp'
    | metadata last skip =>
      simp only [startPlace] at e2
      split at e2 <;> cases e2
      exact hp'
    | data last mlen unc =>
      cases unc with
      | true =>
        simp only [startPlace, ↓reduceIte] at e2
        split at e2 <;> cases e2
        show 1 ≤ st.produced + mlen
        omega
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        show 1 ≤ st.produced + mlen
        omega
  | .skip w st last 0, bs, q, c, hp, h => by
    cases h
    exact past_after hp
  | .skip w st last (n + 1), bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' h
    cases e2
    exact hp
  | .raw w st last 0, bs, q, c, hp, h => by
    cases h
    have hp' : 1 ≤ st.produced + 0 := hp
    exact past_after (by omega)
  | .raw w st last (n + 1), bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' h
    cases e2
    have hp' : 1 ≤ st.produced + (n + 1) := hp
    show 1 ≤ st.produced + 1 + n
    omega
  | .hdr w st last mlen g p, bs, q, c, hp, h => by
    cases e : hStep g p bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      exact hp
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      exact hp
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .cmds w last m p, bs, q, c, hp, h => by
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      exact cStep_live _ _ _ _ hp e
    | exit s b =>
      obtain ⟨rfl, h0⟩ := cStep_exit e
      have hl : 1 ≤ s.produced + s.remaining := hp
      have hb : sStep (.cmds w last m (.command s)) bs = if usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance then .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b else .bad := by
        simp only [sStep, e]
      rw [hb] at h
      split at h
      · cases h
        exact past_after (show s.produced ≠ 0 by omega)
      · cases h
    | bad =>
      have h' : sStep (.cmds w last m p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.cmds w last m p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .ended st, bs, q, c, hp, h => by
    by_cases hm : bs.length % 8 = 0
    · simp only [sStep, hm, ↓reduceIte] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
      | some b =>
        simp only [sStep, hm, ↓reduceIte, e] at h
        cases h
        exact hp

/-- Before the first meta-block with data, the reading in order stays before it or starts it. -/
theorem noData_step : ∀ (p : SPhase) (bs : List Bool) (q : SPhase) (c : List Bool), NoData p → sStep p bs = .next q c →
    NoData q ∨ Past q
  | .wbits, bs, q, c, _, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' h
    cases e2
    exact Or.inl rfl
  | .mblock w st, bs, q, c, hp, h => by
    obtain ⟨ms, b, e1, e2⟩ := readIn_next' h
    have hp' : st.produced = 0 := hp
    have hms := metaStart_ok e1
    cases ms with
    | lastEmpty => cases e2; exact Or.inl hp'
    | metadata last skip =>
      simp only [startPlace] at e2
      split at e2 <;> cases e2
      exact Or.inl hp'
    | data last mlen unc =>
      have hm1 : 1 ≤ mlen := hms.1
      cases unc with
      | true =>
        simp only [startPlace, ↓reduceIte] at e2
        split at e2 <;> cases e2
        exact Or.inr (show 1 ≤ st.produced + mlen by omega)
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        exact Or.inr (show 1 ≤ st.produced + mlen by omega)
  | .skip w st last 0, bs, q, c, hp, h => by
    cases h
    cases last <;> exact Or.inl hp
  | .skip w st last (n + 1), bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' h
    cases e2
    exact Or.inl hp
  | .ended st, bs, q, c, hp, h => by
    by_cases hm : bs.length % 8 = 0
    · simp only [sStep, hm, ↓reduceIte] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
      | some b =>
        simp only [sStep, hm, ↓reduceIte, e] at h
        cases h
        exact Or.inl hp
  | .raw .., _, _, _, hp, _ => hp.elim
  | .hdr .., _, _, _, hp, _ => hp.elim
  | .cmds .., _, _, _, hp, _ => hp.elim

theorem past_reach {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) (hp : Past p) : Past q := by
  induction h with
  | refl => exact hp
  | next hs _ ih => exact ih (past_step _ _ _ _ hp hs)

theorem noData_reach {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) (hp : NoData p) : NoData q ∨ Past q := by
  induction h with
  | refl => exact Or.inl hp
  | next hs r ih =>
    rcases noData_step _ _ _ _ hp hs with h1 | h1
    · exact ih h1
    · exact Or.inr (past_reach r h1)

/-- The window's worth ignores the fill bits at the stream's end. -/
theorem win_fillFree : FillFree winSem := fun _ _ _ _ => rfl

/-- A step before the first meta-block with data keeps the window's worth. -/
theorem win_step {p q : SPhase} {bs c : List Bool} (hp : NoData p) (hq : NoData q) (h : sStep p bs = .next q c) :
    srest winSem p bs = srest winSem q c := by
  rw [← sNext winSem win_fillFree h]
  by_cases hmb : ∃ w st, p = .mblock w st
  · obtain ⟨w, st, rfl⟩ := hmb
    have hp' : st.produced = 0 := hp
    obtain ⟨ms, b, e1, e2⟩ := readIn_next' (show readIn 31 metaStart bs (fun ms b => startPlace w st ms b) = _ from h)
    have hv : ∀ l ml u, ms ≠ .data l ml u := by
      rintro l ml u rfl
      cases u with
      | true =>
        simp only [startPlace, ↓reduceIte] at e2
        split at e2 <;> cases e2
        exact hq
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        exact hq
    show (if st.produced = 0 then winFrom w bs else some w) = _
    rw [ite_eq_left hp']
    exact winFrom_leave hp' e1 hv
  · exact srest_leave winSem (fun w st e => hmb ⟨w, st, e⟩) bs

/-- The reading in order before the first meta-block with data keeps the window's worth. -/
theorem win_reach {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) (hp : NoData p) (hq : NoData q) :
    srest winSem p bs = srest winSem q c := by
  induction h with
  | refl => rfl
  | next hs r ih =>
    rcases noData_step _ _ _ _ hp hs with h1 | h1
    · exact (win_step hp h1 hs).trans (ih h1 hq)
    · exact absurd (past_reach r h1) (fun e => noData_past hq e)

/-- Where the reading in order before the first meta-block with data can't go on, it allocates no window. -/
theorem win_stuck {p : SPhase} {c : List Bool} (hp : NoData p) (h : ∀ q r, sStep p c ≠ .next q r) : srest winSem p c = none := by
  cases p with
  | wbits =>
    show (readWBITS c >>= fun p => winFrom (windowSize p.1) p.2) = none
    cases e : readWBITS c with
    | none => rfl
    | some v =>
      obtain ⟨v, b⟩ := v
      exact absurd (readIn_some (room := 7) (k := fun v b => (ORes.next (SPhase.mblock (windowSize v) ⟨[], 0, initialDistances⟩) b :
        ORes SPhase (List UInt8))) e) (h _ _)
  | mblock w st =>
    have hp' : st.produced = 0 := hp
    show (if st.produced = 0 then winFrom w c else some w) = none
    rw [ite_eq_left hp']
    cases e : metaStart c with
    | none => exact winFrom_none (fun v b e' => by rw [e] at e'; cases e')
    | some v =>
      obtain ⟨ms, b⟩ := v
      have hs : sStep (.mblock w st) c = startPlace w st ms b := readIn_some e
      cases ms with
      | lastEmpty => exact absurd hs (h _ _)
      | metadata last skip =>
        rw [winFrom_meta e]
        cases hf : readFill b with
        | none => rfl
        | some b1 =>
          refine absurd hs ?_
          simp only [startPlace, hf]
          exact h _ _
      | data last mlen unc =>
        rw [winFrom_data e]
        cases unc with
        | true =>
          cases hf : readFill b with
          | none => rfl
          | some b1 =>
            refine absurd hs ?_
            simp only [startPlace, ↓reduceIte, hf]
            exact h _ _
        | false =>
          refine absurd hs ?_
          simp only [startPlace, Bool.false_eq_true, ↓reduceIte]
          exact h _ _
  | skip w st last n =>
    cases n with
    | zero => exact absurd rfl (h _ _)
    | succ n =>
      cases e : readInt 8 c with
      | some v =>
        obtain ⟨v, b⟩ := v
        exact absurd (readIn_some (room := 8) (k := fun _ b => (ORes.next (SPhase.skip w st last n) b : ORes SPhase (List UInt8))) e) (h _ _)
      | none =>
        have hl : c.length < 8 := by
          rcases Nat.lt_or_ge c.length 8 with h8 | h8
          · exact h8
          · obtain ⟨v, hv⟩ := readInt_of_le 8 c h8
            rw [hv] at e
            cases e
        show (if c.length < (n + 1) * 8 then none else _) = none
        rw [ite_eq_left (by omega)]
  | ended => rfl
  | raw => exact hp.elim
  | hdr => exact hp.elim
  | cmds => exact hp.elim

/-- The window of a meta-block's data place. -/
def winOfPlace : SPhase → Nat
  | .raw w .. | .hdr w .. => w
  | .wbits | .mblock .. | .skip .. | .cmds .. | .ended _ => 0

/-- The step that starts the first meta-block with data: the window's worth is the window it is read with. -/
theorem win_start {p q : SPhase} {bs c : List Bool} (hp : NoData p) (hq : Past q) (h : sStep p bs = .next q c) :
    srest winSem p bs = some (winOfPlace q) := by
  cases p with
  | mblock w st =>
    have hp' : st.produced = 0 := hp
    obtain ⟨ms, b, e1, e2⟩ := readIn_next' (show readIn 31 metaStart bs (fun ms b => startPlace w st ms b) = _ from h)
    show (if st.produced = 0 then winFrom w bs else some w) = _
    rw [ite_eq_left hp']
    cases ms with
    | lastEmpty => cases e2; exact absurd hp' hq
    | metadata last skip =>
      simp only [startPlace] at e2
      split at e2 <;> cases e2
      exact absurd hp' hq
    | data last mlen unc =>
      rw [winFrom_data e1]
      cases unc with
      | true =>
        simp only [startPlace, ↓reduceIte] at e2
        split at e2
        · rename_i b' hf
          cases e2
          rw [ite_eq_left rfl, hf]
          rfl
        · cases e2
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        rw [ite_eq_right (fun e => Bool.noConfusion e)]
        show some (blockWindow w ⟨[], 0, initialDistances⟩ last mlen) = some (blockWindow w st last mlen)
        unfold blockWindow
        rw [hp']
  | wbits =>
    obtain ⟨v, b, _, e2⟩ := readIn_next' h
    cases e2
    exact absurd rfl hq
  | skip w st last n =>
    have hq0 : NoData q := by
      cases n with
      | zero => cases h; cases last <;> exact hp
      | succ n => obtain ⟨v, b, _, e2⟩ := readIn_next' h; cases e2; exact hp
    exact absurd hq (fun e => noData_past hq0 e)
  | ended st =>
    have hq0 : NoData q := by
      by_cases hm : bs.length % 8 = 0
      · simp only [sStep, hm, ↓reduceIte] at h
        split at h <;> cases h
      · cases e : readFill bs with
        | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
        | some b =>
          simp only [sStep, hm, ↓reduceIte, e] at h
          cases h
          exact hp
    exact absurd hq (fun e => noData_past hq0 e)
  | raw => exact hp.elim
  | hdr => exact hp.elim
  | cmds => exact hp.elim

/-- Once the reading in order is past the first meta-block with data, the window's worth is settled by the bits read before,
whatever whole bytes follow them. -/
theorem win_fixed {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) (hp : NoData p) (hq : Past q) :
    ∃ v u r, bs = u ++ r ∧ c.length ≤ r.length ∧ ∀ T : List Bool, T.length % 8 = r.length % 8 → srest winSem p (u ++ T) = some v := by
  induction h with
  | refl => exact absurd hq (fun e => noData_past hp e)
  | @next p0 b0 p1 b1 q0 c0 hs r ih =>
    obtain ⟨u0, hu0, hk⟩ := nfaith_sStep p0 b0 p1 b1 hs
    rcases noData_step _ _ _ _ hp hs with h1 | h1
    · obtain ⟨v, u, r', e1, e2, e3⟩ := ih h1 hq
      refine ⟨v, u0 ++ u, r', by rw [hu0, e1, List.append_assoc], e2, fun T hT => ?_⟩
      have hs' := hk (u ++ T) (by rw [e1, List.length_append, List.length_append]; omega)
      rw [List.append_assoc, win_step hp h1 hs']
      exact e3 T hT
    · have hl : c0.length ≤ b1.length := by
        obtain ⟨u1, hu1⟩ := reach_suffix nfaith_sStep r
        rw [hu1, List.length_append]
        omega
      exact ⟨winOfPlace p1, u0, b1, hu0, hl, fun T hT => win_start hp h1 (hk T hT)⟩

/-- The window allocated from a meta-block's start stays allocated when whole bytes follow. -/
theorem winFrom_ext (w : Nat) : ∀ (n : Nat) (P : List Bool), P.length = n → ∀ (F : List Bool) (v : Nat), F.length % 8 = 0 →
    winFrom w P = some v → winFrom w (P ++ F) = some v := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro P hn F v hF hv
    cases hm : metaStart P with
    | none => rw [winFrom_none (fun v' b' e => by rw [hm] at e; cases e)] at hv; cases hv
    | some q =>
      obtain ⟨ms, b⟩ := q
      obtain ⟨u, hu, hf⟩ := faith_metaStart P ms b hm
      have hm' : metaStart (P ++ F) = some (ms, b ++ F) := by rw [hu, List.append_assoc]; exact hf _
      have hlt := takes_one faith_metaStart rfl hm
      cases ms with
      | lastEmpty => rw [winFrom_none (fun v' b' e => by rw [hm] at e; cases e; rfl)] at hv; cases hv
      | metadata last skip =>
        rw [winFrom_meta hm] at hv
        rw [winFrom_meta hm']
        cases hfl : readFill b with
        | none => rw [hfl] at hv; cases hv
        | some b1 =>
          rw [hfl] at hv
          obtain ⟨u1, hu1, hk1⟩ := faith_readFill hfl
          have hfl' : readFill (b ++ F) = some (b1 ++ F) := by
            rw [hu1, List.append_assoc]
            exact hk1 _ (by rw [List.length_append]; omega)
          rw [hfl']
          have hl := readFill_len hfl
          dsimp only [bind, Option.bind] at hv ⊢
          by_cases h1 : b1.length < skip * 8
          · rw [ite_eq_left h1] at hv; cases hv
          · rw [ite_eq_right h1] at hv
            rw [ite_eq_right (by rw [List.length_append]; omega)]
            cases last with
            | true => cases hv
            | false =>
              rw [ite_eq_right (fun e => Bool.noConfusion e)] at hv ⊢
              rw [List.drop_append_of_le_length (by omega)]
              exact ih _ (by rw [← hn, List.length_drop]; omega) _ rfl F v hF hv
      | data last mlen unc =>
        rw [winFrom_data hm] at hv
        rw [winFrom_data hm']
        cases unc with
        | true =>
          rw [ite_eq_left rfl] at hv ⊢
          cases hfl : readFill b with
          | none => rw [hfl] at hv; simp at hv
          | some b1 =>
            rw [hfl] at hv
            obtain ⟨u1, hu1, hk1⟩ := faith_readFill hfl
            have hfl' : readFill (b ++ F) = some (b1 ++ F) := by
              rw [hu1, List.append_assoc]
              exact hk1 _ (by rw [List.length_append]; omega)
            rw [hfl']
            exact hv
        | false => exact hv

/-- The window allocated for a stream's bits stays allocated when whole bytes follow. -/
theorem winFirst_ext {P F : List Bool} {v : Nat} (hF : F.length % 8 = 0) (h : winSem.first P = some v) :
    winSem.first (P ++ F) = some v := by
  show (readWBITS (P ++ F) >>= fun p => winFrom (windowSize p.1) p.2) = _
  have h' : (readWBITS P >>= fun p => winFrom (windowSize p.1) p.2) = some v := h
  cases e : readWBITS P with
  | none => rw [e] at h'; cases h'
  | some q =>
    obtain ⟨k, b⟩ := q
    rw [e] at h'
    obtain ⟨u, hu, hf⟩ := faith_readWBITS P k b e
    rw [hu, List.append_assoc, hf]
    exact winFrom_ext _ _ b rfl F v hF h'

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
