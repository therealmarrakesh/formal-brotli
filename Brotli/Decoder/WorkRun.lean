import Brotli.Decoder.WorkStream

/-!
# The work of the decoder's loop and of a call, against a potential

A potential on the stream's places holds what is still to do once the bits that make it necessary are read: a header's
potential and what its end costs, the commands' potential and what their end costs, and a round of a call for a
meta-block's start that waits for output space. A step's work is paid for by the potential and by the bits it reads, the
bytes it produces and the window it allocates; a step that stops the loop costs at most a constant more.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### What the stream's steps read in order take -/

theorem sStep_len {p q : SPhase} {bs c : List Bool} (h : sStep p bs = .next q c) : c.length ≤ bs.length := by
  obtain ⟨u, hu, _⟩ := nfaith_sStep p bs q c h
  rw [hu, List.length_append]
  omega

theorem sreach_len {p q : SPhase} {bs c : List Bool} (h : SReach p bs q c) : c.length ≤ bs.length := by
  induction h with
  | refl => exact Nat.le_refl _
  | next hs _ _ ih => exact Nat.le_trans ih (sStep_len hs)

/-- A meta-block's data and the stream's end. -/
def STail : SPhase → Prop
  | .skip .. => True
  | .raw .. => True
  | .ended _ => True
  | _ => False

theorem sStep_tail {p q : SPhase} {bs c : List Bool} (hp : STail p) (h : sStep p bs = .next q c) :
    STail q ∨ ∃ w st, q = .mblock w st := by
  cases p with
  | skip w st last n =>
    cases n with
    | zero =>
      have h' : ORes.next (afterBlock w last st) bs = .next q c := h
      cases h'
      unfold afterBlock
      cases last
      · exact Or.inr ⟨w, st, rfl⟩
      · exact Or.inl trivial
    | succ n =>
      have h' : readIn 8 (readInt 8) bs (fun _ b => (ORes.next (SPhase.skip w st last n) b : ORes SPhase (List UInt8))) =
          .next q c := h
      obtain ⟨v, b, _, e⟩ := readIn_next' h'
      cases e
      exact Or.inl trivial
  | raw w st last n =>
    cases n with
    | zero =>
      have h' : ORes.next (afterBlock w last st) bs = .next q c := h
      cases h'
      unfold afterBlock
      cases last
      · exact Or.inr ⟨w, st, rfl⟩
      · exact Or.inl trivial
    | succ n =>
      have h' : readIn 8 (readInt 8) bs (fun v b =>
          (ORes.next (SPhase.raw w ⟨v :: st.output, st.produced + 1, st.distances⟩ last n) b : ORes SPhase (List UInt8))) =
          .next q c := h
      obtain ⟨v, b, _, e⟩ := readIn_next' h'
      cases e
      exact Or.inl trivial
  | ended st =>
    have h' : (if bs.length % 8 = 0 then (if bs.isEmpty then ORes.exit (st.output.reverse.map Nat.toUInt8) bs else .bad)
        else match readFill bs with
          | some b => .next (.ended st) b
          | none => .bad) = .next q c := h
    split at h'
    · split at h' <;> cases h'
    · split at h'
      · cases h'
        exact Or.inl trivial
      · cases h'
  | _ => exact absurd hp id

/-- From a meta-block's data or the stream's end, the reading in order that passes no meta-block's start stays among
them or ends at a meta-block's start. -/
theorem sreach_tail {p q : SPhase} {bs c : List Bool} (h : SReach p bs q c) (hp : STail p) :
    STail q ∨ ∃ w st, q = .mblock w st := by
  induction h with
  | refl => exact Or.inl hp
  | @next p q1 r bs c1 d hs hq _ ih =>
    rcases sStep_tail hp hs with h1 | ⟨w, st, rfl⟩
    · exact ih h1
    · obtain ⟨rfl, -⟩ := hq w st rfl
      exact Or.inr ⟨w, st, rfl⟩

/-- A meta-block's start, read in order to where it leads: at least a bit, and at least 19 to a header. -/
theorem sreach_mblock {w : Nat} {st : StreamState} {q : SPhase} {bs c : List Bool} (h : SReach (.mblock w st) bs q c)
    (hne : ∀ w' st', q ≠ .mblock w' st') :
    c.length < bs.length ∧ (∀ w' st' l mlen g hp, q = .hdr w' st' l mlen g hp → c.length + 19 ≤ bs.length) := by
  cases h with
  | refl => exact absurd rfl (hne w st)
  | @next _ q1 _ _ c1 _ hs _ h' =>
    obtain ⟨ms, b, e1, e2⟩ := readIn_next' (show readIn 31 metaStart bs (fun ms b => startPlace w st ms b) = _ from hs)
    have hb : b.length < bs.length := takes_one faith_metaStart rfl e1
    have hc := sreach_len h'
    have hnh : STail q1 → ∀ w' st' l mlen g hp, q ≠ .hdr w' st' l mlen g hp := by
      intro ht w' st' l mlen g hp e
      rcases sreach_tail h' ht with h1 | ⟨w2, st2, h2⟩
      · rw [e] at h1
        exact h1
      · rw [e] at h2
        cases h2
    cases ms with
    | lastEmpty =>
      cases e2
      exact ⟨by omega, fun w' st' l mlen g hp e => absurd e (hnh trivial w' st' l mlen g hp)⟩
    | metadata last skip =>
      have e2' : (match readFill b with
          | some b' => ORes.next (SPhase.skip w st last skip) b'
          | none => .bad) = .next q1 c1 := e2
      split at e2'
      · rename_i b' hf
        cases e2'
        have := readFill_le hf
        exact ⟨by omega, fun w' st' l mlen g hp e => absurd e (hnh trivial w' st' l mlen g hp)⟩
      · cases e2'
    | data last mlen unc =>
      cases unc with
      | true =>
        have e2' : (match readFill b with
            | some b' => ORes.next (SPhase.raw w st last mlen) b'
            | none => .bad) = .next q1 c1 := e2
        split at e2'
        · rename_i b' hf
          cases e2'
          have := readFill_le hf
          exact ⟨by omega, fun w' st' l mlen g hp e => absurd e (hnh trivial w' st' l mlen g hp)⟩
        · cases e2'
      | false =>
        cases e2
        have := metaStart_data e1
        exact ⟨by omega, fun _ _ _ _ _ _ _ => by omega⟩

/-- WBITS, read in order: at least a bit. -/
theorem sreach_wbits {q : SPhase} {bs c : List Bool} (h : SReach .wbits bs q c) (hne : q ≠ .wbits) :
    c.length < bs.length := by
  cases h with
  | refl => exact absurd rfl hne
  | next hs _ h' =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show readIn 7 readWBITS bs _ = _ from hs)
    cases e2
    have := takes_one faith_readWBITS rfl e1
    have := sreach_len h'
    omega

/-- A byte of metadata or of uncompressed data, read in order: eight bits. -/
theorem sreach_byte {q : SPhase} {bs c : List Bool} {p : SPhase} (h : SReach p bs q c) (hne : q ≠ p)
    (hp : (∃ w st last n, p = .skip w st last (n + 1)) ∨ (∃ w st last n, p = .raw w st last (n + 1))) :
    c.length + 8 ≤ bs.length := by
  cases h with
  | refl => exact absurd rfl hne
  | next hs _ h' =>
    have := sreach_len h'
    rcases hp with ⟨w, st, last, n, rfl⟩ | ⟨w, st, last, n, rfl⟩
    · obtain ⟨v, b, e1, e2⟩ := readIn_next' (show readIn 8 (readInt 8) bs _ = _ from hs)
      cases e2
      have := readInt_length _ _ _ _ e1
      omega
    · obtain ⟨v, b, e1, e2⟩ := readIn_next' (show readIn 8 (readInt 8) bs _ = _ from hs)
      cases e2
      have := readInt_length _ _ _ _ e1
      omega

end Brotli.Decoder
