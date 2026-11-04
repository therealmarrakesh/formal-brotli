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

/-! ### The potential on the stream's places -/

/-- A round of a call that pauses at a meta-block's start for output space, besides the bytes it hands out: the step that
pauses, the loop's and the call's rounds, and handing out. -/
def roundCost : Nat := 8

/-- What the commands' end costs: the round that ends the command loop, the check that every block type occurred, the
loop's round, and a round of the call at the next meta-block's start. -/
def cmdsEnd : Nat := 117 + 772 + 1 + roundCost

/-- What a header's end costs beyond its potential: its last step, `mkHdr`, the loop's round, and what the commands' start
holds. -/
def hdrEnd : Nat := hdrSlack + 218924 + 769 + 1 + 271 + cmdsEnd

/-- What a metadata block's or an uncompressed block's end costs: its last step and the loop's round, and a round of the
call at the next meta-block's start. -/
def tailEnd : Nat := 2 + roundCost

/-- The potential of a stream's place. -/
def spot : SPhase → Nat
  | .wbits => 0
  | .mblock .. => 0
  | .skip .. => tailEnd
  | .raw .. => tailEnd
  | .hdr _ _ _ _ g p => hpot g p + hdrEnd
  | .cmds _ _ _ p => cpot p + cmdsEnd
  | .ended _ => 0

/-- The potential of a state at a place: a meta-block's start with bytes waiting holds a round of the call. -/
def dpot (p : SPhase) (D : Dec) : Nat :=
  spot p + match p with
    | .mblock .. => if D.cmd.pend = 0 then 0 else roundCost
    | _ => 0

/-- A step's work against the potential: the potential at the place after it and the bits left there, with its work,
are at most the potential before, the bits there, 282 for each byte it produces, and `extra`. -/
def Pays (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (pos : USize) (r : Dec) (W extra : Nat) : Prop :=
  ∃ q, DRel r q ∧ OutD p q D r ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ t : List UInt8, W + dpot q r + hdrRate * (r.bits a r.pos stop (bits t)).length ≤
      dpot p D + hdrRate * (D.bits a pos stop (bits t)).length + 282 * (q.out.length - p.out.length) + extra

theorem dpot_mblock_le (w : Nat) (st : StreamState) (D : Dec) : dpot (.mblock w st) D ≤ roundCost := by
  unfold dpot spot
  dsimp only
  split <;> omega

/-! ### WBITS -/

theorem wbits_range {b : BitBuffer} (hw : b.Wf) (h : (wbitsFast b).status = .ok) :
    10 ≤ (wbitsFast b).a.toNat ∧ (wbitsFast b).a.toNat ≤ 24 := by
  have e := ((wbitsFast_ok hw).ok h).2 []
  rw [List.append_nil, List.append_nil] at e
  exact readWBITS_range e

/-- WBITS's step that goes on: the window's zeros, and eleven, with the loop's round. -/
theorem wbitsW_next {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf) (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status = .next) :
    stepDWbitsW a stop hs D pos + 1 ≤ 5 * 2 ^ (stepDWbits a stop hs D pos).k.toNat + 77 := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepDWbits at hn ⊢
  unfold stepDWbitsW
  rw [dite_eq_left hp'] at hn ⊢
  rw [dite_eq_left hp']
  have hR := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs hp
  obtain ⟨h1, -⟩ := refill_spec hs hp hw
  have hrange := wbits_range h1
  dsimp only at hn ⊢
  split at hn
  · exact absurd hn (fun e => DStatus.noConfusion e)
  · exact absurd hn (fun e => DStatus.noConfusion e)
  · rename_i heq
    obtain ⟨ha1, ha2⟩ := hrange heq
    split at hn
    · rename_i hl
      rw [heq]
      dsimp only
      rw [ite_eq_left hl, ite_eq_left hl]
      have hb2 : (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
          (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat ≤ 24 := ha2
      generalize (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a = x at hb2 ⊢
      have hk : x.toUSize.toNat = x.toNat := word_toUSize (by omega)
      have hsh : ((1 : UInt64) <<< x).toNat = 2 ^ x.toNat := one_shl (by omega)
      show _ + (zbW ((1 : UInt64) <<< x).toNat + 1) + 1 ≤ 5 * 2 ^ x.toUSize.toNat + 77
      rw [hk, hsh]
      have := zbW_le (2 ^ x.toNat)
      omega
    · exact absurd hn (fun e => DStatus.noConfusion e)

/-- WBITS's step that doesn't go on: at most eleven, with the loop's round. -/
theorem wbitsW_stop {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status ≠ .next) : stepDWbitsW a stop hs D pos + 1 ≤ 11 := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepDWbits at hn
  unfold stepDWbitsW
  rw [dite_eq_left hp'] at hn
  rw [dite_eq_left hp']
  have hR := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs hp
  dsimp only at hn ⊢
  split
  · rename_i heq
    rw [heq] at hn
    dsimp only at hn
    split
    · rename_i hl
      rw [ite_eq_left hl] at hn
      exact absurd rfl hn
    · omega
  · omega

/-- WBITS's step, against the potential. -/
theorem pay_wbits {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D .wbits)
    (hp : pos.toNat ≤ stop.toNat) :
    ((stepDWbits a stop hs D pos).status = .next → Pays a stop .wbits D pos (stepDWbits a stop hs D pos)
      (stepDWbitsW a stop hs D pos + 1) (5 * 2 ^ (stepDWbits a stop hs D pos).k.toNat)) ∧
    ((stepDWbits a stop hs D pos).status = .needsInput → Pays a stop .wbits D pos (stepDWbits a stop hs D pos)
      (stepDWbitsW a stop hs D pos + 1) 11) ∧
    ((stepDWbits a stop hs D pos).status ≠ .next → stepDWbitsW a stop hs D pos + 1 ≤ 11) := by
  have hok := stepDWbits_ok (S := specSem) (hs := hs) hrel hp
  have hR : hdrRate = 22343 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => wbitsW_stop hp hn⟩
  · have hW := wbitsW_next (hs := hs) hrel.2.1 hp hn
    obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    have hne : p' ≠ .wbits := fun e => by rw [e] at hsd; exact hsd
    have hb := sreach_wbits (hj t) hne
    cases p' with
    | mblock w st =>
      have := dpot_mblock_le w st (stepDWbits a stop hs D pos)
      have h0 : dpot .wbits D = 0 := rfl
      rw [h0, hR]
      unfold roundCost at this
      omega
    | _ => exact absurd hsd id
  · have hn' : (stepDWbits a stop hs D pos).status ≠ .next := by rw [hn]; exact fun e => DStatus.noConfusion e
    have hW := wbitsW_stop (hs := hs) (D := D) hp hn'
    obtain ⟨b1, b2, p', hR', _, _, hsd, _, hout, hj, _⟩ := hok.needsInput hn
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun t => ?_⟩
    have hb := sreach_len (hj t)
    cases p' with
    | wbits =>
      have h0 : ∀ E, dpot .wbits E = 0 := fun _ => rfl
      rw [h0, h0, hR]
      omega
    | _ => exact absurd hsd id

end Brotli.Decoder
