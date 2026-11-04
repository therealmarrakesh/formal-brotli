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

/-! ### A meta-block's start -/

theorem metaGo_hd {D : Dec} {c : Cmd} {r : Rd} {pos : USize} (ht : D.tag = .mblock) (h : (metaGo D c r pos).tag = .hdr) :
    (metaGo D c r pos).hd = hdStart r.word r.count D.limit := by
  unfold metaGo at h ⊢
  by_cases h0 : r.a = 0
  · rw [ite_eq_left h0] at h
    cases h
  · rw [ite_eq_right h0] at h ⊢
    by_cases h1 : r.a = 1
    · rw [ite_eq_left h1] at h
      split at h
      · cases h
      · dsimp only at h
        rw [ht] at h
        cases h
    · rw [ite_eq_right h1] at h ⊢
      by_cases h2 : (r.d != 0) = true
      · rw [ite_eq_left h2] at h
        split at h
        · cases h
        · dsimp only at h
          rw [ht] at h
          cases h
      · rw [ite_eq_right h2]

/-- A meta-block's start that leads to a header leaves the header machine at its start. -/
theorem stepDMeta_hd {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (ht : D.tag = .mblock)
    (h : (stepDMeta a stop hs D pos).tag = .hdr) : ∃ x y z, (stepDMeta a stop hs D pos).hd = hdStart x y z := by
  unfold stepDMeta at h ⊢
  by_cases h0 : D.cmd.pend = 0
  · rw [ite_eq_left h0] at h ⊢
    by_cases hp : pos ≤ stop
    · rw [dite_eq_left hp] at h ⊢
      dsimp only at h ⊢
      split at h
      · dsimp only at h
        rw [ht] at h
        cases h
      · dsimp only at h
        rw [ht] at h
        cases h
      · exact ⟨_, _, _, metaGo_hd ht h⟩
    · rw [dite_eq_right hp] at h
      dsimp only at h
      rw [ht] at h
      cases h
  · rw [ite_eq_right h0] at h
    dsimp only at h
    rw [ht] at h
    cases h

/-- A header's start holds the potential of the literal category's number of block types not yet read. -/
theorem hpot_start {x y z : UInt64} {g : Gh} {p : HPhase} (h : HRel (hdStart x y z) g p) : hpot g p = 4735 := by
  have ht := h.tag_eq
  cases p with
  | cat i =>
    have hc : (hdStart x y z).cat = i := h.2.2.2
    cases i with
    | L => rfl
    | I => cases hc
    | D => cases hc
  | _ => cases ht

theorem metaW_le {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hp : pos.toNat ≤ stop.toNat) :
    stepDMetaW a stop hs D pos ≤ 11 := by
  unfold stepDMetaW
  have := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs hp
  split
  · split <;> omega
  · omega

/-- A meta-block's start, against the potential. -/
theorem pay_mblock {w : Nat} {st : StreamState} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.mblock w st)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepDMeta a stop hs D pos).status = .next → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) 0) ∧
    ((stepDMeta a stop hs D pos).status = .needsInput → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) 12) ∧
    ((stepDMeta a stop hs D pos).status = .needsOutput → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) 2) ∧
    stepDMetaW a stop hs D pos + 1 ≤ 12 := by
  have hok := stepDMeta_ok (S := specSem) (hs := hs) hrel hp
  have hW := metaW_le (hs := hs) (D := D) hp
  have hR : hdrRate = 22343 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_, by omega⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    have hne : ∀ w' st', p' ≠ .mblock w' st' := fun w' st' e => by rw [e] at hsd; exact hsd
    obtain ⟨hb, hb19⟩ := sreach_mblock (hj t) hne
    rw [hR]
    cases p' with
    | ended st' =>
      have : dpot (.ended st') (stepDMeta a stop hs D pos) = 0 := rfl
      omega
    | skip w' st' l n =>
      have : dpot (.skip w' st' l n) (stepDMeta a stop hs D pos) = 10 := rfl
      omega
    | raw w' st' l n =>
      have : dpot (.raw w' st' l n) (stepDMeta a stop hs D pos) = 10 := rfl
      omega
    | hdr w' st' l mlen g hp' =>
      have h19 := hb19 w' st' l mlen g hp' rfl
      obtain ⟨x, y, z, hx⟩ := stepDMeta_hd hrel.1 hR'.1
      have hrh : HRel (hdStart x y z) g hp' := by rw [← hx]; exact hR'.2.2.2.2.2.2.1
      have : dpot (.hdr w' st' l mlen g hp') (stepDMeta a stop hs D pos) = hpot g hp' + hdrEnd := by
        unfold dpot spot
        dsimp only
        omega
      rw [this, hpot_start hrh]
      unfold hdrEnd hdrSlack cmdsEnd roundCost
      omega
    | _ => exact absurd hsd id
  · obtain ⟨b1, b2, p', hR', _, _, hsd, _, hout, hj, _⟩ := hok.needsInput hn
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun t => ?_⟩
    have hb := sreach_len (hj t)
    rw [hR]
    cases p' with
    | mblock w' st' =>
      have he : dpot (.mblock w' st') (stepDMeta a stop hs D pos) = dpot (.mblock w st) D := by
        unfold dpot spot
        dsimp only
        rw [hsd]
      rw [he]
      omega
    | _ => exact absurd hsd id
  · obtain ⟨p', hR', h1, h2, _, _, hsd, _, hout, hj⟩ := hok.needsOutput hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    have hb := sreach_len (hj t)
    have hw1 : stepDMetaW a stop hs D pos = 1 := by
      have hpe : D.cmd.pend ≠ 0 := by
        unfold stepDMeta at hn
        intro e
        rw [ite_eq_left e] at hn
        by_cases hp' : pos ≤ stop
        · rw [dite_eq_left hp'] at hn
          dsimp only at hn
          split at hn
          · cases hn
          · cases hn
          · rename_i heq
            unfold metaGo at hn
            repeat' (first | split at hn | cases hn)
        · rw [dite_eq_right hp'] at hn
          cases hn
      unfold stepDMetaW
      rw [ite_eq_right hpe]
    rw [hR, hw1]
    cases p' with
    | mblock w' st' =>
      have he : dpot (.mblock w' st') (stepDMeta a stop hs D pos) = dpot (.mblock w st) D := by
        unfold dpot spot
        dsimp only
        rw [hsd]
      rw [he]
      omega
    | _ => exact absurd hsd id

/-! ### A header -/

theorem psize_le {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) : psize p ≤ 704 := by
  cases p with
  | code o n => exact h.2.2.2.1.2.2
  | clens o n _ _ _ => exact h.2.2.2.1.2.2
  | syms o n _ _ => exact h.2.2.2.1.2.2
  | _ => exact Nat.zero_le _

/-- A header's step, against the potential: a step that goes on is paid by the header's potential and bits, the header's
end by what the header holds for it, and a step that runs out of input costs at most 269. -/
theorem pay_hdr {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.hdr w st last mlen g p)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepDHdr a stop hs D pos).status = .next → Pays a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos)
      (stepDHdrW a stop hs D pos + 1) 0) ∧
    ((stepDHdr a stop hs D pos).status = .needsInput → Pays a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos)
      (stepDHdrW a stop hs D pos + 1) 269) ∧
    ((stepDHdr a stop hs D pos).status ≠ .next → stepDHdrW a stop hs D pos + 1 ≤ hpot g p + hdrSlack) := by
  have hok := stepDHdr_ok (S := specSem) (hs := hs) hrel hp
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hall, hl, hleft, hm1, hm2, hR, hp0⟩ := hrel
  have ht' : tag = .hdr := ht
  subst ht'
  dsimp only at hR
  have hstep := stepH_ok (K := hdrK w (specSem.after w last) st mlen) (a := a) (hs := hs) hR hp
  have hsz := psize_le hR
  have eW : stepDHdrW a stop hs ⟨.hdr, cmd, hd, H, k, last', left, limit, pos', status⟩ pos =
      stepHW a stop hs hd pos + (if (stepH a stop hs hd pos).status = .ready then mkHdrW (stepH a stop hs hd pos).d + 769 else 0) := rfl
  rw [eW]
  unfold stepDHdr takeHd at hok ⊢
  dsimp only at hok ⊢
  cases hst : (stepH a stop hs hd pos).status
  case next =>
    obtain ⟨g', p', oc, hR', h1, h2, _, _, _, h5⟩ := hstep.next hst
    have hW := stepHW_cost hR hp hst hR' h5
    rw [ite_eq_right (fun e => HStatus.noConfusion e)]
    refine ⟨fun _ => ⟨.hdr w st last mlen g' p', ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0⟩,
      ⟨[], rfl, rfl⟩, h1, h2, fun t => ?_⟩, fun e => DStatus.noConfusion e, fun e => absurd rfl e⟩
    have hpy := hpay hsz (h5 (bits t))
    simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, clearHd]
    omega
  case needsInput =>
    obtain ⟨b1, b2, hR', _, _, _, h6, _⟩ := hstep.needsInput hst
    have hW := stepHW_short (hs := hs) (st := hd) (pos := pos) hst
    rw [ite_eq_right (fun e => HStatus.noConfusion e)]
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨.hdr w st last mlen g p,
      ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0⟩, ⟨[], rfl, rfl⟩,
      by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun t => ?_⟩, fun _ => ?_⟩
    · simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, clearHd]
      rw [h6]
      omega
    · unfold hdrSlack
      omega
  case bad =>
    have hW := stepHW_stop hR hp (by rw [hst]; exact fun e => HStatus.noConfusion e)
    rw [ite_eq_right (fun e => HStatus.noConfusion e)]
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => by omega⟩
  case memory =>
    have hW := stepHW_stop hR hp (by rw [hst]; exact fun e => HStatus.noConfusion e)
    rw [ite_eq_right (fun e => HStatus.noConfusion e)]
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => by omega⟩
  case ready =>
    obtain ⟨g', hu, -, -, -, -, -, -, -, -⟩ := hstep.ready hst
    obtain ⟨H', hmk, -, -⟩ := mkHdr_ok hu
    have hW := stepHW_stop hR hp (by rw [hst]; exact fun e => HStatus.noConfusion e)
    have hM := mkHdrW_le hu
    rw [ite_eq_left rfl]
    rw [hst] at hok
    dsimp only at hok
    rw [hmk] at hok ⊢
    dsimp only at hok ⊢
    refine ⟨fun _ => ?_, fun e => DStatus.noConfusion e, fun e => absurd rfl e⟩
    obtain ⟨p', hR'', h1', h2', _, _, hout, hj⟩ := hok.next rfl
    refine ⟨p', hR'', hout, h1', h2', fun t => ?_⟩
    have hb := sreach_len (hj t)
    cases p' with
    | cmds w' l' m' cp =>
      have := cpot_le cp
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot] at hb ⊢
      unfold hdrEnd
      rw [hdrRate_eq]
      omega
    | _ => exact absurd hR''.1 (fun e => DTag.noConfusion e)

/-! ### Metadata and uncompressed data -/

/-- A step in metadata, against the potential: a byte read for each one skipped, and the potential for the last step. -/
theorem pay_skip {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {D : Dec} {pos : USize} (hrel : DRel D (.skip w st last n)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepDSkip stop D pos).status = .next → Pays a stop (.skip w st last n) D pos (stepDSkip stop D pos) 2 0) ∧
    ((stepDSkip stop D pos).status = .needsInput → Pays a stop (.skip w st last n) D pos (stepDSkip stop D pos) 2 2) ∧
    ((stepDSkip stop D pos).status = .needsOutput → Pays a stop (.skip w st last n) D pos (stepDSkip stop D pos) 2 2) := by
  have hok := stepDSkip_ok (S := specSem) hs hrel hp
  have hR : hdrRate = 22343 := rfl
  have hd : dpot (.skip w st last n) D = 10 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    have hb := sreach_len (hj t)
    rw [hd, hR]
    cases p' with
    | skip w' st' l n' =>
      have hlt : n' < n := hsd
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hne : SPhase.skip w' st' l n' ≠ .skip w st last (m + 1) := fun e => by cases e; omega
      have h8 := sreach_byte (hj t) hne (Or.inl ⟨w, st, last, m, rfl⟩)
      have : dpot (.skip w' st' l n') (stepDSkip stop D pos) = 10 := rfl
      omega
    | mblock w' st' =>
      have := dpot_mblock_le w' st' (stepDSkip stop D pos)
      unfold roundCost at this
      omega
    | ended st' =>
      have : dpot (.ended st') (stepDSkip stop D pos) = 0 := rfl
      omega
    | _ => exact absurd hsd id
  · obtain ⟨b1, b2, p', hR', _, _, hsd, _, hout, hj, _⟩ := hok.needsInput hn
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun t => ?_⟩
    have hb := sreach_len (hj t)
    rw [hd, hR]
    cases p' with
    | skip w' st' l n' =>
      have : dpot (.skip w' st' l n') (stepDSkip stop D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id
  · obtain ⟨p', hR', h1, h2, _, _, hsd, _, hout, hj⟩ := hok.needsOutput hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    have hb := sreach_len (hj t)
    rw [hd, hR]
    cases p' with
    | skip w' st' l n' =>
      have : dpot (.skip w' st' l n') (stepDSkip stop D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id

theorem rawRunW_pos (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    1 ≤ rawRunW a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp := by
  rw [rawRunW]
  split
  · omega
  · dsimp only
    split
    · omega
    · split <;> omega

/-- A step in uncompressed data: ten for each byte it moves into the window, and twelve, with the loop's round. -/
theorem rawW_le {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    stepDRawW a stop hs D pos + 1 ≤ 10 * ((stepDRaw a stop hs D pos).cmd.pend.toNat - D.cmd.pend.toNat) + 12 := by
  unfold stepDRawW stepDRaw
  dsimp only
  by_cases h0 : D.left = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    omega
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hc : winCheck D.k D.cmd.wpos D.cmd.ring = true ∧ pos ≤ stop
    · rw [dite_eq_left hc, dite_eq_left hc]
      by_cases hr : room D.k D.cmd.cap ≤ D.cmd.pend
      · rw [ite_eq_left hr, ite_eq_left hr]
        omega
      · rw [ite_eq_right hr, ite_eq_right hr]
        unfold takeRing rawFinish
        dsimp only
        have hk := winCheck_k hc.1
        have h1 := room_lt hr
        have h2 := room_le (cap := D.cmd.cap) hk
        have h3 : (2 : Nat) ^ D.k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
        have hsub : (room D.k D.cmd.cap - D.cmd.pend).toNat = (room D.k D.cmd.cap).toNat - D.cmd.pend.toNat := room_sub' (by omega)
        have hn : (usmin D.left.toUSize (room D.k D.cmd.cap - D.cmd.pend)).toNat ≤ (room D.k D.cmd.cap).toNat - D.cmd.pend.toNat := by
          rw [usmin_toNat, hsub]
          omega
        generalize usmin D.left.toUSize (room D.k D.cmd.cap - D.cmd.pend) = n at hn ⊢
        have hW := rawRunW_le a stop hs (ringMask D.k) D.k.toNat (winCheck_k hc.1) (ringMask_toNat (winCheck_k hc.1)) _ n
          D.cmd.word D.cmd.count pos D.cmd.ring D.cmd.wpos D.cmd.p1 D.cmd.p2 (USize.le_iff_toNat_le.mp hc.2) (winCheck_size hc.1)
          (winCheck_pos hc.1) rfl
        have hW1 := rawRunW_pos a stop hs (ringMask D.k) D.k.toNat (winCheck_k hc.1) (ringMask_toNat (winCheck_k hc.1)) n
          D.cmd.word D.cmd.count pos D.cmd.ring D.cmd.wpos D.cmd.p1 D.cmd.p2 (USize.le_iff_toNat_le.mp hc.2) (winCheck_size hc.1)
          (winCheck_pos hc.1)
        generalize (rawRun a stop hs (ringMask D.k) D.k.toNat (winCheck_k hc.1) (ringMask_toNat (winCheck_k hc.1)) n
          D.cmd.word D.cmd.count pos D.cmd.ring D.cmd.wpos D.cmd.p1 D.cmd.p2 (USize.le_iff_toNat_le.mp hc.2) (winCheck_size hc.1)
          (winCheck_pos hc.1)).left = left at hW ⊢
        have hl : left.toNat ≤ n.toNat := by omega
        have hm : (n - left).toNat = n.toNat - left.toNat := USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hl)
        show _ + 1 + 1 ≤ 10 * ((D.cmd.pend + (n - left)).toNat - D.cmd.pend.toNat) + 12
        rw [pend_add (by rw [hm]; omega), hm]
        omega
    · rw [dite_eq_right hc, dite_eq_right hc]
      omega

/-- A step in uncompressed data, against the potential: its bytes, a byte read for each, and the potential for the last
step. -/
theorem pay_raw {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}
    {D : Dec} {pos : USize} (hrel : DRel D (.raw w st last n)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepDRaw a stop hs D pos).status = .next → Pays a stop (.raw w st last n) D pos (stepDRaw a stop hs D pos)
      (stepDRawW a stop hs D pos + 1) 0) ∧
    ((stepDRaw a stop hs D pos).status = .needsInput → Pays a stop (.raw w st last n) D pos (stepDRaw a stop hs D pos)
      (stepDRawW a stop hs D pos + 1) 12) ∧
    ((stepDRaw a stop hs D pos).status = .needsOutput → Pays a stop (.raw w st last n) D pos (stepDRaw a stop hs D pos)
      (stepDRawW a stop hs D pos + 1) 12) ∧
    stepDRawW a stop hs D pos + 1 ≤ 12 + 10 * ((stepDRaw a stop hs D pos).cmd.pend.toNat - D.cmd.pend.toNat) := by
  have hok := stepDRaw_ok (S := specSem) (hs := hs) hrel hp
  have hR : hdrRate = 22343 := rfl
  have hd : dpot (.raw w st last n) D = 10 := rfl
  have hW := rawW_le (hs := hs) (D := D) (pos := pos)
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_, by omega⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : p'.out.length - (SPhase.raw w st last n).out.length = l.length := by rw [hl1, List.length_append]; omega
    rw [hl2] at hW
    have hb := sreach_len (hj t)
    rw [hd, hR, hlo]
    cases p' with
    | raw w' st' l' n' =>
      have hlt : n' < n := hsd
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hne : SPhase.raw w' st' l' n' ≠ .raw w st last (m + 1) := fun e => by cases e; omega
      have h8 := sreach_byte (hj t) hne (Or.inr ⟨w, st, last, m, rfl⟩)
      have : dpot (.raw w' st' l' n') (stepDRaw a stop hs D pos) = 10 := rfl
      omega
    | mblock w' st' =>
      have := dpot_mblock_le w' st' (stepDRaw a stop hs D pos)
      unfold roundCost at this
      cases n with
      | zero =>
        have hl0 : D.left = 0 := UInt64.toNat_inj.mp (by rw [hrel.2.2.2.2.1]; rfl)
        have hw2 : stepDRawW a stop hs D pos = 1 := by unfold stepDRawW; rw [ite_eq_left hl0]
        omega
      | succ m =>
        have hne : SPhase.mblock w' st' ≠ .raw w st last (m + 1) := fun e => SPhase.noConfusion e
        have h8 := sreach_byte (hj t) hne (Or.inr ⟨w, st, last, m, rfl⟩)
        omega
    | ended st' =>
      have : dpot (.ended st') (stepDRaw a stop hs D pos) = 0 := rfl
      cases n with
      | zero =>
        have hl0 : D.left = 0 := UInt64.toNat_inj.mp (by rw [hrel.2.2.2.2.1]; rfl)
        have hw2 : stepDRawW a stop hs D pos = 1 := by unfold stepDRawW; rw [ite_eq_left hl0]
        omega
      | succ m =>
        have hne : SPhase.ended st' ≠ .raw w st last (m + 1) := fun e => SPhase.noConfusion e
        have h8 := sreach_byte (hj t) hne (Or.inr ⟨w, st, last, m, rfl⟩)
        omega
    | _ => exact absurd hsd id
  · obtain ⟨b1, b2, p', hR', _, _, hsd, _, hout, hj, _⟩ := hok.needsInput hn
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun t => ?_⟩
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : p'.out.length - (SPhase.raw w st last n).out.length = l.length := by rw [hl1, List.length_append]; omega
    rw [hl2] at hW
    have hb := sreach_len (hj t)
    rw [hd, hR, hlo]
    cases p' with
    | raw w' st' l' n' =>
      have : dpot (.raw w' st' l' n') (stepDRaw a stop hs D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id
  · obtain ⟨p', hR', h1, h2, _, _, hsd, _, hout, hj⟩ := hok.needsOutput hn
    refine ⟨p', hR', hout, h1, h2, fun t => ?_⟩
    obtain ⟨l, hl1, hl2⟩ := hout
    have hlo : p'.out.length - (SPhase.raw w st last n).out.length = l.length := by rw [hl1, List.length_append]; omega
    rw [hl2] at hW
    have hb := sreach_len (hj t)
    rw [hd, hR, hlo]
    cases p' with
    | raw w' st' l' n' =>
      have : dpot (.raw w' st' l' n') (stepDRaw a stop hs D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id

end Brotli.Decoder
