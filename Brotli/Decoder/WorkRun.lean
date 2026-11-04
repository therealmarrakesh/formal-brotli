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
  ∃ q, DRel r q ∧ OutD p q D r ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ (SInv p → SInv q) ∧
    ∀ t : List UInt8, W + dpot q r + hdrRate * (r.bits a r.pos stop (bits t)).length ≤
      dpot p D + hdrRate * (D.bits a pos stop (bits t)).length + 282 * (q.out.length - p.out.length) + extra

theorem sinv_of_sreach {p q : SPhase} {bs c : List Bool} (h : SReach p bs q c) (hi : SInv p) : SInv q := by
  obtain ⟨n, hn⟩ := h.toReach.count
  exact (steps_le hn hi).1

theorem Pays.mono {a : ByteArray} {stop : USize} {p : SPhase} {D : Dec} {pos : USize} {r : Dec} {W e e' : Nat}
    (h : Pays a stop p D pos r W e) (he : e ≤ e') : Pays a stop p D pos r W e' := by
  obtain ⟨q, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨q, h1, h2, h3, h4, h5, fun t => by have := h6 t; omega⟩

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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => sinv_of_sreach (hj []) hi,
      fun t => ?_⟩
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
theorem hpot_start {x y z : UInt64} {g : Gh} {p : HPhase} (h : HRel (hdStart x y z) g p) : hpot g p = 17167 := by
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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => sinv_of_sreach (hj []) hi,
      fun t => ?_⟩
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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
      ⟨[], rfl, rfl⟩, h1, h2, fun hi => sinv_of_sreach (sreach_hdr (q := (g, p)) (q' := (g', p')) (Reach.one (h5 []))) hi,
      fun t => ?_⟩, fun e => DStatus.noConfusion e, fun e => absurd rfl e⟩
    have hpy := hpay hsz (h5 (bits t))
    simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, clearHd]
    omega
  case needsInput =>
    obtain ⟨b1, b2, hR', _, _, _, h6, _⟩ := hstep.needsInput hst
    have hW := stepHW_short (hs := hs) (st := hd) (pos := pos) hst
    rw [ite_eq_right (fun e => HStatus.noConfusion e)]
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨.hdr w st last mlen g p,
      ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0⟩, ⟨[], rfl, rfl⟩,
      by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => hi, fun t => ?_⟩, fun _ => ?_⟩
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
    refine ⟨p', hR'', hout, h1', h2', fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
    have hb := sreach_len (hj t)
    cases p' with
    | cmds w' l' m' cp =>
      have := cpot_le cp
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot] at hb ⊢
      unfold hdrEnd
      rw [hdrRate_eq]
      omega
    | _ => exact absurd hR''.1 (fun e => DTag.noConfusion e)

/-! ### A meta-block's commands -/

theorem avail_len (word count : UInt64) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    (availBits word count a pos stop F).length = (availBits word count a pos stop []).length + F.length := by
  simp only [availBits, List.length_append, List.append_nil]
  omega

/-- The bits from a position hold the chunk's bytes from there. -/
theorem avail_chunk (word count : UInt64) {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) (pos : USize) (F : List Bool) :
    (stop.toNat - pos.toNat) * 8 ≤ (availBits word count a pos stop F).length := by
  simp only [availBits, List.length_append, chunkBits_length hs]
  omega

/-- What the bits from a position pay for covers the chunk's bytes from any later position. -/
theorem rate_chunk (D : Dec) {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {pos r : USize} (hp : pos.toNat ≤ r.toNat)
    (F : List Bool) : hdrRate * ((stop.toNat - r.toNat) * 8) ≤ hdrRate * (D.bits a pos stop F).length :=
  Nat.mul_le_mul_left _ (Nat.le_trans (by omega) (avail_chunk D.word D.count hs pos F))

theorem cpot_end {s : CommandState} (h0 : s.remaining = 0) : cpot (.command s) = 0 := by
  simp [cpot, crank, cstage, h0]

/-- The commands' step, against the potential: the command loop's work is paid for by the commands' potential, their
bits and bytes, and the commands' end by what they hold for it. A loop that runs out of its budget has read or produced
enough to pay for its round. -/
theorem pay_cmds {w : Nat} {last : Bool} {m : MetaBlockHeader} {q0 : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m q0)) (hsi : SInv (.cmds w last m q0))
    (hp : pos.toNat ≤ stop.toNat) :
    ((stepDCmds a stop hs D pos).status = .next → Pays a stop (.cmds w last m q0) D pos (stepDCmds a stop hs D pos)
      (stepDCmdsW a stop hs D pos + 1) 0) ∧
    ((stepDCmds a stop hs D pos).status = .needsInput ∨ (stepDCmds a stop hs D pos).status = .needsOutput →
      Pays a stop (.cmds w last m q0) D pos (stepDCmds a stop hs D pos) (stepDCmdsW a stop hs D pos + 1) 118) ∧
    ((stepDCmds a stop hs D pos).status = .bad → ∃ L, D.cmd.pend.toNat + L ≤ (stepDCmds a stop hs D pos).cmd.pend.toNat ∧
      ∀ t : List UInt8, stepDCmdsW a stop hs D pos + 1 + hdrRate * ((stop.toNat - (stepDCmds a stop hs D pos).pos.toNat) * 8) ≤
        dpot (.cmds w last m q0) D + hdrRate * (D.bits a pos stop (bits t)).length + 282 * L + 118) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  obtain ⟨hm, hci⟩ := hsi
  dsimp only at hR
  obtain ⟨c, q, st', pos'', hq, hciq, o1, l1, g1, g2, hr, g3, g4, gb, g5, g6⟩ :=
    runCmdW_count (w := w) (k := k) (hs := hs) hm hH _ cmdBudget cmd q0 pos rfl hR hci hp []
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hq8 := crank_le q
  have hp8 := crank_le q0
  have hcp := cpot_le q0
  have hb65 : cmdBudget.toNat = 65536 := usize_ofNat' (by decide)
  obtain ⟨l, hl1, hl2⟩ := o1
  have hl2' : st'.pend.toNat = cmd.pend.toNat + l.length := hl2
  have hlo : q.out.length - q0.out.length = l.length := by rw [hl1, List.length_append]; omega
  have hRate : hdrRate = 22343 := rfl
  have eW : stepDCmdsW a stop hs ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ pos =
      runCmdW H k a stop hs cmdBudget cmd pos + (if (runCmd H k a stop hs cmdBudget cmd pos).status = .done then 772 else 0) := rfl
  simp only [stateBits] at g3 c1 c3
  rw [eW]
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmd H k a stop hs cmdBudget cmd pos = rc at g3 g4 gb g5 g6 ⊢
  cases hst : rc.status with
  | next =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    have hc := g6 hst
    have he : cmdEnd st' = 1 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun _ => ?_, fun e => ?_, fun e => ?_⟩
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
      simp only [Dec.bits, Dec.word, Dec.count, clearCmd, dpot, spot, SPhase.out]
      rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate, hlo]
      rw [hlo] at c3
      omega
    · rcases e with e | e <;> cases e
    · cases e
  | needsInput =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    have he : cmdEnd st' = 117 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun e => ?_, fun _ => ?_, fun e => ?_⟩
    · cases e
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
      simp only [Dec.bits, Dec.word, Dec.count, clearCmd, dpot, spot, SPhase.out]
      rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate, hlo]
      omega
    · cases e
  | needsOutput =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    have he : cmdEnd st' = 117 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun e => ?_, fun _ => ?_, fun e => ?_⟩
    · cases e
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
      simp only [Dec.bits, Dec.word, Dec.count, clearCmd, dpot, spot, SPhase.out]
      rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate, hlo]
      omega
    · cases e
  | bad =>
    have he : cmdEnd rc = 117 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    obtain ⟨⟨-, -, e3⟩, hpr⟩ := gb hst
    have hch := avail_chunk st'.word st'.count hs pos'' []
    refine ⟨fun e => ?_, fun e => ?_, fun _ => ⟨l.length, ?_, fun t => ?_⟩⟩
    · cases e
    · rcases e with e | e <;> cases e
    · show _ ≤ rc.pend.toNat
      rw [e3]
      omega
    · show _ + 1 + hdrRate * ((stop.toNat - rc.pos.toNat) * 8) ≤ _
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot]
      rw [avail_len cmd.word cmd.count a pos stop (bits t), hRate]
      rw [hlo] at g3
      omega
  | done =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    obtain ⟨s, rfl, h0⟩ := g5 hst
    have he : cmdEnd st' = 117 := by unfold cmdEnd; rw [hst]; rfl
    rw [he, cpot_end h0] at g3
    rw [ite_eq_left rfl]
    have hcheck := seenOk_iff hH hq
    have hq' := hq
    obtain ⟨hC, htg, hprod⟩ := hq'
    have hwin := hC.toWin
    by_cases hsee : seenOk st'.seen H.nL H.nI H.nD = true
    · rw [ite_eq_left hsee]
      refine ⟨fun _ => ?_, fun e => ?_, fun e => ?_⟩
      rotate_left
      · rcases e with e | e <;> cases e
      · cases e
      cases last' with
      | true =>
        refine ⟨.ended ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, w, ⟨hwin, hprod, hlim⟩⟩, ⟨l, hl1, hl2⟩, g1, g2,
          fun _ => trivial, fun t => ?_⟩
        simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, SPhase.out, ↓reduceIte]
        rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate]
        have hlo' : s.output.length - q0.out.length = l.length := hlo
        try rw [hlo] at g3
        rw [hlo']
        unfold cmdsEnd roundCost
        omega
      | false =>
        refine ⟨.mblock w ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, ⟨hwin, hprod, hlim⟩⟩, ⟨l, hl1, hl2⟩, g1, g2,
          fun _ => hciq, fun t => ?_⟩
        simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, SPhase.out, Bool.false_eq_true, ↓reduceIte]
        rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate]
        have hlo' : s.output.length - q0.out.length = l.length := hlo
        try rw [hlo] at g3
        rw [hlo']
        unfold cmdsEnd roundCost
        split <;> omega
    · rw [ite_eq_right hsee]
      refine ⟨fun e => ?_, fun e => ?_, fun _ => ⟨l.length, ?_, fun t => ?_⟩⟩
      · cases e
      · rcases e with e | e <;> cases e
      · show _ ≤ st'.pend.toNat
        omega
      have hch := avail_chunk st'.word st'.count hs st'.pos []
      show _ + 1 + hdrRate * ((stop.toNat - st'.pos.toNat) * 8) ≤ _
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot]
      rw [avail_len cmd.word cmd.count a pos stop (bits t), hRate]
      rw [hlo] at g3
      unfold cmdsEnd roundCost
      omega

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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => sinv_of_sreach (hj []) hi,
      fun t => ?_⟩
    have hb := sreach_len (hj t)
    rw [hd, hR]
    cases p' with
    | skip w' st' l n' =>
      have : dpot (.skip w' st' l n') (stepDSkip stop D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id
  · obtain ⟨p', hR', h1, h2, _, _, hsd, _, hout, hj⟩ := hok.needsOutput hn
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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
    refine ⟨p', hR', hout, by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => sinv_of_sreach (hj []) hi,
      fun t => ?_⟩
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
    refine ⟨p', hR', hout, h1, h2, fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
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

/-! ### A step of the stream -/

/-- Only WBITS's step sets the window's size. -/
theorem stepD_k {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} (h : D.tag ≠ .wbits) :
    (stepD a stop hs D).k = D.k := by
  unfold stepD
  cases ht : D.tag <;> dsimp only
  · exact absurd ht h
  · unfold stepDMeta metaGo
    repeat' (first | split_all | rfl)
  · unfold stepDSkip moveOn
    repeat' (first | split_all | rfl)
  · unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | rfl)
  · unfold stepDHdr takeHd clearHd
    dsimp only
    repeat' (first | split_all | rfl)
  · unfold stepDCmds takeCmd clearCmd
    dsimp only
    repeat' (first | split_all | rfl)

/-- What a step that pauses costs beyond the potential: a meta-block's start that waits for output space the least, any
other wait for output space at most the command loop's stopping round and its round, and a wait for input at most a
header's step that runs out of input. -/
def stopCost (r : Dec) : Nat := if r.status = .needsOutput then (if r.tag = .mblock then 2 else 118) else 269

theorem stopCost_ge (r : Dec) : 2 ≤ stopCost r := by
  unfold stopCost
  split
  · split <;> omega
  · omega

theorem stepDCmds_out_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (ht : D.tag = .cmds) :
    (stepDCmds a stop hs D pos).status = .needsOutput → (stepDCmds a stop hs D pos).tag = .cmds := by
  unfold stepDCmds takeCmd clearCmd
  dsimp only
  repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) | (intro _; exact ht))

theorem stopCost_in {r : Dec} (h : r.status = .needsInput) : stopCost r = 269 := by
  unfold stopCost
  rw [ite_eq_right (by rw [h]; exact fun e => DStatus.noConfusion e)]

theorem stopCost_out {r : Dec} (h : r.status = .needsOutput) (ht : r.tag ≠ .mblock) : stopCost r = 118 := by
  unfold stopCost
  rw [ite_eq_left h, ite_eq_right ht]

/-- No step goes back to WBITS. -/
theorem stepD_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} (h : D.tag ≠ .wbits) :
    (stepD a stop hs D).tag ≠ .wbits := by
  unfold stepD
  cases ht : D.tag <;> dsimp only
  · exact absurd ht h
  · unfold stepDMeta metaGo
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · unfold stepDSkip moveOn
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · unfold stepDHdr takeHd clearHd
    dsimp only
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · unfold stepDCmds takeCmd clearCmd
    dsimp only
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [ht]
    exact fun e => DTag.noConfusion e

/-- WBITS's step that goes on leaves WBITS. -/
theorem stepDWbits_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDWbits a stop hs D pos).status = .next → (stepDWbits a stop hs D pos).tag ≠ .wbits := by
  unfold stepDWbits
  repeat' (first | split_all | (intro _; exact fun e => DTag.noConfusion e) | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- After WBITS, the loop keeps the window's size. -/
theorem runD_wk {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ x : RunArg a stop hs, x.D.tag ≠ .wbits → (runD a stop hs x.D x.inv).tag ≠ .wbits ∧ (runD a stop hs x.D x.inv).k = x.D.k := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    intro h
    dsimp only at ih h ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact ⟨h, rfl⟩
    · rw [dite_eq_right he]
      dsimp only
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        obtain ⟨i1, i2⟩ := ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ (stepD_tag h)
        exact ⟨i1, i2.trans (stepD_k h)⟩
      · rw [dite_eq_right hn]
        exact ⟨stepD_tag h, stepD_k h⟩

/-- WBITS's step, when it reports the limit, leaves the bytes waiting as they were. -/
theorem stepDWbits_memPend {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDWbits a stop hs D pos).status = .memory → (stepDWbits a stop hs D pos).cmd.pend = D.cmd.pend := by
  unfold stepDWbits winStart
  repeat' (first | split_all | (intro _; rfl) | (intro _; trivial) | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- A header's step, when it reports the limit, leaves the bytes waiting as they were. -/
theorem stepDHdr_memPend {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDHdr a stop hs D pos).status = .memory → (stepDHdr a stop hs D pos).cmd.pend = D.cmd.pend := by
  unfold stepDHdr takeHd clearHd cmdStart
  dsimp only
  repeat' (first | split_all | (intro _; rfl) | (intro _; trivial) | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- A stream step, against the potential: one that goes on is paid for, with the window when it is WBITS's; one that
pauses costs at most 269 more; one that rejects or reports the limit costs at most the potential, the bits, the bytes it
decodes first, which are waiting after it, and 23750. -/
theorem pay_stepD {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} (hrel : DRel D p)
    (hsi : SInv p) (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) :
    ((stepD a stop hs D).status = .next → Pays a stop p D D.pos (stepD a stop hs D) (stepDW a stop hs D + 1)
      (if D.tag = .wbits then 5 * 2 ^ (stepD a stop hs D).k.toNat else 0)) ∧
    ((stepD a stop hs D).status = .needsInput ∨ (stepD a stop hs D).status = .needsOutput →
      Pays a stop p D D.pos (stepD a stop hs D) (stepDW a stop hs D + 1) (stopCost (stepD a stop hs D))) ∧
    ((stepD a stop hs D).status = .bad ∨ (stepD a stop hs D).status = .memory → ∃ L,
      D.cmd.pend.toNat + L ≤ (stepD a stop hs D).cmd.pend.toNat ∧
      ((stepD a stop hs D).status = .memory → (stepD a stop hs D).cmd.pend.toNat = 0) ∧ ∀ t : List UInt8,
      stepDW a stop hs D + 1 + hdrRate * ((stop.toNat - (stepD a stop hs D).pos.toNat) * 8) ≤
        dpot p D + hdrRate * (D.bits a D.pos stop (bits t)).length + 282 * L + 23750) := by
  have hok := stepD_ok specSem (hs := hs) hrel he hp
  have hpl := stepD_pendLe a stop hs D
  have hmem : (stepD a stop hs D).status = .memory → p = .wbits ∨ ∃ w st last mlen g q, p = .hdr w st last mlen g q :=
    fun h => (hok.memory h).2.2.2.2
  have hpos : (stepD a stop hs D).status = .bad ∨ (stepD a stop hs D).status = .memory →
      D.pos.toNat ≤ (stepD a stop hs D).pos.toNat := by
    intro h
    rcases h with h | h
    · obtain ⟨_, _, _, d1, d2, _⟩ := (hok.bad h).2
      omega
    · exact (hok.memory h).1
  cases p with
  | wbits =>
    have e1 : stepD a stop hs D = stepDWbits a stop hs D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = stepDWbitsW a stop hs D D.pos := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_left hrel.1]
    rw [e1] at hok hpos
    obtain ⟨n1, n2, n3⟩ := pay_wbits (hs := hs) hrel hp
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (by rw [stopCost_in h]; omega)
      · obtain ⟨p', _, _, _, _, hne0, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | wbits =>
          have e : (stepDWbits a stop hs D D.pos).cmd.pend = D.cmd.pend := hsd
          rw [e, hrel.2.2.2] at hne0
          exact absurd rfl hne0
        | _ => exact absurd hsd id
    · have := n3 (by rcases h with h | h <;> rw [h] <;> exact fun e => DStatus.noConfusion e)
      have h0 : D.cmd.pend.toNat = 0 := by rw [hrel.2.2.2]; rfl
      exact ⟨0, by omega, fun hm => by rw [stepDWbits_memPend hm]; exact h0,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); omega⟩
  | mblock w st =>
    have e1 : stepD a stop hs D = stepDMeta a stop hs D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = stepDMetaW a stop hs D D.pos := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_right (by rw [hrel.1]; exact fun e => DTag.noConfusion e)]
    obtain ⟨n1, n2, n3, n4⟩ := pay_mblock (hs := hs) hrel hp
    rw [e1] at hok hpos
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    rotate_left
    · rcases h with h | h
      · have e3 := congrArg USize.toNat (stepDMeta_badWin h).1.2.2
        exact ⟨0, by omega, fun h' => absurd (h'.symm.trans h) (fun e => DStatus.noConfusion e),
          fun t => by have := rate_chunk D hs (hpos (Or.inl h)) (bits t); omega⟩
      · rcases hmem (by rw [e1]; exact h) with h' | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
    rcases h with h | h
    · exact (n2 h).mono (by rw [stopCost_in h]; omega)
    · have ht : (stepDMeta a stop hs D D.pos).tag = .mblock := by
        obtain ⟨p', hR', _, _, _, _, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | mblock => exact hR'.1
        | _ => exact absurd hsd id
      have hsc : stopCost (stepDMeta a stop hs D D.pos) = 2 := by
        unfold stopCost
        rw [ite_eq_left h, ite_eq_left ht]
      exact (n3 h).mono (Nat.le_of_eq hsc.symm)
  | skip w st last n =>
    have e1 : stepD a stop hs D = stepDSkip stop D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = 1 := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_right (by rw [hrel.1]; exact fun e => DTag.noConfusion e)]
    obtain ⟨n1, n2, n3⟩ := pay_skip (a := a) (hs := hs) hrel hp
    rw [e1] at hpos
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    rotate_left
    · rcases h with h | h
      · have e3 := congrArg USize.toNat (stepDSkip_badWin h).1.2.2
        exact ⟨0, by omega, fun h' => absurd (h'.symm.trans h) (fun e => DStatus.noConfusion e),
          fun t => by have := rate_chunk D hs (hpos (Or.inl h)) (bits t); omega⟩
      · rcases hmem (by rw [e1]; exact h) with h' | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
    rcases h with h | h
    · exact (n2 h).mono (stopCost_ge _)
    · exact (n3 h).mono (stopCost_ge _)
  | raw w st last n =>
    have e1 : stepD a stop hs D = stepDRaw a stop hs D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = stepDRawW a stop hs D D.pos := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_right (by rw [hrel.1]; exact fun e => DTag.noConfusion e)]
    rw [e1] at hpl hok hpos
    obtain ⟨n1, n2, n3, n4⟩ := pay_raw (hs := hs) hrel hp
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (by rw [stopCost_in h]; omega)
      · have ht : (stepDRaw a stop hs D D.pos).tag ≠ .mblock := by
          obtain ⟨p', hR', _, _, _, _, hsd, _⟩ := hok.needsOutput h
          cases p' with
          | raw => rw [hR'.1]; exact fun e => DTag.noConfusion e
          | _ => exact absurd hsd id
        exact (n3 h).mono (by rw [stopCost_out h ht]; omega)
    · have := hpl.2
      have hle : D.cmd.pend.toNat ≤ (stepDRaw a stop hs D D.pos).cmd.pend.toNat := by
        rcases h with h | h
        · exact Nat.le_of_eq (congrArg USize.toNat (stepDRaw_badWin h).1.2.2).symm
        · rcases hmem (by rw [e1]; exact h) with h' | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
      refine ⟨(stepDRaw a stop hs D D.pos).cmd.pend.toNat - D.cmd.pend.toNat, by omega, fun hm => ?_,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); omega⟩
      rcases hmem (by rw [e1]; exact hm) with h' | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
  | hdr w st last mlen g q =>
    have e1 : stepD a stop hs D = stepDHdr a stop hs D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = stepDHdrW a stop hs D D.pos := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_right (by rw [hrel.1]; exact fun e => DTag.noConfusion e)]
    rw [e1] at hok hpos
    obtain ⟨n1, n2, n3⟩ := pay_hdr (hs := hs) hrel hp
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (Nat.le_of_eq (stopCost_in h).symm)
      · obtain ⟨p', _, _, _, _, hne0, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | hdr w' st' l' ml' g' q' =>
          have e : (stepDHdr a stop hs D D.pos).cmd.pend = D.cmd.pend := hsd.2
          rw [e, hrel.2.2.2.2.2.2.2] at hne0
          exact absurd rfl hne0
        | _ => exact absurd hsd id
    · have := n3 (by rcases h with h | h <;> rw [h] <;> exact fun e => DStatus.noConfusion e)
      have hd : dpot (.hdr w st last mlen g q) D = hpot g q + hdrEnd := rfl
      have hS : hdrSlack = 23750 := rfl
      have h0 : D.cmd.pend.toNat = 0 := by rw [hrel.2.2.2.2.2.2.2]; rfl
      exact ⟨0, by omega, fun hm => by rw [stepDHdr_memPend hm]; exact h0,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); omega⟩
  | cmds w last m q =>
    have e1 : stepD a stop hs D = stepDCmds a stop hs D D.pos := by unfold stepD; rw [hrel.1]
    have e2 : stepDW a stop hs D = stepDCmdsW a stop hs D D.pos := by unfold stepDW; rw [hrel.1]
    rw [e1, e2, ite_eq_right (by rw [hrel.1]; exact fun e => DTag.noConfusion e)]
    obtain ⟨n1, n2, n3⟩ := pay_cmds (hs := hs) hrel hsi hp
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    · rcases h with h' | h'
      · exact (n2 (Or.inl h')).mono (by rw [stopCost_in h']; omega)
      · have ht : (stepDCmds a stop hs D D.pos).tag ≠ .mblock := by
          rw [stepDCmds_out_tag hrel.1 h']
          exact fun e => DTag.noConfusion e
        exact (n2 (Or.inr h')).mono (Nat.le_of_eq (stopCost_out h' ht).symm)
    rcases h with h | h
    · obtain ⟨L, hL, hb⟩ := n3 h
      exact ⟨L, hL, fun hm => absurd (hm.symm.trans h) (fun e => DStatus.noConfusion e), fun t => by have := hb t; omega⟩
    · rcases hmem (by rw [e1]; exact h) with h' | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
  | ended st => exact absurd hrel.1 he

/-! ### Handing bytes out -/

/-- A round of handing bytes out: it hands out what waits, what the space takes, or the bytes up to the window's end,
whichever is fewest, and keeps everything else. -/
theorem flushCmd_st {k : USize} {st : Cmd} {buf : ByteArray} {sp : USize} (hk : k.toNat ≤ 24) (hplt : st.wpos.toNat < 2 ^ k.toNat)
    (hle : st.pend.toNat ≤ 2 ^ k.toNat) (hp0 : st.pend.toNat ≠ 0) (hs0 : sp.toNat ≠ 0) :
    (flushCmd k st buf sp).st = { st with pend := (flushCmd k st buf sp).st.pend } ∧
    (flushCmd k st buf sp).st.pend.toNat = st.pend.toNat -
      min (min st.pend.toNat sp.toNat) (2 ^ k.toNat - ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat) := by
  unfold flushCmd
  have hz : ¬ (st.pend = 0 ∨ sp = 0) := fun h => h.elim (fun e => hp0 (by rw [e]; rfl)) (fun e => hs0 (by rw [e]; rfl))
  rw [ite_eq_right hz]
  dsimp only
  have hback : (ringBack st.wpos st.pend (ringMask k) (ringSize k)).toNat = ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat :=
    ringBack_toNat hk (ringMask_toNat hk) (ringSize_toNat hk) hplt (by omega) hle
  have hstart : ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat < 2 ^ k.toNat := by
    unfold ringStart
    exact ringIdx_lt hplt (by omega)
  have hroom : (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k)).toNat =
      2 ^ k.toNat - ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hback, ringSize_toNat hk]; omega)), hback, ringSize_toNat hk]
  have hlenN : (usmin (usmin st.pend sp) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat =
      min (min st.pend.toNat sp.toNat) (2 ^ k.toNat - ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat) := by
    rw [usmin_toNat, usmin_toNat, hroom]
  have hpn : (st.pend - usmin (usmin st.pend sp) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat =
      st.pend.toNat - (usmin (usmin st.pend sp) (ringSize k - ringBack st.wpos st.pend (ringMask k) (ringSize k))).toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hlenN]; omega))
  exact ⟨rfl, by rw [hpn, hlenN]⟩

/-- Handing bytes out takes at most three rounds: one up to the window's end, one from its start, and the one that finds
nothing left to do. Its work is the bytes it hands out, and five. -/
theorem flushAllW_le {k : USize} (hk : k.toNat ≤ 24) (st : Cmd) (buf : ByteArray) (space : Nat)
    (hplt : st.wpos.toNat < 2 ^ k.toNat) (hle : st.pend.toNat ≤ 2 ^ k.toNat) :
    flushAllW k st buf space ≤ min st.pend.toNat space + 5 := by
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  rw [flushAllW]
  dsimp only
  by_cases hz : st.pend = 0 ∨ space = 0
  · rw [ite_eq_left hz]
    omega
  rw [ite_eq_right hz]
  have hp0 : st.pend.toNat ≠ 0 := fun e => hz (Or.inl (USize.toNat_inj.mp (by rw [e]; rfl)))
  have hs0 : space ≠ 0 := fun e => hz (Or.inr e)
  have hsp : (USize.ofNat (min space 16777216)).toNat = min space 16777216 := usize_ofNat' (by omega)
  obtain ⟨e1, e2⟩ := flushCmd_st (buf := buf) (sp := USize.ofNat (min space 16777216)) hk hplt hle hp0 (by rw [hsp]; omega)
  rw [hsp] at e2
  have hsdef : ringStart (2 ^ k.toNat) st.wpos.toNat st.pend.toNat = if st.pend.toNat - 1 < st.wpos.toNat then
      st.wpos.toNat - 1 - (st.pend.toNat - 1) else st.wpos.toNat + 2 ^ k.toNat - 1 - (st.pend.toNat - 1) := rfl
  generalize hr : flushCmd k st buf (USize.ofNat (min space 16777216)) = r at e1 e2 ⊢
  have hlt : r.st.pend < st.pend := USize.lt_iff_toNat_lt.mpr (by split at hsdef <;> omega)
  rw [dite_eq_left hlt]
  have hsub : (st.pend - r.st.pend).toNat = st.pend.toNat - r.st.pend.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))
  rw [hsub, flushAllW]
  dsimp only
  by_cases hz2 : r.st.pend = 0 ∨ space - (st.pend.toNat - r.st.pend.toNat) = 0
  · rw [ite_eq_left hz2]
    split at hsdef <;> omega
  rw [ite_eq_right hz2]
  have hq0 : r.st.pend.toNat ≠ 0 := fun e => hz2 (Or.inl (USize.toNat_inj.mp (by rw [e]; rfl)))
  have hq1 : space - (st.pend.toNat - r.st.pend.toNat) ≠ 0 := fun e => hz2 (Or.inr e)
  have hw1 : r.st.wpos = st.wpos := by rw [e1]
  -- The first round stopped at the window's end: what is left starts at the window's start.
  have hwrap : r.st.pend.toNat = st.wpos.toNat := by split at hsdef <;> omega
  have hs1 : ringStart (2 ^ k.toNat) r.st.wpos.toNat r.st.pend.toNat = 0 := by
    rw [hw1, hwrap]
    show (if st.wpos.toNat - 1 < st.wpos.toNat then st.wpos.toNat - 1 - (st.wpos.toNat - 1) else _) = 0
    rw [ite_eq_left (by omega)]
    omega
  have hsp2 : (USize.ofNat (min (space - (st.pend.toNat - r.st.pend.toNat)) 16777216)).toNat =
      min (space - (st.pend.toNat - r.st.pend.toNat)) 16777216 := usize_ofNat' (by omega)
  obtain ⟨-, f2⟩ := flushCmd_st (buf := r.buf) (sp := USize.ofNat (min (space - (st.pend.toNat - r.st.pend.toNat)) 16777216)) hk
    (by rw [hw1]; exact hplt) (by omega) hq0 (by rw [hsp2]; omega)
  rw [hsp2, hs1] at f2
  generalize flushCmd k r.st r.buf (USize.ofNat (min (space - (st.pend.toNat - r.st.pend.toNat)) 16777216)) = r2 at f2 ⊢
  have hlt2 : r2.st.pend < r.st.pend := USize.lt_iff_toNat_lt.mpr (by omega)
  rw [dite_eq_left hlt2]
  have hsub2 : (r.st.pend - r2.st.pend).toNat = r.st.pend.toNat - r2.st.pend.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))
  rw [hsub2, flushAllW]
  dsimp only
  have hz3 : r2.st.pend = 0 ∨ space - (st.pend.toNat - r.st.pend.toNat) - (r.st.pend.toNat - r2.st.pend.toNat) = 0 := by
    by_cases hh : r2.st.pend.toNat = 0
    · exact Or.inl (USize.toNat_inj.mp (by rw [hh]; rfl))
    · right
      omega
  rw [ite_eq_left hz3]
  omega

/-! ### Pausing for output space -/

/-- A step that pauses for output space anywhere but at a meta-block's start has no room left. -/
theorem stepD_room {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} (he : D.tag ≠ .ended) :
    (stepD a stop hs D).status = .needsOutput → (stepD a stop hs D).tag ≠ .mblock →
      room (stepD a stop hs D).k (stepD a stop hs D).cmd.cap ≤ (stepD a stop hs D).cmd.pend := by
  unfold stepD
  cases ht : D.tag <;> dsimp only
  · unfold stepDWbits
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · unfold stepDMeta metaGo
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) |
      (intro _ h2; exact absurd ht h2))
  · unfold stepDSkip moveOn
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) | (intro _ _; assumption))
  · unfold stepDHdr takeHd clearHd
    dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · unfold stepDCmds takeCmd clearCmd
    dsimp only
    have hf := runCmd_full (H := D.H) (k := D.k) (a := a) (hs := hs) _ cmdBudget D.cmd D.pos rfl
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) |
      (intro _ _; exact hf (by assumption)))
  · exact absurd ht he

/-- The loop pauses for output space anywhere but at a meta-block's start only with no room left. -/
theorem runD_room {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ x : RunArg a stop hs, (runD a stop hs x.D x.inv).status = .needsOutput → (runD a stop hs x.D x.inv).tag ≠ .mblock →
      room (runD a stop hs x.D x.inv).k (runD a stop hs x.D x.inv).cmd.cap ≤ (runD a stop hs x.D x.inv).cmd.pend := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    dsimp only at ih ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      intro h
      cases h
    · rw [dite_eq_right he]
      dsimp only
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        exact ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩
      · rw [dite_eq_right hn]
        exact stepD_room he

/-- WBITS's step that goes on sets a window of at least 2¹⁰ bytes. -/
theorem stepDWbits_k {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf) (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status = .next) :
    10 ≤ (stepDWbits a stop hs D pos).k.toNat := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepDWbits at hn ⊢
  rw [dite_eq_left hp'] at hn ⊢
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
      rw [ite_eq_left hl]
      show 10 ≤ (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toUSize.toNat
      have ha2' : (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
          (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat ≤ 24 := ha2
      have ha1' : 10 ≤ (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
          (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat := ha1
      rw [word_toUSize (by omega)]
      exact ha1'
    · exact absurd hn (fun e => DStatus.noConfusion e)

/-- Handing out the bytes of a state that can hand them out: its work is the bytes it hands out, and five. -/
theorem flushW_win {D : Dec} (h : WinOk D) (buf : ByteArray) (space : Nat) :
    flushAllW D.k D.cmd buf space ≤ min D.cmd.pend.toNat space + 5 := by
  rcases h with h0 | ⟨_, hr, hl, -, hk⟩
  · rw [flushAllW]
    dsimp only
    rw [ite_eq_left (Or.inl h0)]
    omega
  · exact flushAllW_le hk _ _ _ hr.pos_lt hl

/-- Handing out a state's bytes: its work is the bytes it hands out, and five. -/
theorem flushW_le {D : Dec} {p : SPhase} (h : DRel D p) (buf : ByteArray) (space : Nat) :
    flushAllW D.k D.cmd buf space ≤ min D.cmd.pend.toNat space + 5 :=
  flushW_win h.winOk buf space

/-- The cap a round gives the bytes waiting: one more than its space, at most 2²⁴ + 1. -/
theorem capE_capFor (space : Nat) : capE (capFor space) = min space 16777216 + 1 := by
  unfold capE capFor
  rw [usize_ofNat' (by omega)]
  omega

/-- Fewer bytes waiting raises no place's potential. -/
theorem dpot_mono (q : SPhase) {D D' : Dec} (h : D'.cmd.pend.toNat ≤ D.cmd.pend.toNat) : dpot q D' ≤ dpot q D := by
  unfold dpot
  cases q with
  | mblock w st =>
    dsimp only
    by_cases h1 : D'.cmd.pend = 0
    · rw [ite_eq_left h1]
      omega
    · have h2 : D.cmd.pend ≠ 0 := by
        intro e
        apply h1
        apply USize.toNat_inj.mp
        have : D.cmd.pend.toNat = 0 := by rw [e]; rfl
        show D'.cmd.pend.toNat = (0 : USize).toNat
        rw [show (0 : USize).toNat = 0 from rfl]
        omega
      rw [ite_eq_right h1, ite_eq_right h2]
      exact Nat.le_refl _
  | _ => exact Nat.le_refl _

theorem stepDWbits_out {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDWbits a stop hs D pos).status ≠ .needsOutput := by
  unfold stepDWbits
  repeat' (first | split_all | exact fun e => DStatus.noConfusion e)

/-- A loop that pauses for output space has a window of at least 2¹⁰ bytes. -/
theorem runD_k10 {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} (x : RunArg a stop hs) {p : SPhase} (hrel : DRel x.D p)
    (hk : x.D.tag ≠ .wbits → 10 ≤ x.D.k.toNat) (hn : (runD a stop hs x.D x.inv).status = .needsOutput) :
    10 ≤ (runD a stop hs x.D x.inv).k.toNat := by
  obtain ⟨D, hinv⟩ := x
  dsimp only at hrel hk hn ⊢
  by_cases hw : D.tag = .wbits
  · have he : D.tag ≠ .ended := by rw [hw]; exact fun e => DTag.noConfusion e
    have e : stepD a stop hs D = stepDWbits a stop hs D D.pos := by unfold stepD; rw [hw]
    rw [runD, dite_eq_right he] at hn ⊢
    dsimp only at hn ⊢
    by_cases h1 : (stepD a stop hs D).status = .next
    · rw [dite_eq_left h1] at hn ⊢
      have hw' : DRel D .wbits := by cases p <;> first | exact hrel | exact absurd hw (by rw [hrel.1]; exact fun e => DTag.noConfusion e)
      have ht1 : (stepD a stop hs D).tag ≠ .wbits := by rw [e]; exact stepDWbits_tag (by rw [← e]; exact h1)
      have hk1 : 10 ≤ (stepD a stop hs D).k.toNat := by
        rw [e]
        exact stepDWbits_k hw'.2.1 hinv.2 (by rw [← e]; exact h1)
      rw [(runD_wk ⟨_, hinv.step he h1⟩ ht1).2]
      exact hk1
    · rw [dite_eq_right h1] at hn
      rw [e] at hn
      exact absurd hn stepDWbits_out
  · rw [(runD_wk ⟨D, hinv⟩ hw).2]
    exact hk hw

/-! ### The decoder's loop -/

/-- The window a run of the loop allocates: WBITS's, when it starts there and gets past it. -/
def winD (D r : Dec) : Nat := if D.tag = .wbits ∧ r.tag ≠ .wbits then 5 * 2 ^ r.k.toNat else 0

/-- The decoder's loop, against the potential: its steps are paid for by the potential, 22343 for each bit, 282 for each
byte and the window, and the step that stops it by at most 270 more, or, when it rejects or reports the limit, by the bits
and the bytes it may decode first, and 23751. -/
theorem pay_runD {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} : ∀ (x : RunArg a stop hs) (p : SPhase),
    DRel x.D p → SInv p →
    ((runD a stop hs x.D x.inv).status = .next ∨ (runD a stop hs x.D x.inv).status = .needsInput ∨
        (runD a stop hs x.D x.inv).status = .needsOutput →
      Pays a stop p x.D x.D.pos (runD a stop hs x.D x.inv) (runDW a stop hs x.D x.inv)
        (winD x.D (runD a stop hs x.D x.inv) + stopCost (runD a stop hs x.D x.inv))) ∧
    ((runD a stop hs x.D x.inv).status = .bad ∨ (runD a stop hs x.D x.inv).status = .memory → ∃ L,
      x.D.cmd.pend.toNat + L ≤ (runD a stop hs x.D x.inv).cmd.pend.toNat ∧
      ((runD a stop hs x.D x.inv).status = .memory → (runD a stop hs x.D x.inv).cmd.pend.toNat = 0) ∧ ∀ t : List UInt8,
      runDW a stop hs x.D x.inv + hdrRate * ((stop.toNat - (runD a stop hs x.D x.inv).pos.toNat) * 8) ≤
        dpot p x.D + hdrRate * (x.D.bits a x.D.pos stop (bits t)).length + 282 * L + winD x.D (runD a stop hs x.D x.inv) + 23751) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    intro p hrel hsi
    dsimp only at ih hrel ⊢
    rw [runDW, runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he, dite_eq_left he]
      have e1 : dpot p { D with status := .next } = dpot p D := rfl
      have e2 : ∀ t : List UInt8, ({ D with status := .next } : Dec).bits a D.pos stop (bits t) = D.bits a D.pos stop (bits t) :=
        fun _ => rfl
      refine ⟨fun _ => ⟨p, hrel.congr rfl rfl rfl rfl rfl rfl rfl rfl, ⟨[], rfl, rfl⟩, Nat.le_refl _, hinv.2, id, fun t => ?_⟩,
        fun h => ?_⟩
      · rw [e1, e2]
        have := stopCost_ge { D with status := .next }
        omega
      · rcases h with h | h <;> cases h
    · rw [dite_eq_right he, dite_eq_right he]
      dsimp only
      obtain ⟨s1, s2, s3⟩ := pay_stepD (hs := hs) hrel hsi he hinv.2
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn, dite_eq_left hn]
        obtain ⟨q1, hR1, ho1, hp1, hp2, hsi1, hw1⟩ := s1 hn
        obtain ⟨i1, i2⟩ := ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ q1 hR1 (hsi1 hsi)
        dsimp only at i1 i2
        have hwin : (if D.tag = .wbits then 5 * 2 ^ (stepD a stop hs D).k.toNat else 0) +
            winD (stepD a stop hs D) (runD a stop hs (stepD a stop hs D) (hinv.step he hn)) ≤
            winD D (runD a stop hs (stepD a stop hs D) (hinv.step he hn)) := by
          by_cases hw : D.tag = .wbits
          · have e : stepD a stop hs D = stepDWbits a stop hs D D.pos := by unfold stepD; rw [hw]
            have ht1 : (stepD a stop hs D).tag ≠ .wbits := by
              rw [e]
              exact stepDWbits_tag (by rw [← e]; exact hn)
            obtain ⟨ht2, hk⟩ := runD_wk ⟨_, hinv.step he hn⟩ ht1
            dsimp only at hk ht2
            unfold winD
            rw [ite_eq_left hw, ite_eq_right (fun h => ht1 h.1), ite_eq_left ⟨hw, ht2⟩, hk]
            omega
          · have ht1 := stepD_tag (hs := hs) hw
            unfold winD
            rw [ite_eq_right hw, ite_eq_right (fun h => ht1 h.1), ite_eq_right (fun h => hw h.1)]
            exact Nat.le_refl _
        obtain ⟨l1, hl1, hl1'⟩ := ho1
        have o1 : q1.out.length = l1.length + p.out.length := by rw [hl1, List.length_append]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨q, hR, ho, hq1, hq2, hsiq, hw⟩ := i1 h
          obtain ⟨l2, hl2, hl2'⟩ := ho
          refine ⟨q, hR, ⟨l2 ++ l1, by rw [hl2, hl1, List.append_assoc], by rw [hl2', hl1', List.length_append]; omega⟩,
            by omega, hq2, fun h => hsiq (hsi1 h), fun t => ?_⟩
          have a1 := hw1 t
          have a2 := hw t
          have o2 : q.out.length = l2.length + q1.out.length := by rw [hl2, List.length_append]
          omega
        · obtain ⟨L, hL, hm, hb⟩ := i2 h
          have hl1'' : (stepD a stop hs D).cmd.pend.toNat = D.cmd.pend.toNat + l1.length := hl1'
          refine ⟨l1.length + L, by omega, hm, fun t => ?_⟩
          have a1 := hw1 t
          have a2 := hb t
          omega
      · rw [dite_eq_right hn, dite_eq_right hn]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rcases h with h | h | h
          · exact absurd h hn
          · exact (s2 (Or.inl h)).mono (Nat.le_add_left _ _)
          · exact (s2 (Or.inr h)).mono (Nat.le_add_left _ _)
        · obtain ⟨L, hL, hm, hb⟩ := s3 h
          exact ⟨L, hL, hm, fun t => by have := hb t; omega⟩

/-- The loop goes on to its end only at the stream's end. -/
theorem runD_next {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ x : RunArg a stop hs, (runD a stop hs x.D x.inv).status = .next → (runD a stop hs x.D x.inv).tag = .ended := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    dsimp only at ih ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      intro _
      exact he
    · rw [dite_eq_right he]
      dsimp only
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        exact ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩
      · rw [dite_eq_right hn]
        exact fun h => absurd h hn

/-- A round that pauses for output space with no room left, and hands all its bytes out within its space, hands out a
whole window. -/
theorem room_full {k cap pend : USize} {space : Nat} (hk : k.toNat ≤ 24) (hc : cap = capFor space) (hr : room k cap ≤ pend)
    (hs : pend.toNat ≤ space) : 2 ^ k.toNat ≤ pend.toNat := by
  have h1 := USize.le_iff_toNat_le.mp hr
  have hcN : cap.toNat = min space 16777216 + 1 := by
    rw [hc]
    unfold capFor
    exact usize_ofNat' (by omega)
  have hne : cap ≠ 0 := fun e => by
    rw [e, show (0 : USize).toNat = 0 from rfl] at hcN
    omega
  unfold room at h1
  rw [usmin_toNat, ringSize_toNat hk, ite_eq_right hne, hcN] at h1
  have : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  omega

end Brotli.Decoder
