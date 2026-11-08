module

public import Brotli.Decoder.WorkStream
public import Brotli.Decoder.WorkHdr
public import Brotli.Decoder.StreamMem

@[expose] public section

/-!
# The work of the decoder's loop and of a call, against a potential

A potential on the stream's places holds what is still to do once the bits that make it necessary are read: a header's
potential and what its end costs, the commands' potential and what their end costs, and a round of a call for a
meta-block's start that waits for output space. A step's work is paid for by the potential and by the bits it reads, the
bytes it produces and the window it allocates; a step that stops the loop costs at most a constant more.
-/

namespace Brotli.Decoder

open Brotli.Spec

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

/-- What the commands' end costs: the round that ends the command loop, what the command loop's start holds for an entry
into the fast loop, the check that every block type occurred, the loop's round, and a round of the call at the next
meta-block's start. -/
def cmdsEnd : Nat := 84 + 3 + 1 + 1 + roundCost

/-- What a header's end costs beyond its potential: the command loop's header with its shared table bases and first
state, its derived tables' constant part (`tabCost`), the loop's round, and what the commands' start holds. Its last step
is within its place's potential, and its derived tables' share by the numbers of block types within its place's
`tabPot`. -/
def hdrEnd : Nat := 770 + trivRounds + 13300 + 1 + 106 + cmdsEnd

/-- What a metadata block's or an uncompressed block's end costs: its last step and the loop's round, and a round of the
call at the next meta-block's start. -/
def tailEnd : Nat := 2 + roundCost

/-- The potential of a stream's place. -/
def spot : SPhase → Nat
  | .wbits => 0
  | .mblock .. => 0
  | .skip .. => tailEnd
  | .raw .. => tailEnd
  | .hdr _ _ _ _ g p => hpot g p + tabPot g p + hdrEnd
  | .cmds _ _ _ p => cpot p + cmdsEnd
  | .ended _ => 0

/-- The potential of a state at a place: a meta-block's start with bytes waiting holds a round of the call. -/
def dpot (p : SPhase) (D : Dec) : Nat :=
  spot p + match p with
    | .mblock .. => if D.cmd.pend = 0 then 0 else roundCost
    | _ => 0

/-- A step's work against the potential: the potential at the place after it, the bits left there and the chunk's bytes
not yet taken, with its work, are at most the potential before, the bits and bytes there, 32 for each byte it produces,
and `extra`. A byte taken pays for the round that takes it. -/
def Pays (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (pos : USize) (r : Dec) (W extra : Nat) : Prop :=
  ∃ q, DRel r q ∧ OutD p q D r ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ (SInv p → SInv q) ∧
    ∀ t : List UInt8, W + dpot q r + hdrRate * (r.bits a r.pos stop (bits t)).length + (stop.toNat - r.pos.toNat) ≤
      dpot p D + hdrRate * (D.bits a pos stop (bits t)).length + (stop.toNat - pos.toNat) + 32 *(q.out.length - p.out.length) +
        extra

/-- A step that pays without the bytes it takes. -/
theorem Pays.intro {a : ByteArray} {stop : USize} {p : SPhase} {D : Dec} {pos : USize} {r : Dec} {W extra : Nat} (q : SPhase)
    (h1 : DRel r q) (h2 : OutD p q D r) (h3 : pos.toNat ≤ r.pos.toNat) (h4 : r.pos.toNat ≤ stop.toNat) (h5 : SInv p → SInv q)
    (h6 : ∀ t : List UInt8, W + dpot q r + hdrRate * (r.bits a r.pos stop (bits t)).length ≤
      dpot p D + hdrRate * (D.bits a pos stop (bits t)).length + 32 *(q.out.length - p.out.length) + extra) :
    Pays a stop p D pos r W extra :=
  ⟨q, h1, h2, h3, h4, h5, fun t => by have := h6 t; omega⟩

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

/-- The window a run of steps from `D` to `r` allocates: the one `r` holds, with 256 more for zero-filling it, when `D`
holds none. -/
def winD (D r : Dec) : Nat := if D.cmd.ring.size = 0 ∧ r.cmd.ring.size ≠ 0 then 2 ^ r.k.toNat + 256 else 0

/-! ### WBITS -/

theorem wbits_range {b : BitBuffer} (hw : b.Wf) (h : (wbitsFast b).status = .ok) :
    10 ≤ (wbitsFast b).a.toNat ∧ (wbitsFast b).a.toNat ≤ 24 := by
  have e := ((wbitsFast_ok hw).ok h).2 []
  rw [List.append_nil, List.append_nil] at e
  exact readWBITS_range e

/-- WBITS's step: ten at most, with the loop's round. It allocates no window. -/
theorem wbitsW_next {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hp : pos.toNat ≤ stop.toNat) : stepDWbitsW a stop hs D pos + 1 ≤ 10 := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepDWbitsW
  rw [ite_eq_left hp']
  have := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs hp
  omega

/-- WBITS's step that doesn't go on: three, with the loop's round, and a round for each byte its refill takes. -/
theorem wbitsW_stop {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status ≠ .next) :
    stepDWbitsW a stop hs D pos + 1 ≤ 3 + ((stepDWbits a stop hs D pos).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  unfold stepDWbits at hn ⊢
  unfold stepDWbitsW
  rw [dite_eq_left hp'] at hn ⊢
  rw [ite_eq_left hp']
  have hR := refillW_take (word := D.cmd.word) (count := D.cmd.count) hs hp
  dsimp only at hn ⊢
  split
  · dsimp only
    omega
  · dsimp only
    omega
  · rename_i heq
    rw [heq] at hn
    exact absurd rfl hn

/-- WBITS's step, against the potential. -/
theorem pay_wbits {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D .wbits)
    (hp : pos.toNat ≤ stop.toNat) :
    ((stepDWbits a stop hs D pos).status = .next → Pays a stop .wbits D pos (stepDWbits a stop hs D pos)
      (stepDWbitsW a stop hs D pos + 1) 0) ∧
    ((stepDWbits a stop hs D pos).status = .needsInput → Pays a stop .wbits D pos (stepDWbits a stop hs D pos)
      (stepDWbitsW a stop hs D pos + 1) 3) ∧
    ((stepDWbits a stop hs D pos).status ≠ .next →
      stepDWbitsW a stop hs D pos + 1 ≤ 3 + ((stepDWbits a stop hs D pos).pos.toNat - pos.toNat)) := by
  have hok := stepDWbits_ok (S := specSem) (hs := hs) hrel hp
  have hR : hdrRate = 2980 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => wbitsW_stop hp hn⟩
  · have hW := wbitsW_next (hs := hs) (D := D) hp
    obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
    have b1' := congrArg USize.toNat b1
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
    ∃ z, (metaGo D c r pos).hd = hdStart r.word r.count z := by
  unfold metaGo at h ⊢
  by_cases h0 : r.a = 0
  · simp only [ite_eq_left h0] at h
    cases h
  · simp only [ite_eq_right h0] at h ⊢
    by_cases h1 : r.a = 1
    · simp only [ite_eq_left h1] at h
      split at h
      · cases h
      · rw [ht] at h
        cases h
    · simp only [ite_eq_right h1] at h ⊢
      by_cases h2 : (r.d != 0) = true
      · simp only [ite_eq_left h2] at h
        split at h
        · split at h
          · split at h
            · cases h
            · rw [ht] at h
              cases h
          · cases h
        · rw [ht] at h
          cases h
      · simp only [ite_eq_right h2] at h ⊢
        by_cases h4 : c.ring.size = 0
        · simp only [ite_eq_left h4] at h ⊢
          by_cases h5 : (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c ≤ D.limit
          · simp only [ite_eq_left h5]
            exact ⟨_, rfl⟩
          · simp only [ite_eq_right h5] at h
            rw [ht] at h
            cases h
        · simp only [ite_eq_right h4]
          exact ⟨_, rfl⟩

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
      · obtain ⟨z, hz⟩ := metaGo_hd ht h
        exact ⟨_, _, z, hz⟩
    · rw [dite_eq_right hp] at h
      dsimp only at h
      rw [ht] at h
      cases h
  · rw [ite_eq_right h0] at h
    dsimp only at h
    rw [ht] at h
    cases h

/-- A header's start holds the potential of the literal category's number of block types not yet read. -/
theorem hpot_start {x y z : UInt64} {g : Gh} {p : HPhase} (h : HRel (hdStart x y z) g p) : hpot g p = 19908 := by
  have ht := h.tag_eq
  cases p with
  | cat i =>
    have hc : (hdStart x y z).cat = i := h.2.2.2
    cases i with
    | L => rfl
    | I => cases hc
    | D => cases hc
  | _ => cases ht

/-- A header's start holds no share of the derived tables. -/
theorem tabPot_start {x y z : UInt64} {g : Gh} {p : HPhase} (h : HRel (hdStart x y z) g p) : tabPot g p = 0 := by
  have ht := h.tag_eq
  cases p with
  | cat i => rfl
  | _ => cases ht

/-- The window a window's first state holds. -/
theorem winStart_size {c : Cmd} {word count need : UInt64} (h : need.toNat < 2 ^ 32) :
    (winStart c word count need).ring.size = need.toNat :=
  zeroBytes_size h

/-- `metaGo`'s work beyond its read is the zeros of the window it allocates, if any. -/
theorem metaGoW_le {D : Dec} {c : Cmd} {r : Rd} {pos : USize} (hl : D.limit.toNat < 2 ^ 32) :
    metaGoW D c r ≤ if c.ring.size = 0 then zbW (metaGo D c r pos).cmd.ring.size else 0 := by
  unfold metaGoW metaGo
  by_cases h0 : r.a = 0
  · simp only [ite_eq_left h0]
    exact Nat.zero_le _
  simp only [ite_eq_right h0]
  by_cases h1 : r.a = 1
  · simp only [ite_eq_left h1]
    exact Nat.zero_le _
  simp only [ite_eq_right h1]
  by_cases h4 : c.ring.size = 0
  · simp only [ite_eq_left h4]
    by_cases h2 : (r.d != 0) = true
    · simp only [ite_eq_left h2]
      by_cases h3 : r.buf.peek (r.count &&& 7) = 0
      · simp only [ite_eq_left h3]
        by_cases h5 : (1 : UInt64) <<< D.k.toUInt64 ≤ D.limit
        · simp only [ite_eq_left h5]
          rw [winStart_size (Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp h5) hl)]
          exact Nat.le_refl _
        · simp only [ite_eq_right h5]
          exact Nat.zero_le _
      · simp only [ite_eq_right h3]
        exact Nat.zero_le _
    · simp only [ite_eq_right h2]
      by_cases h5 : (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c ≤ D.limit
      · simp only [ite_eq_left h5]
        rw [winStart_size (Nat.lt_of_le_of_lt (UInt64.le_iff_toNat_le.mp h5) hl)]
        exact Nat.le_refl _
      · simp only [ite_eq_right h5]
        exact Nat.zero_le _
  · simp only [ite_eq_right h4, ite_self]
    exact Nat.le_refl _

/-- `metaGo` that doesn't go on allocates nothing. -/
theorem metaGoW_stop {D : Dec} {c : Cmd} {r : Rd} {pos : USize} (h : (metaGo D c r pos).status ≠ .next) :
    metaGoW D c r = 0 := by
  unfold metaGoW
  unfold metaGo at h
  by_cases h0 : r.a = 0
  · rw [ite_eq_left h0]
  rw [ite_eq_right h0]
  by_cases h1 : r.a = 1
  · rw [ite_eq_left h1]
  rw [ite_eq_right h1]
  simp only [ite_eq_right h0, ite_eq_right h1] at h
  by_cases h2 : (r.d != 0) = true
  · rw [ite_eq_left h2]
    simp only [ite_eq_left h2] at h
    by_cases h3 : r.buf.peek (r.count &&& 7) = 0
    · rw [ite_eq_left h3]
      simp only [ite_eq_left h3] at h
      by_cases h4 : c.ring.size = 0
      · rw [ite_eq_left h4]
        simp only [ite_eq_left h4] at h
        by_cases h5 : (1 : UInt64) <<< D.k.toUInt64 ≤ D.limit
        · simp only [ite_eq_left h5] at h <;> exact absurd rfl h
        · rw [ite_eq_right h5]
      · rw [ite_eq_right h4]
    · rw [ite_eq_right h3]
  · rw [ite_eq_right h2]
    simp only [ite_eq_right h2] at h
    by_cases h4 : c.ring.size = 0
    · rw [ite_eq_left h4]
      simp only [ite_eq_left h4] at h
      by_cases h5 : (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c ≤ D.limit
      · simp only [ite_eq_left h5] at h <;> exact absurd rfl h
      · rw [ite_eq_right h5]
    · rw [ite_eq_right h4]

theorem metaGo_out {D : Dec} {c : Cmd} {r : Rd} {pos : USize} : (metaGo D c r pos).status ≠ .needsOutput := by
  unfold metaGo
  repeat' (first | split_all | exact fun e => DStatus.noConfusion e)

/-- A meta-block's start's work: ten, and the zeros of the window it allocates. -/
theorem metaW_le {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hl : D.limit.toNat < 2 ^ 32) :
    stepDMetaW a stop hs D pos ≤ 10 + if D.cmd.ring.size = 0 then zbW (stepDMeta a stop hs D pos).cmd.ring.size else 0 := by
  unfold stepDMetaW stepDMeta
  by_cases h0 : D.cmd.pend = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    by_cases hp' : pos ≤ stop
    · rw [dite_eq_left hp', dite_eq_left hp']
      have hR := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs (USize.le_iff_toNat_le.mp hp')
      dsimp only
      generalize refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp') = rf
      generalize metaStartFast ⟨rf.word, rf.count⟩ = r
      cases hst : r.status with
      | ok =>
        dsimp only
        have := metaGoW_le (D := D) (c := D.cmd) (r := r) (pos := rf.pos) hl
        omega
      | short => dsimp only; omega
      | bad => dsimp only; omega
    · rw [dite_eq_right hp', dite_eq_right hp']
      omega
  · rw [ite_eq_right h0, ite_eq_right h0]
    omega

/-- A meta-block's start that doesn't go on: ten, and three with a round for each byte its refill takes. -/
theorem metaW_stop {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf) (hp : pos.toNat ≤ stop.toNat) (hn : (stepDMeta a stop hs D pos).status ≠ .next) :
    stepDMetaW a stop hs D pos ≤ 10 ∧ stepDMetaW a stop hs D pos ≤ 3 + (stop.toNat - pos.toNat) := by
  have hT := refillW_take (word := D.cmd.word) (count := D.cmd.count) hs hp
  have hS := (refill_spec hs hp hw).2.2.1
  have hR := refillW_le (word := D.cmd.word) (count := D.cmd.count) hs hp
  unfold stepDMetaW
  unfold stepDMeta at hn
  by_cases h0 : D.cmd.pend = 0
  · rw [ite_eq_left h0]
    rw [ite_eq_left h0] at hn
    by_cases hp' : pos ≤ stop
    · rw [dite_eq_left hp']
      rw [dite_eq_left hp'] at hn
      dsimp only at hn ⊢
      generalize metaStartFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩ = r at hn ⊢
      cases hst : r.status with
      | ok =>
        rw [hst] at hn
        dsimp only at hn ⊢
        rw [metaGoW_stop hn]
        constructor <;> omega
      | short => dsimp only; constructor <;> omega
      | bad => dsimp only; constructor <;> omega
    · rw [dite_eq_right hp']
      constructor <;> omega
  · rw [ite_eq_right h0]
    constructor <;> omega

/-- A meta-block's start, against the potential: the step that allocates the window is paid for with it. -/
theorem pay_mblock {w : Nat} {st : StreamState} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.mblock w st)) (hp : pos.toNat ≤ stop.toNat) :
    ((stepDMeta a stop hs D pos).status = .next → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) (winD D (stepDMeta a stop hs D pos))) ∧
    ((stepDMeta a stop hs D pos).status = .needsInput → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) 4) ∧
    ((stepDMeta a stop hs D pos).status = .needsOutput → Pays a stop (.mblock w st) D pos (stepDMeta a stop hs D pos)
      (stepDMetaW a stop hs D pos + 1) 2) ∧
    ((stepDMeta a stop hs D pos).status ≠ .next → stepDMetaW a stop hs D pos + 1 ≤ 12) := by
  have hok := stepDMeta_ok (S := specSem) (hs := hs) hrel hp
  have hl : D.limit.toNat < 2 ^ 32 := by have := hrel.2.2.limit; omega
  have hR : hdrRate = 2980 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_, fun hn => by have := (metaW_stop hrel.2.1 hp hn).1; omega⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    have hW : stepDMetaW a stop hs D pos ≤ 11 + winD D (stepDMeta a stop hs D pos) := by
      have hW0 := metaW_le (a := a) (stop := stop) (hs := hs) (pos := pos) hl
      unfold winD
      by_cases hz0 : D.cmd.ring.size = 0
      · rw [ite_eq_left hz0] at hW0
        by_cases hz1 : (stepDMeta a stop hs D pos).cmd.ring.size = 0
        · rw [hz1] at hW0
          rw [ite_eq_right (fun h => h.2 hz1)]
          have := zbW_le 0
          omega
        · rw [ite_eq_left ⟨hz0, hz1⟩]
          obtain ⟨e1, e2, -⟩ := hR'.arrays hz1
          rw [e1] at hW0
          have := zbW_le (2 ^ (stepDMeta a stop hs D pos).k.toNat)
          have hpw : 2 ^ (stepDMeta a stop hs D pos).k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) e2
          have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
          omega
      · rw [ite_eq_right hz0] at hW0
        rw [ite_eq_right (fun h => hz0 h.1)]
        omega
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
      have : dpot (.hdr w' st' l mlen g hp') (stepDMeta a stop hs D pos) = hpot g hp' + tabPot g hp' + hdrEnd := by
        unfold dpot spot
        dsimp only
        omega
      rw [this, hpot_start hrh, tabPot_start hrh]
      unfold hdrEnd cmdsEnd roundCost trivRounds
      omega
    | _ => exact absurd hsd id
  · obtain ⟨b1, b2, p', hR', _, _, hsd, _, hout, hj, _⟩ := hok.needsInput hn
    have b1' := congrArg USize.toNat b1
    have hW' := (metaW_stop (hs := hs) hrel.2.1 hp (by rw [hn]; exact fun e => DStatus.noConfusion e)).2
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
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
          · exact metaGo_out hn
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

theorem vleft_le {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) : vleft p ≤ 16384 := by
  cases p with
  | vals isL t r code done left =>
    obtain ⟨_, hu, _, hi, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ := h
    have := (mapSizeFast_eq (g := g) hi hu).2
    show left ≤ 16384
    omega
  | _ => exact Nat.zero_le _

theorem tsize_le {st : Hd} {g : Gh} {isL : Bool} (h : HRel st g (.trees isL)) : mapSize g isL ≤ 16384 := by
  obtain ⟨_, hu, _, hi⟩ := h
  exact (mapSizeFast_eq (g := g) hi hu).2

/-- A header's step, against the potential: a step that goes on is paid by the header's potential and bits, the header's
end by what the header holds for it, and a step that runs out of input costs at most 3; each byte a refill takes pays for
itself. -/
theorem pay_hdr {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.hdr w st last mlen g p)) (hp : pos.toNat ≤ stop.toNat)
    {hH : HIn D.hd} :
    ((stepDHdr a stop hs D pos hH hp).status = .next → Pays a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos hH hp)
      (stepDHdrW a stop hs D pos (fun _ => hH) hp + 1) 0) ∧
    ((stepDHdr a stop hs D pos hH hp).status = .needsInput → Pays a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos hH hp)
      (stepDHdrW a stop hs D pos (fun _ => hH) hp + 1) 3) ∧
    ((stepDHdr a stop hs D pos hH hp).status = .bad ∨ (stepDHdr a stop hs D pos hH hp).status = .memory →
      stepDHdrW a stop hs D pos (fun _ => hH) hp + 1 ≤ hpot g p + ((stepDHdr a stop hs D pos hH hp).pos.toNat - pos.toNat)) := by
  have hok := stepDHdr_ok (S := specSem) (hs := hs) (hH := hH) hrel hp
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hall, hl, hleft, hm1, hm2, hR, hp0, hb⟩ := hrel
  have ht' : tag = .hdr := ht
  subst ht'
  dsimp only at hR
  have hstep := stepH_ok (K := hdrK w (specSem.after w last) st mlen) (a := a) (hs := hs) (h := hH) hR hp hb
  have hsz := psize_le hR
  have eW : stepDHdrW a stop hs ⟨.hdr, cmd, hd, H, k, last', left, limit, pos', status⟩ pos (fun _ => hH) hp =
      stepHW a stop hs hd pos + (if hst : (stepH a stop hs hd pos hH hp).status = .ready then
        770 + trivRounds + mkHdrW (stepH a stop hs hd pos hH hp).d left (stepH_upto hH hp hst) else 0) := rfl
  rw [eW]
  unfold stepDHdr takeHd at hok ⊢
  dsimp only at hok ⊢
  generalize hrr : stepHR a stop hs hd pos hH hp = rr at hok ⊢
  obtain ⟨r, hr⟩ := rr
  have e : r = stepH a stop hs hd pos hH hp := by rw [← stepHR_val (h := hH) (hp := hp), hrr]
  subst e
  unfold hdrNext at hok ⊢
  dsimp only at hok ⊢
  by_cases hrd : (stepH a stop hs hd pos hH hp).status = .ready
  · rw [dite_eq_left hrd]
    split at hok <;> rename_i hst' <;> (try exact absurd (hrd.symm.trans hst') (fun e => HStatus.noConfusion e))
    have hW := stepHW_stop hR hb hp (by rw [hrd]; exact fun e => HStatus.noConfusion e)
    obtain ⟨g'', hu'', _, _, _, _, _, _, _, _, hx⟩ := hstep.ready hrd
    have hT := tabPot_exit (hx []) hu'' rfl
    have hM := mkHdrW_le (d := (stepH a stop hs hd pos hH hp).d) (mlen := left) (h := stepH_upto hH hp hrd)
    unfold tabCost at hM
    refine ⟨fun _ => ?_, fun e => DStatus.noConfusion e, fun e => by rcases e with e | e <;> exact DStatus.noConfusion e⟩
    obtain ⟨p', hR'', h1', h2', _, _, hout, hj⟩ := hok.next rfl
    refine ⟨p', hR'', hout, h1', h2', fun hi => sinv_of_sreach (hj []) hi, fun t => ?_⟩
    have hb := sreach_len (hj t)
    cases p' with
    | cmds w' l' m' cp =>
      have := cpot_command hR''.2.2.2.2.1 rfl
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot] at hb ⊢
      simp only [takeReady] at h1' h2' hb ⊢
      unfold hdrEnd
      rw [hdrRate_eq]
      omega
    | _ => exact absurd hR''.1 (fun e => DTag.noConfusion e)
  rw [dite_eq_right hrd]
  split <;> rename_i hst
  · obtain ⟨g', p', oc, hR', h1, h2, _, _, hmv, h5⟩ := hstep.next hst
    have hW := stepHW_cost hR hp hst hR' h5
    refine ⟨fun _ => ⟨.hdr w st last mlen g' p', ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0, hmv.bud hb⟩,
      ⟨[], rfl, rfl⟩, h1, h2, fun hi => sinv_of_sreach (sreach_hdr (q := (g, p)) (q' := (g', p')) (Reach.one (h5 []))) hi,
      fun t => ?_⟩, fun e => DStatus.noConfusion e, fun e => by rcases e with e | e <;> exact DStatus.noConfusion e⟩
    have hpy := hpay hsz (vleft_le hR) (fun isL e => by subst e; exact tsize_le hR)
      (fun o n order acc sum e => by subst e; exact hR.2.2.2.2.2.sumEq)
      (fun isL t r n e => by
        subst e
        obtain ⟨_, _, _, _, h2, _, _, hn⟩ := hR.2.2.2.2
        rw [hn]
        unfold contextMapAlphabetSize
        omega) (h5 (bits t))
    simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, clearHd]
    omega
  · obtain ⟨b1, b2, hR', _, _, hmv, h6, _⟩ := hstep.needsInput hst
    have hW := stepHW_short (hs := hs) (st := hd) (pos := pos) hst
    have b1' := congrArg USize.toNat b1
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨.hdr w st last mlen g p,
      ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0, hmv.bud hb⟩, ⟨[], rfl, rfl⟩,
      by rw [b1]; exact hp, by rw [b1]; exact Nat.le_refl _, fun hi => hi, fun t => ?_⟩,
      fun e => by rcases e with e | e <;> exact DStatus.noConfusion e⟩
    simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, clearHd]
    rw [h6]
    omega
  · have hW := stepHW_stop hR hb hp (by rw [hst]; exact fun e => HStatus.noConfusion e)
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => by omega⟩
  · have hW := stepHW_stop hR hb hp (by rw [hst]; exact fun e => HStatus.noConfusion e)
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => by omega⟩
  · exact absurd hst hrd

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
  simp [cpot, crank, cstage, cred, h0]

/-- The commands' step, against the potential: the command loop's work is paid for by the commands' potential, their
bits and bytes, and the commands' end by what they hold for it. A loop that runs out of its budget has read or produced
enough to pay for its round. -/
theorem pay_cmds {w : Nat} {last : Bool} {m : MetaBlockHeader} {q0 : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m q0)) (hsi : SInv (.cmds w last m q0))
    (_hp : pos.toNat ≤ stop.toNat) {h : CmdInv D.H D.k stop D.cmd pos} :
    ((stepDCmds a stop hs D pos h).status = .next → Pays a stop (.cmds w last m q0) D pos (stepDCmds a stop hs D pos h)
      (stepDCmdsW a stop hs D pos h + 1) 0) ∧
    ((stepDCmds a stop hs D pos h).status = .needsInput ∨ (stepDCmds a stop hs D pos h).status = .needsOutput →
      Pays a stop (.cmds w last m q0) D pos (stepDCmds a stop hs D pos h) (stepDCmdsW a stop hs D pos h + 1) 88) ∧
    ((stepDCmds a stop hs D pos h).status = .bad → ∃ L, D.cmd.pend.toNat + L ≤ (stepDCmds a stop hs D pos h).cmd.pend.toNat ∧
      ∀ t : List UInt8, stepDCmdsW a stop hs D pos h + 1 +
        hdrRate * ((stop.toNat - (stepDCmds a stop hs D pos h).pos.toNat) * 8) +
        (stop.toNat - (stepDCmds a stop hs D pos h).pos.toNat) ≤
        dpot (.cmds w last m q0) D + hdrRate * (D.bits a pos stop (bits t)).length + (stop.toNat - pos.toNat) + 32 *L + 96) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hl, hlim, hH, hR, hlive⟩ := hrel
  have ht' : tag = .cmds := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  obtain ⟨hm, hci⟩ := hsi
  dsimp only at hR
  obtain ⟨c, q, st', pos'', hq, hciq, o1, g1, g2, hr, g3, g4, gb, g5, g6⟩ :=
    runCmdFW_count (w := w) (k := k) (hs := hs) hm hH cmdBudget hR hci h []
  have hliveq : CLive q := reach_live hr.reach hlive
  obtain ⟨-, c1, c2, c3, c4⟩ := creach hm hr hci
  have hq8 := crank_le q
  have hp8 := crank_le q0
  have hcp := cpot_le q0
  have hal := alw_le q0
  have hb65 : cmdBudget.toNat = 65536 := usize_ofNat' (by decide)
  obtain ⟨l, hl1, hl2⟩ := o1
  have hl2' : st'.pend.toNat = cmd.pend.toNat + l.length := hl2
  have hlo : q.out.length - q0.out.length = l.length := by rw [hl1, List.length_append]; omega
  have hRate : hdrRate = 2980 := rfl
  have eW : stepDCmdsW a stop hs ⟨.cmds, cmd, hd, H, k, last', left, limit, pos', status⟩ pos h =
      runCmdFW H k a stop hs cmdBudget cmd pos h +
        (if (runCmdF H k a stop hs cmdBudget cmd pos h).status = .done then 1 else 0) := rfl
  simp only [stateBits] at g3 c1 c3
  rw [eW]
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmdFW H k a stop hs cmdBudget cmd pos h = W at g3 ⊢
  generalize runCmdF H k a stop hs cmdBudget cmd pos h = rc at g3 g4 gb g5 g6 ⊢
  cases hst : rc.status with
  | next =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    have hc := g6 hst
    simp only [↓reduceIte] at hc
    have he : cmdEnd st' = 1 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun _ => ?_, fun e => ?_, fun e => ?_⟩
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq, hliveq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
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
    have he : cmdEnd st' = 84 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun e => ?_, fun _ => ?_, fun e => ?_⟩
    · cases e
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq, hliveq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
      simp only [Dec.bits, Dec.word, Dec.count, clearCmd, dpot, spot, SPhase.out]
      rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate, hlo]
      omega
    · cases e
  | needsOutput =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    have he : cmdEnd st' = 84 := by unfold cmdEnd; rw [hst]; rfl
    rw [he] at g3
    rw [ite_eq_right (fun e => StepStatus.noConfusion e)]
    refine ⟨fun e => ?_, fun _ => ?_, fun e => ?_⟩
    · cases e
    · refine ⟨.cmds w last' m q, ⟨rfl, rfl, hlim, hH, hq, hliveq⟩, ⟨l, hl1, hl2⟩, g1, g2, fun _ => ⟨hm, hciq⟩, fun t => ?_⟩
      simp only [Dec.bits, Dec.word, Dec.count, clearCmd, dpot, spot, SPhase.out]
      rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate, hlo]
      omega
    · cases e
  | bad =>
    have he : cmdEnd rc = 92 := by unfold cmdEnd; rw [hst]; rfl
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
    · show _ + 1 + hdrRate * ((stop.toNat - rc.pos.toNat) * 8) + (stop.toNat - rc.pos.toNat) ≤ _
      simp only [Dec.bits, Dec.word, Dec.count, dpot, spot]
      rw [avail_len cmd.word cmd.count a pos stop (bits t), hRate]
      rw [hlo] at g3
      omega
  | done =>
    obtain ⟨e1, e2⟩ := g4 (by rw [hst]; decide)
    subst e1
    subst e2
    obtain ⟨s, rfl, h0⟩ := g5 hst
    have he : cmdEnd st' = 84 := by unfold cmdEnd; rw [hst]; rfl
    rw [he, cpot_end h0] at g3
    rw [ite_eq_left rfl]
    have hcheck := seenOk_iff hH hq
    have hq' := hq
    obtain ⟨hC, htg, hprod⟩ := hq'
    have hwin := hC.toWin
    have hlv : 1 ≤ s.produced + s.remaining := hliveq
    have hne : s.produced ≠ 0 := by omega
    by_cases hsee : seenOk st' H.nL H.nI H.nD = true
    · rw [ite_eq_left hsee]
      refine ⟨fun _ => ?_, fun e => ?_, fun e => ?_⟩
      rotate_left
      · rcases e with e | e <;> cases e
      · cases e
      cases last' with
      | true =>
        refine ⟨.ended ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, w, Or.inl ⟨⟨hwin, hprod, hlim⟩, hne⟩⟩, ⟨l, hl1, hl2⟩, g1, g2,
          fun _ => trivial, fun t => ?_⟩
        simp only [Dec.bits, Dec.word, Dec.count, dpot, spot, SPhase.out, ↓reduceIte]
        rw [avail_len st'.word st'.count a st'.pos stop (bits t), avail_len cmd.word cmd.count a pos stop (bits t), hRate]
        have hlo' : s.output.length - q0.out.length = l.length := hlo
        try rw [hlo] at g3
        rw [hlo']
        unfold cmdsEnd roundCost
        omega
      | false =>
        refine ⟨.mblock w ⟨s.output, s.produced, s.distances⟩, ⟨rfl, hC.wf, Or.inl ⟨⟨hwin, hprod, hlim⟩, hne⟩⟩, ⟨l, hl1, hl2⟩, g1, g2,
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
      show _ + 1 + hdrRate * ((stop.toNat - st'.pos.toNat) * 8) + (stop.toNat - st'.pos.toNat) ≤ _
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
  have hR : hdrRate = 2980 := rfl
  have hd : dpot (.skip w st last n) D = 10 := rfl
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
    refine Pays.intro p' hR' hout (by rw [b1]; exact hp) (by rw [b1]; exact Nat.le_refl _) (fun hi => sinv_of_sreach (hj []) hi)
      (fun t => ?_)
    have hb := sreach_len (hj t)
    rw [hd, hR]
    cases p' with
    | skip w' st' l n' =>
      have : dpot (.skip w' st' l n') (stepDSkip stop D pos) = 10 := rfl
      omega
    | _ => exact absurd hsd id
  · obtain ⟨p', hR', h1, h2, _, _, hsd, _, hout, hj⟩ := hok.needsOutput hn
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
  have hR : hdrRate = 2980 := rfl
  have hd : dpot (.raw w st last n) D = 10 := rfl
  have hW := rawW_le (hs := hs) (D := D) (pos := pos)
  refine ⟨fun hn => ?_, fun hn => ?_, fun hn => ?_, by omega⟩
  · obtain ⟨p', hR', h1, h2, _, hsd, hout, hj⟩ := hok.next hn
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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
    refine Pays.intro p' hR' hout (by rw [b1]; exact hp) (by rw [b1]; exact Nat.le_refl _) (fun hi => sinv_of_sreach (hj []) hi)
      (fun t => ?_)
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
    refine Pays.intro p' hR' hout h1 h2 (fun hi => sinv_of_sreach (hj []) hi) (fun t => ?_)
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

/-- The window's log size a meta-block's start allocates is in 10..24 when the stream's is. -/
theorem allocBits_range {k : USize} (last : Bool) (m : UInt64) (h10 : 10 ≤ k.toNat) (h24 : k.toNat ≤ 24) :
    10 ≤ (allocBits k last m).toUSize.toNat ∧ (allocBits k last m).toUSize.toNat ≤ 24 ∧
      (allocBits k last m).toUSize.toNat ≤ k.toNat := by
  have e := allocBits_toNat (k := k) last m
  have hr := fitBits_range m.toNat
  cases last with
  | false =>
    have e' : (allocBits k false m).toNat = k.toNat := e
    rw [word_toUSize (by omega), e']
    exact ⟨h10, h24, Nat.le_refl _⟩
  | true =>
    have e' : (allocBits k true m).toNat = min k.toNat (fitBits m.toNat) := e
    rw [word_toUSize (by omega), e']
    omega

/-- A step from a state with nothing at WBITS keeps the window's log size in 10..24, and never raises it. -/
theorem stepD_k10 {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {hinv : DInv stop D} (h : D.tag ≠ .wbits)
    (hk : 10 ≤ D.k.toNat ∧ D.k.toNat ≤ 24) : 10 ≤ (stepD a stop hs D hinv).k.toNat ∧ (stepD a stop hs D hinv).k.toNat ≤ 24 ∧
      (stepD a stop hs D hinv).k.toNat ≤ D.k.toNat := by
  have hk' : 10 ≤ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.k.toNat ≤ D.k.toNat := ⟨hk.1, hk.2, Nat.le_refl _⟩
  cases ht : D.tag
  · exact absurd ht h
  · rw [stepD_mblock ht]
    unfold stepDMeta metaGo
    repeat' (first | split_all | exact hk' | exact allocBits_range _ _ hk.1 hk.2)
  · rw [stepD_skip ht]
    unfold stepDSkip moveOn
    repeat' (first | split_all | exact hk')
  · rw [stepD_raw ht]
    unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | exact hk')
  · rw [stepD_hdr ht]
    unfold stepDHdr takeHd clearHd hdrNext
    dsimp only
    repeat' (first | split_all | exact hk')
  · rw [stepD_cmds ht]
    unfold stepDCmds takeCmd clearCmd
    dsimp only
    repeat' (first | split_all | exact hk')
  · rw [stepD_ended ht]
    exact hk'

/-- A step from a state that holds a window keeps it and its size. -/
theorem stepD_ringK {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} {hinv : DInv stop D}
    (hrel : DRel D p) (hr : D.cmd.ring.size ≠ 0) :
    (stepD a stop hs D hinv).cmd.ring.size = D.cmd.ring.size ∧ (stepD a stop hs D hinv).k = D.k := by
  cases p with
  | wbits => exact absurd hrel.2.2.2.2 hr
  | mblock w st =>
    rw [stepD_mblock hrel.1]
    unfold stepDMeta metaGo
    constructor <;>
      repeat' (first | split_all | rfl | trivial | exact absurd ‹D.cmd.ring.size = 0› hr)
  | skip w st last n =>
    rw [stepD_skip hrel.1]
    refine ⟨by rw [(stepDSkip_win stop D D.pos).1], ?_⟩
    unfold stepDSkip moveOn
    repeat' (first | split_all | rfl | trivial)
  | raw w st last n =>
    rw [stepD_raw hrel.1]
    refine ⟨stepDRaw_ring a stop hs D D.pos, ?_⟩
    unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | rfl | trivial)
  | hdr w st last mlen g q =>
    rw [stepD_hdr hrel.1]
    unfold stepDHdr takeHd clearHd hdrNext
    dsimp only
    constructor <;> repeat' (first | split_all | rfl | trivial)
  | cmds w last m q =>
    rw [stepD_cmds hrel.1]
    refine ⟨stepDCmds_ring' hrel hinv.2, ?_⟩
    unfold stepDCmds takeCmd clearCmd
    dsimp only
    repeat' (first | split_all | rfl | trivial)
  | ended st =>
    rw [stepD_ended hrel.1]
    exact ⟨rfl, rfl⟩

/-- A state stands for a place past WBITS only with a window's log size of at most 24. -/
theorem DRel.k24 {D : Dec} {p : SPhase} (h : DRel D p) (ht : D.tag ≠ .wbits) : D.k.toNat ≤ 24 := by
  by_cases hr : D.cmd.ring.size = 0
  · cases p with
    | wbits => exact absurd h.1 ht
    | mblock => exact (h.2.2.noRing hr).k24
    | skip => exact (h.2.2.1.noRing hr).k24
    | ended =>
      obtain ⟨_, _, w, hw⟩ := h
      exact (hw.noRing hr).k24
    | raw => exact absurd h.1 (h.noRing hr).2.2
    | hdr => exact absurd h.1 (h.noRing hr).1
    | cmds => exact absurd h.1 (h.noRing hr).2.1
  · exact (h.arrays hr).2.1

/-- Bytes wait only in a window. -/
theorem DRel.ring_of_pend {D : Dec} {p : SPhase} (h : DRel D p) (hp : D.cmd.pend ≠ 0) : D.cmd.ring.size ≠ 0 := by
  intro hr
  cases p with
  | wbits => exact hp h.2.2.2.1
  | mblock => exact hp (h.2.2.noRing hr).pend
  | skip => exact hp (h.2.2.1.noRing hr).pend
  | ended =>
    obtain ⟨_, _, w, hw⟩ := h
    exact hp (hw.noRing hr).pend
  | raw => exact (h.noRing hr).2.2 h.1
  | hdr => exact (h.noRing hr).1 h.1
  | cmds => exact (h.noRing hr).2.1 h.1

/-- WBITS's step allocates no window. -/
theorem stepDWbits_ring {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDWbits a stop hs D pos).cmd.ring = D.cmd.ring := by
  unfold stepDWbits
  repeat' (first | split_all | rfl | trivial)

/-- What a step that pauses costs beyond the potential: a meta-block's start that waits for output space the least, and
any other pause at most the command loop's stopping round and its round. -/
def stopCost (r : Dec) : Nat := if r.status = .needsOutput ∧ r.tag = .mblock then 2 else 88

theorem stopCost_ge (r : Dec) : 2 ≤ stopCost r := by
  unfold stopCost
  split <;> omega

theorem stepDCmds_out_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (ht : D.tag = .cmds)
    {h : CmdInv D.H D.k stop D.cmd pos} :
    (stepDCmds a stop hs D pos h).status = .needsOutput → (stepDCmds a stop hs D pos h).tag = .cmds := by
  unfold stepDCmds takeCmd clearCmd
  dsimp only
  repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) | (intro _; exact ht))

theorem stopCost_in {r : Dec} (h : r.status = .needsInput) : stopCost r = 88 := by
  unfold stopCost
  rw [ite_eq_right (fun e => absurd (h.symm.trans e.1) (fun e => DStatus.noConfusion e))]

theorem stopCost_out {r : Dec} (ht : r.tag ≠ .mblock) : stopCost r = 88 := by
  unfold stopCost
  rw [ite_eq_right (fun e => ht e.2)]

/-- No step goes back to WBITS. -/
theorem stepD_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {hinv : DInv stop D} (h : D.tag ≠ .wbits) :
    (stepD a stop hs D hinv).tag ≠ .wbits := by
  cases ht : D.tag
  · exact absurd ht h
  · rw [stepD_mblock ht]
    unfold stepDMeta metaGo
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [stepD_skip ht]
    unfold stepDSkip moveOn
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [stepD_raw ht]
    unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [stepD_hdr ht]
    unfold stepDHdr takeHd clearHd hdrNext
    dsimp only
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [stepD_cmds ht]
    unfold stepDCmds takeCmd clearCmd
    dsimp only
    repeat' (first | split_all | (exact fun e => DTag.noConfusion e) | (rw [ht]; exact fun e => DTag.noConfusion e))
  · rw [stepD_ended ht, ht]
    exact fun e => DTag.noConfusion e

/-- WBITS's step that goes on leaves WBITS. -/
theorem stepDWbits_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDWbits a stop hs D pos).status = .next → (stepDWbits a stop hs D pos).tag ≠ .wbits := by
  unfold stepDWbits
  repeat' (first | split_all | (intro _; exact fun e => DTag.noConfusion e) | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- After WBITS, the loop keeps the window's log size in 10..24. -/
theorem runD_kr {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ x : RunArg a stop hs, x.D.tag ≠ .wbits → 10 ≤ x.D.k.toNat ∧ x.D.k.toNat ≤ 24 →
      (runD a stop hs x.D x.inv).tag ≠ .wbits ∧ 10 ≤ (runD a stop hs x.D x.inv).k.toNat ∧
        (runD a stop hs x.D x.inv).k.toNat ≤ 24 ∧ (runD a stop hs x.D x.inv).k.toNat ≤ x.D.k.toNat := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    intro h hk
    dsimp only at ih h hk ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact ⟨h, hk.1, hk.2, Nat.le_refl _⟩
    · rw [dite_eq_right he]
      dsimp only
      have s1 := stepD_k10 (hs := hs) (hinv := hinv) h hk
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        obtain ⟨i1, i2, i3, i4⟩ := ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ (stepD_tag (hinv := hinv) h) ⟨s1.1, s1.2.1⟩
        exact ⟨i1, i2, i3, Nat.le_trans i4 s1.2.2⟩
      · rw [dite_eq_right hn]
        exact ⟨stepD_tag h, s1⟩

/-- No run of the loop goes back to WBITS. -/
theorem runD_tag {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ x : RunArg a stop hs, x.D.tag ≠ .wbits → (runD a stop hs x.D x.inv).tag ≠ .wbits := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    intro h
    dsimp only at ih h ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact h
    · rw [dite_eq_right he]
      dsimp only
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        exact ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ (stepD_tag (hinv := hinv) h)
      · rw [dite_eq_right hn]
        exact stepD_tag h

/-- The loop from a state that holds a window keeps it and its size. -/
theorem runD_ring {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} :
    ∀ (x : RunArg a stop hs) (p : SPhase), DRel x.D p → x.D.cmd.ring.size ≠ 0 →
      (runD a stop hs x.D x.inv).cmd.ring.size = x.D.cmd.ring.size ∧ (runD a stop hs x.D x.inv).k = x.D.k := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    intro p hrel hr
    dsimp only at ih hrel hr ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact ⟨rfl, rfl⟩
    · rw [dite_eq_right he]
      dsimp only
      have s1 := stepD_ringK (hs := hs) (hinv := hinv) hrel hr
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        obtain ⟨q1, hR1, -⟩ := (stepD_ok specSem (hs := hs) (h := hinv) hrel he hinv.2).next hn
        obtain ⟨i1, i2⟩ := ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ q1 hR1 (by rw [s1.1]; exact hr)
        exact ⟨i1.trans s1.1, i2.trans s1.2⟩
      · rw [dite_eq_right hn]
        exact s1

/-- A meta-block's start, when it reports the limit, leaves the bytes waiting as they were. -/
theorem stepDMeta_memPend {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    (stepDMeta a stop hs D pos).status = .memory → (stepDMeta a stop hs D pos).cmd.pend = D.cmd.pend := by
  unfold stepDMeta metaGo
  repeat' (first | split_all | (intro _; rfl) | (intro _; trivial) |
    (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- A header's step, when it reports the limit, leaves the bytes waiting as they were. -/
theorem stepDHdr_memPend {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    {hH : HIn D.hd} {hp : pos.toNat ≤ stop.toNat} :
    (stepDHdr a stop hs D pos hH hp).status = .memory → (stepDHdr a stop hs D pos hH hp).cmd.pend = D.cmd.pend := by
  unfold stepDHdr takeHd clearHd hdrNext takeReady cmdStart
  dsimp only
  repeat' (first | split_all | (intro _; rfl) | (intro _; trivial) | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))

/-- A stream step, against the potential: one that goes on is paid for, with the window when it is WBITS's; one that
pauses costs at most 88 more; one that rejects or reports the limit costs at most the potential, the bits, the bytes it
decodes first, which are waiting after it, and 96. -/
theorem pay_stepD {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {p : SPhase} (hrel : DRel D p)
    (hsi : SInv p) (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) {hinv : DInv stop D} :
    ((stepD a stop hs D hinv).status = .next → Pays a stop p D D.pos (stepD a stop hs D hinv) (stepDW a stop hs D hinv + 1)
      (winD D (stepD a stop hs D hinv))) ∧
    ((stepD a stop hs D hinv).status = .needsInput ∨ (stepD a stop hs D hinv).status = .needsOutput →
      Pays a stop p D D.pos (stepD a stop hs D hinv) (stepDW a stop hs D hinv + 1) (stopCost (stepD a stop hs D hinv))) ∧
    ((stepD a stop hs D hinv).status = .bad ∨ (stepD a stop hs D hinv).status = .memory → ∃ L,
      D.cmd.pend.toNat + L ≤ (stepD a stop hs D hinv).cmd.pend.toNat ∧
      ((stepD a stop hs D hinv).status = .memory → (stepD a stop hs D hinv).cmd.pend.toNat = 0) ∧ ∀ t : List UInt8,
      stepDW a stop hs D hinv + 1 + hdrRate * ((stop.toNat - (stepD a stop hs D hinv).pos.toNat) * 8) +
        (stop.toNat - (stepD a stop hs D hinv).pos.toNat) ≤
        dpot p D + hdrRate * (D.bits a D.pos stop (bits t)).length + (stop.toNat - D.pos.toNat) + 32 *L + 96) := by
  have hok := stepD_ok specSem (hs := hs) (h := hinv) hrel he hp
  have hpl := stepD_pendLe a stop hs D hinv
  have hmem : (stepD a stop hs D hinv).status = .memory →
      (∃ w, p = .mblock w ⟨[], 0, initialDistances⟩) ∨ ∃ w st last mlen g q, p = .hdr w st last mlen g q :=
    fun h => (hok.memory h).2.2.2.2
  have hpos2 : (stepD a stop hs D hinv).status = .bad ∨ (stepD a stop hs D hinv).status = .memory →
      D.pos.toNat ≤ (stepD a stop hs D hinv).pos.toNat ∧ (stepD a stop hs D hinv).pos.toNat ≤ stop.toNat := by
    intro h
    rcases h with h | h
    · obtain ⟨_, _, _, d1, d2, _⟩ := (hok.bad h).2
      omega
    · exact ⟨(hok.memory h).1, (hok.memory h).2.1⟩
  have hpos : (stepD a stop hs D hinv).status = .bad ∨ (stepD a stop hs D hinv).status = .memory →
      D.pos.toNat ≤ (stepD a stop hs D hinv).pos.toNat := fun h => (hpos2 h).1
  cases p with
  | wbits =>
    have e1 : stepD a stop hs D hinv = stepDWbits a stop hs D D.pos := stepD_wbits hrel.1
    have e2 : stepDW a stop hs D hinv = stepDWbitsW a stop hs D D.pos := stepDW_wbits hrel.1
    rw [e1, e2]
    rw [e1] at hok hpos
    obtain ⟨n1, n2, n3⟩ := pay_wbits (hs := hs) hrel hp
    refine ⟨fun h => (n1 h).mono (Nat.zero_le _), fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (by rw [stopCost_in h]; omega)
      · obtain ⟨p', _, _, _, _, hne0, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | wbits =>
          have e : (stepDWbits a stop hs D D.pos).cmd.pend = D.cmd.pend := hsd
          rw [e, hrel.2.2.2.1] at hne0
          exact absurd rfl hne0
        | _ => exact absurd hsd id
    · have := n3 (by rcases h with h | h <;> rw [h] <;> exact fun e => DStatus.noConfusion e)
      have h0 : D.cmd.pend.toNat = 0 := by rw [hrel.2.2.2.1]; rfl
      rw [e1] at hpos2
      refine ⟨0, by omega, fun hm => ?_,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); have := hpos2 h; omega⟩
      rcases hmem (by rw [e1]; exact hm) with ⟨_, h'⟩ | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
  | mblock w st =>
    have e1 : stepD a stop hs D hinv = stepDMeta a stop hs D D.pos := stepD_mblock hrel.1
    have e2 : stepDW a stop hs D hinv = stepDMetaW a stop hs D D.pos := stepDW_mblock hrel.1
    rw [e1, e2]
    obtain ⟨n1, n2, n3, n4⟩ := pay_mblock (hs := hs) hrel hp
    rw [e1] at hok hpos hpos2
    refine ⟨n1, fun h => ?_, fun h => ?_⟩
    rotate_left
    · have hnn : (stepDMeta a stop hs D D.pos).status ≠ .next := by
        rcases h with h | h <;> rw [h] <;> exact fun e => DStatus.noConfusion e
      have := n4 hnn
      have hle : (stepDMeta a stop hs D D.pos).cmd.pend = D.cmd.pend := by
        rcases h with h | h
        · exact (stepDMeta_badWin h).1.2.2
        · exact stepDMeta_memPend h
      have e3 := congrArg USize.toNat hle
      refine ⟨0, by omega, fun hm => ?_,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); have := hpos2 h; omega⟩
      rw [stepDMeta_memPend hm]
      rcases hmem (by rw [e1]; exact hm) with ⟨w', hw'⟩ | ⟨_, _, _, _, _, _, h'⟩
      · cases hw'
        rcases hrel.2.2 with ⟨_, hne⟩ | hn0
        · exact absurd rfl hne
        · rw [hn0.pend]
          rfl
      · cases h'
    rcases h with h | h
    · exact (n2 h).mono (by rw [stopCost_in h]; omega)
    · have ht : (stepDMeta a stop hs D D.pos).tag = .mblock := by
        obtain ⟨p', hR', _, _, _, _, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | mblock => exact hR'.1
        | _ => exact absurd hsd id
      have hsc : stopCost (stepDMeta a stop hs D D.pos) = 2 := by
        unfold stopCost
        rw [ite_eq_left ⟨h, ht⟩]
      exact (n3 h).mono (Nat.le_of_eq hsc.symm)
  | skip w st last n =>
    have e1 : stepD a stop hs D hinv = stepDSkip stop D D.pos := stepD_skip hrel.1
    have e2 : stepDW a stop hs D hinv = 1 := stepDW_skip hrel.1
    rw [e1, e2]
    obtain ⟨n1, n2, n3⟩ := pay_skip (a := a) (hs := hs) hrel hp
    rw [e1] at hpos
    refine ⟨fun h => (n1 h).mono (Nat.zero_le _), fun h => ?_, fun h => ?_⟩
    rotate_left
    · rcases h with h | h
      · have e3 := congrArg USize.toNat (stepDSkip_badWin h).1.2.2
        exact ⟨0, by omega, fun h' => absurd (h'.symm.trans h) (fun e => DStatus.noConfusion e),
          fun t => by have := rate_chunk D hs (hpos (Or.inl h)) (bits t); have := hpos (Or.inl h); omega⟩
      · rcases hmem (by rw [e1]; exact h) with ⟨_, h'⟩ | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
    rcases h with h | h
    · exact (n2 h).mono (stopCost_ge _)
    · exact (n3 h).mono (stopCost_ge _)
  | raw w st last n =>
    have e1 : stepD a stop hs D hinv = stepDRaw a stop hs D D.pos := stepD_raw hrel.1
    have e2 : stepDW a stop hs D hinv = stepDRawW a stop hs D D.pos := stepDW_raw hrel.1
    rw [e1, e2]
    rw [e1] at hpl hok hpos
    obtain ⟨n1, n2, n3, n4⟩ := pay_raw (hs := hs) hrel hp
    refine ⟨fun h => (n1 h).mono (Nat.zero_le _), fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (by rw [stopCost_in h]; omega)
      · have ht : (stepDRaw a stop hs D D.pos).tag ≠ .mblock := by
          obtain ⟨p', hR', _, _, _, _, hsd, _⟩ := hok.needsOutput h
          cases p' with
          | raw => rw [hR'.1]; exact fun e => DTag.noConfusion e
          | _ => exact absurd hsd id
        exact (n3 h).mono (by rw [stopCost_out ht]; omega)
    · have := hpl.2
      have hle : D.cmd.pend.toNat ≤ (stepDRaw a stop hs D D.pos).cmd.pend.toNat := by
        rcases h with h | h
        · exact Nat.le_of_eq (congrArg USize.toNat (stepDRaw_badWin h).1.2.2).symm
        · rcases hmem (by rw [e1]; exact h) with ⟨_, h'⟩ | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
      refine ⟨(stepDRaw a stop hs D D.pos).cmd.pend.toNat - D.cmd.pend.toNat, by omega, fun hm => ?_,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); have := hpos h; omega⟩
      rcases hmem (by rw [e1]; exact hm) with ⟨_, h'⟩ | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
  | hdr w st last mlen g q =>
    have e1 : stepD a stop hs D hinv = stepDHdr a stop hs D D.pos (hinv.hd hrel.1) hinv.2 := stepD_hdr hrel.1
    have e2 : stepDW a stop hs D hinv = stepDHdrW a stop hs D D.pos hinv.hd hinv.2 := stepDW_hdr hrel.1
    rw [e1, e2]
    rw [e1] at hok hpos hpos2
    obtain ⟨n1, n2, n3⟩ := pay_hdr (hs := hs) (hH := hinv.hd hrel.1) hrel hinv.2
    refine ⟨fun h => (n1 h).mono (Nat.zero_le _), fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (n2 h).mono (by rw [stopCost_in h]; omega)
      · obtain ⟨p', _, _, _, _, hne0, hsd, _⟩ := hok.needsOutput h
        cases p' with
        | hdr w' st' l' ml' g' q' =>
          have e : (stepDHdr a stop hs D D.pos (hinv.hd hrel.1) hinv.2).cmd.pend = D.cmd.pend := hsd.2
          rw [e, hrel.2.2.2.2.2.2.2.1] at hne0
          exact absurd rfl hne0
        | _ => exact absurd hsd id
    · have := n3 h
      have hd : dpot (.hdr w st last mlen g q) D = hpot g q + tabPot g q + hdrEnd := rfl
      have h0 : D.cmd.pend.toNat = 0 := by rw [hrel.2.2.2.2.2.2.2.1]; rfl
      exact ⟨0, by omega, fun hm => by rw [stepDHdr_memPend hm]; exact h0,
        fun t => by have := rate_chunk D hs (hpos h) (bits t); have := hpos2 h; omega⟩
  | cmds w last m q =>
    have e1 : stepD a stop hs D hinv = stepDCmds a stop hs D D.pos (hinv.cmd hrel.1) := stepD_cmds hrel.1
    have e2 : stepDW a stop hs D hinv = stepDCmdsW a stop hs D D.pos (hinv.cmd hrel.1) := stepDW_cmds hrel.1
    rw [e1, e2]
    obtain ⟨n1, n2, n3⟩ := pay_cmds (hs := hs) (h := hinv.cmd hrel.1) hrel hsi hp
    refine ⟨fun h => (n1 h).mono (Nat.zero_le _), fun h => ?_, fun h => ?_⟩
    · rcases h with h' | h'
      · exact (n2 (Or.inl h')).mono (by rw [stopCost_in h']; omega)
      · have ht : (stepDCmds a stop hs D D.pos (hinv.cmd hrel.1)).tag ≠ .mblock := by
          rw [stepDCmds_out_tag hrel.1 h']
          exact fun e => DTag.noConfusion e
        exact (n2 (Or.inr h')).mono (Nat.le_of_eq (stopCost_out ht).symm)
    rcases h with h | h
    · obtain ⟨L, hL, hb⟩ := n3 h
      exact ⟨L, hL, fun hm => absurd (hm.symm.trans h) (fun e => DStatus.noConfusion e), fun t => by have := hb t; omega⟩
    · rcases hmem (by rw [e1]; exact h) with ⟨_, h'⟩ | ⟨_, _, _, _, _, _, h'⟩ <;> cases h'
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
theorem stepD_room {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {hinv : DInv stop D} (he : D.tag ≠ .ended) :
    (stepD a stop hs D hinv).status = .needsOutput → (stepD a stop hs D hinv).tag ≠ .mblock →
      room (stepD a stop hs D hinv).k (stepD a stop hs D hinv).cmd.cap ≤ (stepD a stop hs D hinv).cmd.pend := by
  cases ht : D.tag
  · rw [stepD_wbits ht]
    unfold stepDWbits
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · rw [stepD_mblock ht]
    unfold stepDMeta metaGo
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) |
      (intro _ h2; exact absurd ht h2))
  · rw [stepD_skip ht]
    unfold stepDSkip moveOn
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · rw [stepD_raw ht]
    unfold stepDRaw takeRing moveOn rawFinish clearCmd
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)) | (intro _ _; assumption))
  · rw [stepD_hdr ht]
    unfold stepDHdr takeHd clearHd hdrNext
    dsimp only
    repeat' (first | split_all | (intro h; exact absurd h (fun e => DStatus.noConfusion e)))
  · rw [stepD_cmds ht]
    obtain ⟨p, hrel⟩ := hinv.1
    have hf : (runCmdF D.H D.k a stop hs cmdBudget D.cmd D.pos (hinv.cmd ht)).status = .needsOutput →
        room D.k (runCmdF D.H D.k a stop hs cmdBudget D.cmd D.pos (hinv.cmd ht)).cap ≤
          (runCmdF D.H D.k a stop hs cmdBudget D.cmd D.pos (hinv.cmd ht)).pend := by
      cases p with
      | cmds w last m q => exact runCmdF_full hrel.2.2.2.1 cmdBudget hrel.2.2.2.2.1 (hinv.cmd ht)
      | _ => exact absurd (hrel.1.symm.trans ht) (fun e => DTag.noConfusion e)
    unfold stepDCmds takeCmd clearCmd
    dsimp only
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
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        exact ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩
      · rw [dite_eq_right hn]
        exact stepD_room he

/-- WBITS's step that goes on sets the window's log size the stream declares, in 10..24. -/
theorem stepDWbits_k {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf) (hp : pos.toNat ≤ stop.toNat) (hn : (stepDWbits a stop hs D pos).status = .next) :
    10 ≤ (stepDWbits a stop hs D pos).k.toNat ∧ (stepDWbits a stop hs D pos).k.toNat ≤ 24 := by
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
    show 10 ≤ (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
      (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toUSize.toNat ∧
      (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
      (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toUSize.toNat ≤ 24
    have ha2' : (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat ≤ 24 := ha2
    have ha1' : 10 ≤ (wbitsFast ⟨(refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).word,
        (refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp')).count⟩).a.toNat := ha1
    rw [word_toUSize (by omega)]
    exact ⟨ha1', ha2'⟩

/-- Handing out the bytes of a state that can hand them out: its work is the bytes it hands out, and five. -/
theorem flushW_win {D : Dec} (h : WinOk D) (buf : ByteArray) (space : Nat) :
    flushAllW D.k D.cmd buf space ≤ min D.cmd.pend.toNat space + 5 := by
  rcases h with h0 | ⟨_, hr, hl, -, hk⟩
  · rw [flushAllW]
    dsimp only
    rw [ite_eq_left (Or.inl h0)]
    omega
  · exact flushAllW_le hk _ _ _ hr.pos_lt (Nat.le_trans (Nat.le_add_right _ 16) hl)

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
    have e : stepD a stop hs D hinv = stepDWbits a stop hs D D.pos := stepD_wbits hw
    rw [runD, dite_eq_right he] at hn ⊢
    dsimp only at hn ⊢
    by_cases h1 : (stepD a stop hs D hinv).status = .next
    · rw [dite_eq_left h1] at hn ⊢
      have hw' : DRel D .wbits := by cases p <;> first | exact hrel | exact absurd hw (by rw [hrel.1]; exact fun e => DTag.noConfusion e)
      have ht1 : (stepD a stop hs D hinv).tag ≠ .wbits := by rw [e]; exact stepDWbits_tag (by rw [← e]; exact h1)
      have hk1 : 10 ≤ (stepD a stop hs D hinv).k.toNat ∧ (stepD a stop hs D hinv).k.toNat ≤ 24 := by
        rw [e]
        exact stepDWbits_k hw'.2.1 hinv.2 (by rw [← e]; exact h1)
      exact (runD_kr ⟨_, hinv.step he h1⟩ ht1 hk1).2.1
    · rw [dite_eq_right h1] at hn
      rw [e] at hn
      exact absurd hn stepDWbits_out
  · exact (runD_kr ⟨D, hinv⟩ hw ⟨hk hw, hrel.k24 hw⟩).2.1

/-! ### The decoder's loop -/

/-- The decoder's loop, against the potential: its steps are paid for by the potential, 2980 for each bit, 32 for each
byte and the window, and the step that stops it by at most 88 more, or, when it rejects or reports the limit, by the bits
and the bytes it may decode first, and 97. -/
theorem pay_runD {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} : ∀ (x : RunArg a stop hs) (p : SPhase),
    DRel x.D p → SInv p →
    ((runD a stop hs x.D x.inv).status = .next ∨ (runD a stop hs x.D x.inv).status = .needsInput ∨
        (runD a stop hs x.D x.inv).status = .needsOutput →
      Pays a stop p x.D x.D.pos (runD a stop hs x.D x.inv) (runDW a stop hs x.D x.inv)
        (winD x.D (runD a stop hs x.D x.inv) + stopCost (runD a stop hs x.D x.inv))) ∧
    ((runD a stop hs x.D x.inv).status = .bad ∨ (runD a stop hs x.D x.inv).status = .memory → ∃ L,
      x.D.cmd.pend.toNat + L ≤ (runD a stop hs x.D x.inv).cmd.pend.toNat ∧
      ((runD a stop hs x.D x.inv).status = .memory → (runD a stop hs x.D x.inv).cmd.pend.toNat = 0) ∧ ∀ t : List UInt8,
      runDW a stop hs x.D x.inv + hdrRate * ((stop.toNat - (runD a stop hs x.D x.inv).pos.toNat) * 8) +
        (stop.toNat - (runD a stop hs x.D x.inv).pos.toNat) ≤
        dpot p x.D + hdrRate * (x.D.bits a x.D.pos stop (bits t)).length + (stop.toNat - x.D.pos.toNat) + 32 *L +
          winD x.D (runD a stop hs x.D x.inv) + 97) := by
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
      refine ⟨fun _ => Pays.intro p (hrel.congr rfl rfl rfl rfl rfl rfl rfl rfl) ⟨[], rfl, rfl⟩ (Nat.le_refl _) hinv.2 id (fun t => ?_),
        fun h => ?_⟩
      · rw [e1, e2]
        have := stopCost_ge { D with status := .next }
        omega
      · rcases h with h | h <;> cases h
    · rw [dite_eq_right he, dite_eq_right he]
      dsimp only
      obtain ⟨s1, s2, s3⟩ := pay_stepD (hs := hs) (hinv := hinv) hrel hsi he hinv.2
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn, dite_eq_left hn]
        obtain ⟨q1, hR1, ho1, hp1, hp2, hsi1, hw1⟩ := s1 hn
        obtain ⟨i1, i2⟩ := ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩ q1 hR1 (hsi1 hsi)
        dsimp only at i1 i2
        have hwin : winD D (stepD a stop hs D hinv) +
            winD (stepD a stop hs D hinv) (runD a stop hs (stepD a stop hs D hinv) (hinv.step he hn)) ≤
            winD D (runD a stop hs (stepD a stop hs D hinv) (hinv.step he hn)) := by
          by_cases hz : D.cmd.ring.size = 0
          · by_cases hz1 : (stepD a stop hs D hinv).cmd.ring.size = 0
            · have e0 : winD D (stepD a stop hs D hinv) = 0 := by
                unfold winD
                rw [ite_eq_right (fun h => h.2 hz1)]
              have e1 : winD (stepD a stop hs D hinv) (runD a stop hs (stepD a stop hs D hinv) (hinv.step he hn)) =
                  winD D (runD a stop hs (stepD a stop hs D hinv) (hinv.step he hn)) := by
                unfold winD
                rw [hz, hz1]
              omega
            · obtain ⟨f1, f2⟩ := runD_ring ⟨_, hinv.step he hn⟩ q1 hR1 hz1
              dsimp only at f1 f2
              have e1 : winD (stepD a stop hs D hinv) (runD a stop hs (stepD a stop hs D hinv) (hinv.step he hn)) = 0 := by
                unfold winD
                rw [ite_eq_right (fun h => hz1 h.1)]
              rw [e1]
              unfold winD
              rw [ite_eq_left ⟨hz, hz1⟩, ite_eq_left ⟨hz, by rw [f1]; exact hz1⟩, f2]
              omega
          · have s := stepD_ringK (hs := hs) (hinv := hinv) hrel hz
            have hz1 : (stepD a stop hs D hinv).cmd.ring.size ≠ 0 := by rw [s.1]; exact hz
            unfold winD
            rw [ite_eq_right (fun h => hz h.1), ite_eq_right (fun h => hz1 h.1), ite_eq_right (fun h => hz h.1)]
            omega
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
          have hl1'' : (stepD a stop hs D hinv).cmd.pend.toNat = D.cmd.pend.toNat + l1.length := hl1'
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
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        exact ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩
      · rw [dite_eq_right hn]
        exact fun h => absurd h hn

/-- A round that pauses for output space with no room left, and hands all its bytes out within its space, hands out a
whole window less its slack. -/
theorem room_full {k cap pend : USize} {space : Nat} (hk : k.toNat ≤ 24) (h16 : 16 ≤ 2 ^ k.toNat) (hc : cap = capFor space)
    (hr : room k cap ≤ pend) (hs : pend.toNat ≤ space) : 2 ^ k.toNat ≤ pend.toNat + 16 := by
  have h1 := USize.le_iff_toNat_le.mp hr
  have hcN : cap.toNat = min space 16777216 + 1 := by
    rw [hc]
    unfold capFor
    exact usize_ofNat' (by omega)
  have hne : cap ≠ 0 := fun e => by
    rw [e, show (0 : USize).toNat = 0 from rfl] at hcN
    omega
  rw [room_toNat hk h16, ite_eq_right hne, hcN] at h1
  have : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  omega

end Brotli.Decoder
