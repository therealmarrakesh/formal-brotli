import Brotli.Decoder.Tables
import Brotli.Decoder.Work

/-!
# Where the limit binds

A reply that reports the memory limit reports as used the bytes up to where the limit was found to bind, and the demand of
those bytes alone is over the limit. A state in a header keeps what it has read of its meta-block, whatever bits follow:
the meta-block's start, and the header so far, whose tables are the arena. A step that reports the limit decides on the
bits up to its refill's end.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A header machine state, with what it has read of its meta-block: the meta-block's start `um` and the header so far `u`,
before the bits it holds. Whatever bits follow, the start reads as a compressed meta-block's, the header's reading in order
takes `u` to the state's place, and the header's tables so far are the arena, which may grow to `lim`. -/
structure HdLoc (h : Hd) (lim : UInt64) (last : Bool) (mlen : Nat) (g : Gh) (q : HPhase) (um u : List Bool) : Prop where
  rel : HRel h g q
  path : ∀ T, Reach hStepP (Gh.start, .cat .L) (u ++ T) (g, q) T
  start : ∀ F, metaStart (um ++ u ++ (BitBuffer.mk h.word h.count).held ++ F) =
    some (.data last mlen false, u ++ (BitBuffer.mk h.word h.count).held ++ F)
  tables : ∀ F, (hrest tableK Gh.start (.cat .L) (u ++ (BitBuffer.mk h.word h.count).held ++ F)).getD 0 =
    h.d.arena.size + (hrest tableK g q ((BitBuffer.mk h.word h.count).held ++ F)).getD 0
  max : h.d.arenaMax = lim

/-- A meta-block's bits whose header, as far as any of them go, needs tables within `L`. -/
def Cert (L : Nat) (b : List Bool) : Prop := ∀ P R, b = P ++ R → headerTables P ≤ L

/-- A meta-block's bits that a state in a header is reading: its start, the header so far, and the bits from the state on. -/
def InCur (a : ByteArray) (stop : USize) (t : List UInt8) (D : Dec) (pos : USize) (b : List Bool) : Prop :=
  D.tag = .hdr ∧ ∃ last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u ∧
    b = um ++ u ++ availBits D.hd.word D.hd.count a pos stop (bits t)

/-- Where a header state's meta-block began, seen from where a run began: in the header the run began in, or in one the run
entered, whose start the reading in order reaches. -/
def HdFrom (a : ByteArray) (stop : USize) (t : List UInt8) (D r : Dec) (pos : USize) : Prop :=
  (D.tag = .hdr ∧ ∀ last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u →
    ∃ last' mlen' g' q' u', HdLoc r.hd r.limit last' mlen' g' q' um u' ∧
      u ++ availBits D.hd.word D.hd.count a D.pos stop (bits t) = u' ++ availBits r.hd.word r.hd.count a pos stop (bits t)) ∨
  (∀ p, DRel D p → ∃ w st last mlen g q um u, HdLoc r.hd r.limit last mlen g q um u ∧
      Reach sStep p (D.bits a D.pos stop (bits t)) (.mblock w st) (um ++ u ++ availBits r.hd.word r.hd.count a pos stop (bits t)))

/-- Where the limit binds on the bits `h` gives: at WBITS, for the window, or in a header, for its next table. -/
def Binds (Ws : Option Nat) (L : Nat) (D : Dec) (h : List UInt8 → List Bool) : Prop :=
  (D.tag = .wbits ∧ ∀ s : List UInt8, ∃ kv rest, readWBITS (h s) = some (kv, rest) ∧ L < 2 ^ kv) ∨
  (D.tag = .hdr ∧ ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L ∧
    ∀ last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u → ∀ s : List UInt8,
      D.hd.d.arenaMax.toNat < D.hd.d.arena.size + (hrest tableK g q (h s)).getD 0)

/-- What a step does to where a header's meta-block began, and where it found the limit to bind: at its own state, on the
bits up to the position it reports. -/
structure StepX (Ws : Option Nat) (L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (D r : Dec) : Prop where
  hdr : r.status ≠ .memory → r.status ≠ .bad → r.tag = .hdr → HdFrom a stop t D r r.pos
  why : r.status = .memory → D.pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ 8 * r.pos.toNat + D.held.length ≤ 8 * D.pos.toNat + 64 ∧
    Binds Ws L D (fun s => D.held ++ (chunkBits a D.pos.toNat r.pos.toNat ++ bits s))
  cur : r.status ≠ .memory → r.status ≠ .bad → D.tag = .hdr → ∀ b, InCur a stop t D D.pos b →
    InCur a stop t r r.pos b ∨ Cert r.limit.toNat b
  fresh : r.status ≠ .memory → r.status ≠ .bad → D.tag = .mblock → r.bits a r.pos stop (bits t) ≠ D.bits a D.pos stop (bits t) →
    InCur a stop t r r.pos (D.bits a D.pos stop (bits t)) ∨ Cert r.limit.toNat (D.bits a D.pos stop (bits t))
  lim : r.status ≠ .memory → r.status ≠ .bad → D.tag ≠ .wbits → r.limit = D.limit

/-- A state at a position, reached from the place `z` with the bits `Z`: its place; in a header, its meta-block's start; and
every meta-block's start on the way that it has read past, whose header it is reading or which needs tables within its limit. -/
def Anch (z : SPhase) (Z : List Bool) (a : ByteArray) (stop : USize) (t : List UInt8) (D : Dec) (pos : USize) : Prop :=
  (∃ p, DRel D p ∧ Reach sStep z Z p (D.bits a pos stop (bits t))) ∧
  (D.tag = .hdr → ∃ w st last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u ∧
    Reach sStep z Z (.mblock w st) (um ++ u ++ availBits D.hd.word D.hd.count a pos stop (bits t))) ∧
  (∀ w st b q, Reach sStep z Z (.mblock w st) b → Reach sStep (.mblock w st) b q (D.bits a pos stop (bits t)) →
    b ≠ D.bits a pos stop (bits t) → InCur a stop t D pos b ∨ Cert D.limit.toNat b)

/-- No step of the reading in order goes to WBITS. -/
theorem sStep_ne_wbits {p q : SPhase} {bs c : List Bool} (h : sStep p bs = .next q c) : q ≠ .wbits := by
  rintro rfl
  rcases p with _ | ⟨w, st⟩ | ⟨w, st, last, _ | n⟩ | ⟨w, st, last, _ | n⟩ | ⟨w, st, last, mlen, g, p⟩ | ⟨w, last, m, p⟩ | st
  all_goals simp only [sStep, readIn, startPlace, afterBlock] at h
  all_goals (repeat' split at h)
  all_goals (first | cases h | simp at h)

/-- Only WBITS reaches WBITS, and with the bits it had. -/
theorem reach_to_wbits {p : SPhase} {bs c : List Bool} (h : Reach sStep p bs .wbits c) : p = .wbits ∧ c = bs := by
  suffices ∀ q, Reach sStep p bs q c → q = .wbits → p = .wbits ∧ c = bs from this _ h rfl
  intro q h'
  clear h
  induction h' with
  | refl => exact fun e => ⟨e, rfl⟩
  | next hs _ ih => exact fun e => absurd (ih e).1 (sStep_ne_wbits hs)

/-- The places the reading in order reaches from one that holds the invariant hold it. -/
theorem sinv_of_reach {z q : SPhase} {Z c : List Bool} (hz : SInv z) (h : Reach sStep z Z q c) : SInv q := by
  obtain ⟨n, hn⟩ := h.count
  exact (steps_le hn hz).1

/-- The reading in order doesn't come back to where it was. -/
theorem reach_nocycle {q x : SPhase} {c y : List Bool} (hq : SInv q) (h1 : Reach sStep q c x y) (h2 : Reach sStep x y q c) :
    x = q ∧ y = c := by
  obtain ⟨n1, r1⟩ := h1.count
  obtain ⟨n2, r2⟩ := h2.count
  obtain ⟨_, _, _, hb⟩ := steps_le (r1.trans r2) hq
  have hn1 : n1 = 0 := by omega
  subst hn1
  cases r1 with
  | refl => exact ⟨rfl, rfl⟩

/-- A reading that passes no meta-block's start between its ends meets one only at its ends. -/
theorem SReach.noPass {p q m : SPhase} {B c b : List Bool} (hS : SReach p B q c) (h1 : Reach sStep p B m b)
    (h2 : Reach sStep m b q c) (hm : ∃ w st, m = .mblock w st) (hq : SInv q) : (m = p ∧ b = B) ∨ (m = q ∧ b = c) := by
  induction hS with
  | refl p B =>
    exact Or.inl (reach_nocycle hq h1 h2)
  | @next p0 q1 r0 b0 c1 d0 hs hq1 _ ih =>
    cases h1 with
    | refl => exact Or.inl ⟨rfl, rfl⟩
    | next hs' r1 =>
      rw [hs] at hs'
      cases hs'
      rcases ih r1 h2 hq with ⟨e1, e2⟩ | e
      · obtain ⟨w, st, rfl⟩ := hm
        subst e1
        obtain ⟨e3, e4⟩ := hq1 w st rfl
        exact Or.inr ⟨e3, e2.trans e4⟩
      · exact Or.inr e

/-- Reading a meta-block's start takes bits. -/
theorem mblock_consumes {w : Nat} {st : StreamState} {bs c : List Bool} {q : SPhase} (h : sStep (.mblock w st) bs = .next q c) :
    c.length < bs.length := by
  have hk : readIn 31 metaStart bs (startPlace w st) = .next q c := h
  cases e : metaStart bs with
  | none =>
    simp only [readIn, e] at hk
    split at hk <;> cases hk
  | some p =>
    obtain ⟨ms, b⟩ := p
    rw [readIn_some e] at hk
    obtain ⟨u, hu, _⟩ := (kfaith_startPlace w st ms).nfaith b q c hk
    obtain ⟨u0, hu0, hf⟩ := faith_metaStart bs ms b e
    have hne : u0 ≠ [] := by
      intro h0
      have h3 := hf []
      rw [h0, List.append_nil] at h3
      cases h3
    have l1 := congrArg List.length hu0
    have l2 := congrArg List.length hu
    rw [List.length_append] at l1 l2
    have : 0 < u0.length := List.length_pos_iff.mpr hne
    omega

/-- From a meta-block's start, a place with the same bits is that start. -/
theorem reach_mblock_same {w : Nat} {st : StreamState} {B : List Bool} {q : SPhase} (h : Reach sStep (.mblock w st) B q B) :
    q = .mblock w st := by
  cases h with
  | refl => rfl
  | next hs r =>
    have l1 := mblock_consumes hs
    obtain ⟨v, hv⟩ := reach_suffix nfaith_sStep r
    have l2 := congrArg List.length hv
    rw [List.length_append] at l2
    omega

/-- A state's place, for a state at WBITS. -/
theorem DRel.wbits_place {D : Dec} {p : SPhase} (h : DRel D p) (ht : D.tag = .wbits) : p = .wbits := by
  cases p with
  | wbits => rfl
  | mblock => exact absurd (h.1.symm.trans ht) (by decide)
  | skip => exact absurd (h.1.symm.trans ht) (by decide)
  | raw => exact absurd (h.1.symm.trans ht) (by decide)
  | hdr => exact absurd (h.1.symm.trans ht) (by decide)
  | cmds => exact absurd (h.1.symm.trans ht) (by decide)
  | ended => exact absurd (h.1.symm.trans ht) (by decide)

/-- A move keeps a state reached from `z`. -/
theorem Anch.move {z : SPhase} {Z : List Bool} {a : ByteArray} {stop : USize} {t : List UInt8} {D r : Dec} {pos : USize}
    (hz : SInv z) (h : Anch z Z a stop t D D.pos)
    (hr : ∀ p, DRel D p → ∃ p', DRel r p' ∧ SReach p (D.bits a D.pos stop (bits t)) p' (r.bits a pos stop (bits t)))
    (hf : r.tag = .hdr → HdFrom a stop t D r pos)
    (hcur : D.tag = .hdr → ∀ b, InCur a stop t D D.pos b → InCur a stop t r pos b ∨ Cert r.limit.toNat b)
    (hfresh : D.tag = .mblock → r.bits a pos stop (bits t) ≠ D.bits a D.pos stop (bits t) →
      InCur a stop t r pos (D.bits a D.pos stop (bits t)) ∨ Cert r.limit.toNat (D.bits a D.pos stop (bits t)))
    (hlim : D.tag ≠ .wbits → r.limit = D.limit) : Anch z Z a stop t r pos := by
  obtain ⟨⟨p, hp, hzp⟩, hh, hd⟩ := h
  obtain ⟨p', hp', hr'⟩ := hr p hp
  have hzp' : Reach sStep z Z p' (r.bits a pos stop (bits t)) := hzp.trans hr'.toReach
  have hsp' : SInv p' := sinv_of_reach hz hzp'
  refine ⟨⟨p', hp', hzp'⟩, fun ht => ?_, fun w st b q hzm hmq hne => ?_⟩
  · rcases hf ht with ⟨hD, hA⟩ | hB
    · obtain ⟨w, st, last, mlen, g, q, um, u, hL, hm⟩ := hh hD
      obtain ⟨last', mlen', g', q', u', hL', he⟩ := hA last mlen g q um u hL
      refine ⟨w, st, last', mlen', g', q', um, u', hL', ?_⟩
      rw [List.append_assoc, ← he, ← List.append_assoc]
      exact hm
    · obtain ⟨w, st, last, mlen, g, q, um, u, hL, hm⟩ := hB p hp
      exact ⟨w, st, last, mlen, g, q, um, u, hL, hzp.trans hm⟩
  · -- The meta-block's start lies at or before the state's old place, or between the old place and the new.
    have hfr : p = .mblock w st → b = D.bits a D.pos stop (bits t) → InCur a stop t r pos b ∨ Cert r.limit.toNat b := by
      intro e1 e2
      subst e1 e2
      exact hfresh hp.1 (fun e => hne e.symm)
    rcases Reach.total hzm hzp with e1 | e1
    · by_cases hb : b = D.bits a D.pos stop (bits t)
      · have e1' := e1
        rw [hb] at e1'
        exact hfr (reach_mblock_same e1') hb
      rcases hd w st b p hzm e1 hb with hc | hc
      · exact hcur hc.1 b hc
      · have hnw : D.tag ≠ .wbits := fun ew => by
          have := hp.wbits_place ew
          subst this
          exact absurd (reach_to_wbits e1).1 (fun e => SPhase.noConfusion e)
        rw [hlim hnw]
        exact Or.inr hc
    · rcases Reach.total e1 hr'.toReach with e2 | e2
      · rcases hr'.noPass e1 e2 ⟨w, st, rfl⟩ hsp' with ⟨e3, e4⟩ | ⟨_, e4⟩
        · exact hfr e3.symm e4
        · exact absurd e4 hne
      · obtain ⟨v1, hv1⟩ := reach_suffix nfaith_sStep hmq
        obtain ⟨v2, hv2⟩ := reach_suffix nfaith_sStep e2
        have l1 := congrArg List.length hv1
        have l2 := congrArg List.length hv2
        rw [List.length_append] at l1 l2
        have : v1 = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        exact absurd hv1 hne

/-- The bits a header state holds. -/
theorem Dec.held_hdr {D : Dec} (h : D.tag = .hdr) : D.held = (BitBuffer.mk D.hd.word D.hd.count).held := by
  unfold Dec.held Dec.word Dec.count
  rw [h]

/-- A header's tables, as far as bits short of a header state's go: within the state's limit. -/
theorem cert_within {h : Hd} {lim : UInt64} {last : Bool} {mlen : Nat} {g : Gh} {q : HPhase} {um u : List Bool}
    (hL : HdLoc h lim last mlen g q um u) {X P R : List Bool}
    (hb : um ++ u ++ (BitBuffer.mk h.word h.count).held ++ X = P ++ R) (hlt : ((BitBuffer.mk h.word h.count).held ++ X).length < R.length) :
    headerTables P ≤ lim.toNat := by
  refine headerTables_le_of (hL.start X) hb (fun r' hr' => ?_)
  have hp := hL.path ((BitBuffer.mk h.word h.count).held ++ X)
  rw [← List.append_assoc, hr'] at hp
  have hw := tables_within hp hlt
  dsimp only at hw
  rw [← hr', hL.tables X] at hw
  have hle := hL.rel.2.1.le
  rw [hL.max] at hle
  omega

/-- A finished header's tables, as far as any of its bits go: within the limit of the state that finished it. -/
theorem cert_ready {h : Hd} {lim : UInt64} {last : Bool} {mlen : Nat} {g : Gh} {q : HPhase} {um u : List Bool}
    (hL : HdLoc h lim last mlen g q um u) {X : List Bool}
    (hex : ∃ e F', hStepP (g, q) ((BitBuffer.mk h.word h.count).held ++ X) = .exit e F') :
    Cert lim.toNat (um ++ u ++ (BitBuffer.mk h.word h.count).held ++ X) := by
  intro P R hb
  by_cases hlt : ((BitBuffer.mk h.word h.count).held ++ X).length < R.length
  · exact cert_within hL hb hlt
  refine headerTables_le_of (hL.start X) hb (fun r' hr' => ?_)
  obtain ⟨S, u0, hu0, hS⟩ := chain_tables (hL.path [])
  rw [List.append_nil, List.append_nil] at hu0
  subst hu0
  have hS0 := hS ((BitBuffer.mk h.word h.count).held ++ X)
  rw [← List.append_assoc, hL.tables X] at hS0
  have hle := hL.rel.2.1.le
  rw [hL.max] at hle
  -- the bits cut off lie past the header so far
  rw [List.append_assoc] at hr'
  obtain ⟨Y, hY1, hY2⟩ : ∃ Y, r' = u ++ Y ∧ (BitBuffer.mk h.word h.count).held ++ X = Y ++ R := by
    rcases List.append_eq_append_iff.mp hr' with ⟨a', e1, e2⟩ | ⟨c', e1, e2⟩
    · exact ⟨a', e1, e2⟩
    · have l := congrArg List.length e2
      rw [List.length_append] at l
      have : c' = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact ⟨[], by rw [e1, List.append_nil, List.append_nil], by rw [e2, List.nil_append, List.nil_append]⟩
  subst hY1
  have hst : ∀ q' r, hStepP (g, q) Y ≠ .next q' r := by
    intro q' r hn
    obtain ⟨u1, hu1, hk⟩ := (ufaith_hStep g q).1 Y q' r hn
    have h3 := hk (r ++ R)
    rw [← List.append_assoc, ← hu1, ← hY2] at h3
    obtain ⟨e, F', he⟩ := hex
    rw [he] at h3
    cases h3
  have hv := hS Y
  rw [tables_stuck hst] at hv
  dsimp only at hS0 hv
  omega

/-! ### A header's steps -/

/-- A header step's state, in a header still: what it has read of its meta-block grows by what the step read. -/
theorem stepDHdr_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8}
    {D : Dec} (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .hdr) (hp : D.pos.toNat ≤ stop.toNat) :
    StepX Ws L a stop t D (stepDHdr a stop hs D D.pos) := by
  have hwin := M.win
  have hb0 := Dec.bits_hdr ht a D.pos stop (bits t)
  have hh0 := Dec.held_hdr ht
  have hN := fun g q (hR : HRel D.hd g q) => stepH_next (K := tableK) (a := a) (hs := hs) hR hp
  have hI := fun g q (hR : HRel D.hd g q) => stepH_ok (K := tableK) (a := a) (hs := hs) hR hp
  have hMm := fun g q (hR : HRel D.hd g q) => stepH_memory (K := tableK) (a := a) (hs := hs) hR hp
  unfold stepDHdr takeHd
  dsimp only
  generalize stepH a stop hs D.hd D.pos = rh at hN hI hMm
  cases hst : rh.status with
  | next =>
    dsimp only
    have hA : ∀ last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u → ∃ last' mlen' g' q' u',
        HdLoc rh D.limit last' mlen' g' q' um u' ∧
        u ++ availBits D.hd.word D.hd.count a D.pos stop (bits t) = u' ++ availBits rh.word rh.count a rh.pos stop (bits t) := by
      intro last mlen g q um u hL
      obtain ⟨g', p', oc, hR', hM', h1, h2, hW, hJ1⟩ := hN g q hL.rel hst
      have hJ := fun F => Reach.one (step := hStepP) (hJ1 F)
      obtain ⟨v, hv⟩ := reach_suffix (step := hStepP) (fun q => (kfaith_hStep q.1 q.2).nfaith) (hJ [])
      have hv' : (BitBuffer.mk D.hd.word D.hd.count).held ++ chunkBits a D.pos.toNat rh.pos.toNat =
          v ++ (BitBuffer.mk rh.word rh.count).held := by
        rw [avail_mk, List.append_nil, List.append_nil] at hv
        exact hv
      have hv2 : ∀ F, (BitBuffer.mk D.hd.word D.hd.count).held ++ (chunkBits a D.pos.toNat rh.pos.toNat ++ F) =
          v ++ ((BitBuffer.mk rh.word rh.count).held ++ F) := by
        intro F
        rw [← List.append_assoc, hv', List.append_assoc]
      have hsplit : chunkBits a D.pos.toNat stop.toNat = chunkBits a D.pos.toNat rh.pos.toNat ++ chunkBits a rh.pos.toNat stop.toNat :=
        chunkBits_split a h1 h2
      have hLoc : HdLoc rh D.limit last mlen g' p' um (u ++ v) := by
        refine ⟨hR', fun T => ?_, fun F => ?_, fun F => ?_, ?_⟩
        · obtain ⟨u0, hu0, hr0⟩ := reach_retail (hJ [])
          have e0 : u0 = v := by
            have := hu0.symm.trans hv
            rw [List.append_nil] at this
            exact List.append_cancel_right this
          rw [e0] at hr0
          rw [List.append_assoc]
          exact (hL.path (v ++ T)).trans (hr0 T)
        · have e := hL.start (chunkBits a D.pos.toNat rh.pos.toNat ++ F)
          simp only [List.append_assoc] at e ⊢
          rw [hv2] at e
          exact e
        · have e1 := hL.tables (chunkBits a D.pos.toNat rh.pos.toNat ++ F)
          have e2 := congrArg (Option.getD · 0) (hW F)
          rw [avail_mk] at e2
          simp only [wr_tableK] at e2
          simp only [List.append_assoc] at e1 ⊢
          rw [← hv2, e1, e2, hM'.grow, Nat.add_assoc]
        · rw [hM'.max]
          exact hL.max
      refine ⟨last, mlen, g', p', u ++ v, hLoc, ?_⟩
      rw [avail_mk, avail_mk, hsplit, List.append_assoc (chunkBits _ _ _), hv2, List.append_assoc]
    refine ⟨fun _ _ _ => Or.inl ⟨ht, hA⟩, fun e => DStatus.noConfusion e, fun _ _ _ b hc => Or.inl ?_,
      fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => rfl⟩
    obtain ⟨_, last, mlen, g, q, um, u, hL, hb⟩ := hc
    obtain ⟨last', mlen', g', q', u', hL', he⟩ := hA last mlen g q um u hL
    exact ⟨ht, last', mlen', g', q', um, u', hL', by rw [hb, List.append_assoc, he, ← List.append_assoc]⟩
  | needsInput =>
    dsimp only
    have hA : ∀ last mlen g q um u, HdLoc D.hd D.limit last mlen g q um u → ∃ last' mlen' g' q' u',
        HdLoc rh D.limit last' mlen' g' q' um u' ∧
        u ++ availBits D.hd.word D.hd.count a D.pos stop (bits t) = u' ++ availBits rh.word rh.count a rh.pos stop (bits t) := by
      intro last mlen g q um u hL
      obtain ⟨h1, _, hR', _, _, hM', hb, _⟩ := (hI g q hL.rel).needsInput hst
      have hheld : (BitBuffer.mk rh.word rh.count).held = (BitBuffer.mk D.hd.word D.hd.count).held ++ chunkBits a D.pos.toNat stop.toNat := by
        have e := hb []
        rw [avail_mk, avail_mk, h1, chunkBits_self, List.nil_append, List.append_nil, List.append_nil] at e
        exact e
      have hg0 : rh.d.arena.size = D.hd.d.arena.size := by
        rw [hM'.grow]
        rfl
      have hLoc : HdLoc rh D.limit last mlen g q um u := by
        refine ⟨hR', hL.path, fun F => ?_, fun F => ?_, ?_⟩
        · have e := hL.start (chunkBits a D.pos.toNat stop.toNat ++ F)
          rw [hheld]
          simp only [List.append_assoc] at e ⊢
          exact e
        · have e := hL.tables (chunkBits a D.pos.toNat stop.toNat ++ F)
          rw [hheld, hg0]
          simp only [List.append_assoc] at e ⊢
          exact e
        · rw [hM'.max]
          exact hL.max
      refine ⟨last, mlen, g, q, u, hLoc, ?_⟩
      rw [avail_mk, avail_mk, hheld, h1, chunkBits_self, List.nil_append, List.append_assoc]
    refine ⟨fun _ _ _ => Or.inl ⟨ht, hA⟩, fun e => DStatus.noConfusion e, fun _ _ _ b hc => Or.inl ?_,
      fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => rfl⟩
    obtain ⟨_, last, mlen, g, q, um, u, hL, hb⟩ := hc
    obtain ⟨last', mlen', g', q', u', hL', he⟩ := hA last mlen g q um u hL
    exact ⟨ht, last', mlen', g', q', um, u', hL', by rw [hb, List.append_assoc, he, ← List.append_assoc]⟩
  | bad => exact ⟨fun _ e => absurd rfl e, fun e => DStatus.noConfusion e, fun _ e => absurd rfl e, fun _ e => absurd rfl e,
      fun _ e => absurd rfl e⟩
  | memory =>
    dsimp only
    refine ⟨fun e => absurd rfl e, fun _ => ?_, fun e => absurd rfl e, fun e => absurd rfl e, fun e => absurd rfl e⟩
    obtain ⟨g0, q0, hR0, _⟩ := M.hdr ht
    obtain ⟨m1, m2, m3, _⟩ := hMm g0 q0 hR0 hst
    refine ⟨m1, m2, ?_, Or.inr ⟨ht, ?_⟩⟩
    · rw [hh0, BitBuffer.held_length]
      exact m3
    · rcases hwin with ⟨e, _⟩ | ⟨_, w, g1, g2, g3⟩
      · exact absurd (ht.symm.trans e) (by decide)
      refine ⟨w, g1, g2, g3, fun last mlen g q um u hL s => ?_⟩
      obtain ⟨_, _, _, ⟨c, c1, _, _, c4⟩⟩ := hMm g q hL.rel hst
      obtain ⟨x, hx⟩ := c4 (bits s)
      rw [avail_mk] at hx
      show D.hd.d.arenaMax.toNat < D.hd.d.arena.size + (hrest tableK g q (D.held ++ (chunkBits a D.pos.toNat rh.pos.toNat ++ bits s))).getD 0
      rw [hh0, hx]
      show _ < _ + (tableBytes c + x.getD 0)
      omega
  | ready =>
    dsimp only
    split
    · refine ⟨fun _ _ e => DTag.noConfusion e, fun e => DStatus.noConfusion e, fun _ _ _ b hc => Or.inr ?_,
        fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => rfl⟩
      obtain ⟨_, last, mlen, g, q, um, u, hL, hb⟩ := hc
      obtain ⟨_, _, _, _, _, _, _, _, _, hx⟩ := (hI g q hL.rel).ready hst
      have hc := cert_ready (X := chunkBits a D.pos.toNat stop.toNat ++ bits t) hL ⟨_, _, hx (bits t)⟩
      rw [List.append_assoc] at hc
      rw [hb]
      exact hc
    · exact ⟨fun _ hb _ => absurd rfl hb, fun e => DStatus.noConfusion e, fun _ e => absurd rfl e, fun _ e => absurd rfl e,
        fun _ e => absurd rfl e⟩

/-! ### The other steps -/

/-- The bits a state at WBITS holds. -/
theorem Dec.held_wbits {D : Dec} (h : D.tag = .wbits) : D.held = (BitBuffer.mk D.cmd.word D.cmd.count).held := by
  unfold Dec.held Dec.word Dec.count
  rw [h]

/-- A meta-block's start, entering a header: the header's meta-block begins at the start the step read. -/
theorem stepDMeta_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8}
    {D : Dec} (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .mblock) (hp : D.pos.toNat ≤ stop.toNat) :
    StepX Ws L a stop t D (stepDMeta a stop hs D D.pos) := by
  obtain ⟨p, hrel, _⟩ := M.place
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock w st =>
    have hF := stepDMeta_facts (a := a) (hs := hs) hrel hp
    have hD := stepDMeta_ok (S := specSem) (a := a) (hs := hs) hrel hp
    generalize stepDMeta a stop hs D D.pos = r at hF hD
    have hLocOf : r.tag = .hdr → ∃ last mlen um, HdLoc r.hd r.limit last mlen Gh.start (.cat .L) um [] ∧
        D.bits a D.pos stop (bits t) = um ++ availBits r.hd.word r.hd.count a r.pos stop (bits t) := by
      intro hth
      obtain ⟨_, s2, s3, s4, s5, _⟩ := hF.start hth
      obtain ⟨last, mlen, hm⟩ := s2 t
      obtain ⟨um, hu, hf⟩ := faith_metaStart _ _ _ hm
      rw [Dec.bits_hdr hth] at hu
      refine ⟨last, mlen, um, ⟨s3, fun T => .refl _ _, fun F => ?_, fun F => ?_, ?_⟩, hu⟩
      · rw [List.append_nil, List.nil_append, List.append_assoc]
        exact hf _
      · rw [List.nil_append, s4, Nat.zero_add]
      · rw [s5, hF.limit]
    refine ⟨fun _ _ hth => Or.inr fun p' hp' => ?_, fun e => absurd e hF.status, fun _ _ e => absurd (ht.symm.trans e) (by decide),
      fun h0 h1 _ hne => ?_, fun _ _ _ => hF.limit⟩
    rotate_right
    · by_cases hth : r.tag = .hdr
      · obtain ⟨last, mlen, um, hL, hu⟩ := hLocOf hth
        exact Or.inl ⟨hth, last, mlen, Gh.start, .cat .L, um, [], hL, by rw [hu, List.append_nil]⟩
      · cases hs0 : r.status with
        | next =>
          obtain ⟨v, rest, hm, hv⟩ := hF.plain hs0 hth t
          exact Or.inr fun P R hb => by rw [headerTables_none hm hv hb]; exact Nat.zero_le _
        | needsInput =>
          obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := hD.needsInput hs0
          exact absurd (hb w st rfl t) hne
        | needsOutput =>
          obtain ⟨_, _, _, _, _, _, _, hb, _⟩ := hD.needsOutput hs0
          exact absurd (hb w st rfl t) hne
        | memory => exact absurd hs0 h0
        | bad => exact absurd hs0 h1
    obtain ⟨last, mlen, um, hL, hu⟩ := hLocOf hth
    have hp'm : ∃ w' st', p' = .mblock w' st' := by
      cases p' with
      | mblock => exact ⟨_, _, rfl⟩
      | wbits => exact absurd (hp'.1.symm.trans ht) (by decide)
      | skip => exact absurd (hp'.1.symm.trans ht) (by decide)
      | raw => exact absurd (hp'.1.symm.trans ht) (by decide)
      | hdr => exact absurd (hp'.1.symm.trans ht) (by decide)
      | cmds => exact absurd (hp'.1.symm.trans ht) (by decide)
      | ended => exact absurd (hp'.1.symm.trans ht) (by decide)
    obtain ⟨w', st', rfl⟩ := hp'm
    refine ⟨w', st', last, mlen, Gh.start, .cat .L, um, [], hL, ?_⟩
    rw [List.append_nil, ← hu]
    exact .refl _ _

/-- WBITS's step: the window it declares doesn't fit, on the bits up to the position it reports. -/
theorem stepDWbits_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8}
    {D : Dec} (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .wbits) (hp : D.pos.toNat ≤ stop.toNat) :
    StepX Ws L a stop t D (stepDWbits a stop hs D D.pos) := by
  have hL : D.limit.toNat = L := by
    rcases M.win with ⟨_, _, _, _, h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd ht h
  obtain ⟨p, hrel, _⟩ := M.place
  have hp0 : p = .wbits := by
    cases p with
    | wbits => rfl
    | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  subst hp0
  have hF := stepDWbits_facts (a := a) (hs := hs) hrel hp
  have hh := Dec.held_wbits ht
  generalize stepDWbits a stop hs D D.pos = r at hF
  refine ⟨fun _ _ hth => ?_, fun e => ?_, fun _ _ e => absurd (ht.symm.trans e) (by decide),
    fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ e => absurd ht e⟩
  · by_cases hn : r.status = .next
    · exact absurd ((hF.next hn).1.symm.trans hth) (by decide)
    · exact absurd (ht.symm.trans ((hF.paused hn).1.symm.trans hth)) (by decide)
  · obtain ⟨m1, m2, m3, m4⟩ := hF.memAt e
    refine ⟨m1, m2, by rw [hh, BitBuffer.held_length]; exact m3, Or.inl ⟨ht, fun s => ?_⟩⟩
    obtain ⟨kv, rest, e1, e2⟩ := m4 s
    exact ⟨kv, rest, by rw [hh]; exact e1, by rw [← hL]; exact e2⟩

theorem stepDSkip_x {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D : Dec} (ht : D.tag = .skip) :
    StepX Ws L a stop t D (stepDSkip stop D D.pos) := by
  obtain ⟨_, k2, _, _, k5, _, _, k8, _⟩ := stepDSkip_keeps stop D D.pos ht
  exact ⟨fun _ _ e => absurd e k8, fun e => absurd e k5, fun _ _ e => absurd (ht.symm.trans e) (by decide),
    fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => k2⟩

theorem stepDRaw_x {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} {D : Dec}
    (ht : D.tag = .raw) : StepX Ws L a stop t D (stepDRaw a stop hs D D.pos) := by
  obtain ⟨_, k2, _, _, k5, _, _, k8, _⟩ := stepDRaw_keeps a stop hs D D.pos ht
  exact ⟨fun _ _ e => absurd e k8, fun e => absurd e k5, fun _ _ e => absurd (ht.symm.trans e) (by decide),
    fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => k2⟩

theorem stepDCmds_x {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} {D : Dec}
    (ht : D.tag = .cmds) : StepX Ws L a stop t D (stepDCmds a stop hs D D.pos) := by
  obtain ⟨_, k2, _, k4, _, k6⟩ := stepDCmds_keeps a stop hs D D.pos
  refine ⟨fun _ _ e => ?_, fun e => absurd e k4, fun _ _ e => absurd (ht.symm.trans e) (by decide),
    fun _ _ e => absurd (ht.symm.trans e) (by decide), fun _ _ _ => k2⟩
  rcases k6 with ⟨t1, _⟩ | ⟨_, t2, _, _⟩
  · exact absurd (ht.symm.trans (t1.symm.trans e)) (by decide)
  · exact absurd e t2

/-- A step of the stream. -/
theorem stepD_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} {D : Dec}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) :
    StepX Ws L a stop t D (stepD a stop hs D) := by
  unfold stepD
  cases ht : D.tag with
  | wbits => exact stepDWbits_x M ht hp
  | mblock => exact stepDMeta_x M ht hp
  | skip => exact stepDSkip_x ht
  | raw => exact stepDRaw_x ht
  | hdr => exact stepDHdr_x M ht hp
  | cmds => exact stepDCmds_x ht
  | ended => exact absurd ht he

/-- A step that neither rejects nor finds the limit moves on in the reading in order, passing no meta-block's start. -/
theorem DStepOk.reach {α : Type} {S : Sem α} {a : ByteArray} {stop : USize} {p : SPhase} {D r : Dec} {pos : USize}
    (h : DStepOk S a stop p D pos r) (h0 : r.status ≠ .memory) (h1 : r.status ≠ .bad) :
    ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ ∀ t : List UInt8, SReach p (D.bits a pos stop (bits t)) p' (r.bits a r.pos stop (bits t)) := by
  cases hs : r.status with
  | next =>
    obtain ⟨p', a1, a2, _, _, _, _, a7⟩ := h.next hs
    exact ⟨p', a1, a2, a7⟩
  | needsInput =>
    obtain ⟨b1, b2, p', a1, _, _, _, _, _, a7, _⟩ := h.needsInput hs
    exact ⟨p', a1, by rw [b1]; exact b2, a7⟩
  | needsOutput =>
    obtain ⟨p', a1, a2, _, _, _, _, _, _, a9⟩ := h.needsOutput hs
    exact ⟨p', a1, a2, a9⟩
  | memory => exact absurd hs h0
  | bad => exact absurd hs h1

/-! ### The loop and a call -/

/-- What the loop or a call does to a state reached from `z`, and where it found the limit to bind. -/
structure RunX (Ws : Option Nat) (L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (D r : Dec) : Prop where
  go : r.status ≠ .memory → r.status ≠ .bad → ∀ z Z, SInv z → Anch z Z a stop t D D.pos → Anch z Z a stop t r r.pos
  why : r.status = .memory → D.pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ ∀ z Z, SInv z → Anch z Z a stop t D D.pos →
    ∃ (D1 : Dec) (pos1 : USize), D.pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ r.pos.toNat ∧ 8 * r.pos.toNat + D1.held.length ≤ 8 * pos1.toNat + 64 ∧
      Anch z Z a stop t D1 pos1 ∧ Binds Ws L D1 (fun s => D1.held ++ (chunkBits a pos1.toNat r.pos.toNat ++ bits s))
  ended : D.tag = .ended → r.status = .next ∧ r.tag = .ended

/-- The loop. -/
theorem runD_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} : ∀ x : RunArg a stop hs,
    MemD Ws X L x.D (x.D.bits a x.D.pos stop (bits t)) → RunX Ws L a stop t x.D (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    intro M
    obtain ⟨D, hinv⟩ := x
    dsimp only at M ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact ⟨fun _ _ z Z hz h => Anch.move hz h (fun p hp => ⟨p, hp.congr rfl rfl rfl rfl rfl rfl rfl rfl, .refl _ _⟩)
        (fun e => absurd (he.symm.trans e) (by decide)) (fun e => absurd (he.symm.trans e) (by decide))
        (fun e => absurd (he.symm.trans e) (by decide)) (fun _ => rfl), fun e => DStatus.noConfusion e, fun _ => ⟨rfl, he⟩⟩
    · rw [dite_eq_right he]
      dsimp only
      have hstep := stepD_x (hs := hs) (t := t) M he hinv.2
      have hok := fun p (hrel : DRel D p) => stepD_ok specSem (a := a) (hs := hs) hrel he hinv.2
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        have hM := (stepD_mem (hs := hs) M he hinv.2).go (by rw [hn]; decide) (by rw [hn]; decide)
        have hih := ih ⟨stepD a stop hs D, hinv.step he hn⟩ ⟨he, hn, rfl⟩ hM
        dsimp only at hih
        obtain ⟨p0, hrel0, _⟩ := M.place
        obtain ⟨_, _, hpos, _⟩ := (hok p0 hrel0).reach (by rw [hn]; decide) (by rw [hn]; decide)
        have hn0 : (stepD a stop hs D).status ≠ .memory := by rw [hn]; decide
        have hn1 : (stepD a stop hs D).status ≠ .bad := by rw [hn]; decide
        have h1 : ∀ z Z, SInv z → Anch z Z a stop t D D.pos → Anch z Z a stop t (stepD a stop hs D) (stepD a stop hs D).pos := fun z Z hz h =>
          Anch.move hz h (fun p hrel => by
            obtain ⟨p', b1, _, b3⟩ := (hok p hrel).reach hn0 hn1
            exact ⟨p', b1, b3 t⟩) (hstep.hdr hn0 hn1) (hstep.cur hn0 hn1) (hstep.fresh hn0 hn1) (hstep.lim hn0 hn1)
        generalize runD a stop hs (stepD a stop hs D) (hinv.step he hn) = r at hih ⊢
        refine ⟨fun h0 h1' z Z hz h => hih.go h0 h1' z Z hz (h1 z Z hz h), fun e => ?_, fun e => absurd e he⟩
        obtain ⟨m1, m2, m3⟩ := hih.why e
        refine ⟨Nat.le_trans hpos m1, m2, fun z Z hz h => ?_⟩
        obtain ⟨D1, pos1, b1, b2, b3, b4, b5⟩ := m3 z Z hz (h1 z Z hz h)
        exact ⟨D1, pos1, Nat.le_trans hpos b1, b2, b3, b4, b5⟩
      · rw [dite_eq_right hn]
        refine ⟨fun h0 h1 z Z hz h => Anch.move hz h (fun p hrel => ?_) (hstep.hdr h0 h1) (hstep.cur h0 h1) (hstep.fresh h0 h1)
          (hstep.lim h0 h1), fun e => ?_, fun e => absurd e he⟩
        · obtain ⟨p', b1, _, b3⟩ := (hok p hrel).reach h0 h1
          exact ⟨p', b1, b3 t⟩
        · obtain ⟨m1, m2, m3, m4⟩ := hstep.why e
          exact ⟨m1, m2, fun z Z _ h => ⟨D, D.pos, Nat.le_refl _, m1, m3, h, m4⟩⟩

/-- The cap on waiting bytes changes nothing about a state reached from `z`. -/
theorem Anch.withCap {z : SPhase} {Z : List Bool} {a : ByteArray} {stop : USize} {t : List UInt8} {D : Dec}
    (h : Anch z Z a stop t D D.pos) (space : Nat) : Anch z Z a stop t (withCap D space) (withCap D space).pos := by
  obtain ⟨⟨p, hp, hz⟩, hh, hd⟩ := h
  exact ⟨⟨p, hp.withCap _, hz⟩, hh, hd⟩

/-- Handing out a state's bytes changes nothing about a state reached from `z`. -/
theorem Anch.flush {z : SPhase} {Z : List Bool} {a : ByteArray} {stop : USize} {t : List UInt8} {r : Dec}
    (h : Anch z Z a stop t r r.pos) (buf : ByteArray) (space : Nat) :
    Anch z Z a stop t (flushD r buf space).D (flushD r buf space).D.pos := by
  obtain ⟨⟨p, hp, hz⟩, hh, hd⟩ := h
  obtain ⟨_, _, _, _, a4, _, _, _, a8, _, a9, _⟩ := flushD_spec hp buf space
  rw [a8]
  refine ⟨⟨p, a4, by rw [a9]; exact hz⟩, hh, fun w st b q h1 h2 h3 => ?_⟩
  rw [a9] at h2 h3
  exact hd w st b q h1 h2 h3

theorem RunX.uncap {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D r : Dec} {space : Nat}
    (h : RunX Ws L a stop t (withCap D space) r) : RunX Ws L a stop t D r :=
  ⟨fun h0 h1 z Z hz hA => h.go h0 h1 z Z hz (hA.withCap space), fun e => by
    obtain ⟨m1, m2, m3⟩ := h.why e
    exact ⟨m1, m2, fun z Z hz hA => m3 z Z hz (hA.withCap space)⟩, h.ended⟩

/-- What a call does to a state reached from `z`, and where it found the limit to bind. A call from the stream's end stays
there. -/
structure CallX (Ws : Option Nat) (L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (D : Dec) (o : Out) : Prop where
  go : o.status.stopped = false → o.D.tag ≠ .ended → ∀ z Z, SInv z → Anch z Z a stop t D D.pos → Anch z Z a stop t o.D o.pos
  why : o.status = .memoryLimit → D.pos.toNat ≤ o.pos.toNat ∧ o.pos.toNat ≤ stop.toNat ∧ ∀ z Z, SInv z → Anch z Z a stop t D D.pos →
    ∃ (D1 : Dec) (pos1 : USize), D.pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ o.pos.toNat ∧ 8 * o.pos.toNat + D1.held.length ≤ 8 * pos1.toNat + 64 ∧
      Anch z Z a stop t D1 pos1 ∧ Binds Ws L D1 (fun s => D1.held ++ (chunkBits a pos1.toNat o.pos.toNat ++ bits s))
  ended : D.tag = .ended → o.status ≠ .memoryLimit ∧ (o.status.stopped = false → o.D.tag = .ended)

/-- The stream's end stays the stream's end and doesn't find the limit. -/
theorem endCheck_x {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D0 D : Dec} {final : Bool} (buf : ByteArray)
    (ht : D.tag = .ended) : CallX Ws L a stop t D0 (endCheck D stop final buf) := by
  unfold endCheck
  dsimp only
  by_cases hz : (BitBuffer.mk D.cmd.word D.cmd.count).peek (D.cmd.count &&& 7) = 0
  · rw [ite_eq_left hz]
    by_cases hc : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count = 0 ∧ D.pos = stop
    · rw [ite_eq_left hc]
      cases final with
      | true => exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun _ => ⟨fun e => Status.noConfusion e, fun e => Bool.noConfusion e⟩⟩
      | false => exact ⟨fun _ e => absurd ht e, fun e => Status.noConfusion e, fun _ => ⟨fun e => Status.noConfusion e, fun _ => ht⟩⟩
    · rw [ite_eq_right hc]
      exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun _ => ⟨fun e => Status.noConfusion e, fun e => Bool.noConfusion e⟩⟩
  · rw [ite_eq_right hz]
    exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun _ => ⟨fun e => Status.noConfusion e, fun e => Bool.noConfusion e⟩⟩

/-- What a call does with what the loop left. -/
theorem afterRun_x {Ws : Option Nat} {L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D r : Dec} {final : Bool}
    (hr : RunX Ws L a stop t D r) (hend : r.status = .next → r.tag = .ended) (buf : ByteArray) (space : Nat) :
    CallX Ws L a stop t D (afterRun r stop final buf space) := by
  unfold afterRun
  cases hst : r.status with
  | bad => exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun e => absurd ((hr.ended e).1.symm.trans hst) (by decide)⟩
  | memory => exact ⟨fun e => Bool.noConfusion e, fun _ => hr.why hst, fun e => absurd ((hr.ended e).1.symm.trans hst) (by decide)⟩
  | needsOutput => exact ⟨fun _ _ z Z hz h => hr.go (by rw [hst]; decide) (by rw [hst]; decide) z Z hz h, fun e => Status.noConfusion e,
      fun e => absurd ((hr.ended e).1.symm.trans hst) (by decide)⟩
  | needsInput =>
    have hA := fun z Z hz h => (hr.go (by rw [hst]; decide) (by rw [hst]; decide) z Z hz h).flush buf space
    have hE : D.tag = .ended → False := fun e => absurd ((hr.ended e).1.symm.trans hst) (by decide)
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      cases final with
      | true => exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun e => absurd e hE⟩
      | false => exact ⟨fun _ _ z Z hz h => hA z Z hz h, fun e => Status.noConfusion e, fun e => absurd e hE⟩
    · rw [ite_eq_right hz]
      exact ⟨fun _ _ z Z hz h => hA z Z hz h, fun e => Status.noConfusion e, fun e => absurd e hE⟩
  | next =>
    have hA := fun z Z hz h => (hr.go (by rw [hst]; decide) (by rw [hst]; decide) z Z hz h).flush buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      exact endCheck_x _ (hend hst)
    · rw [ite_eq_right hz]
      exact ⟨fun _ _ z Z hz h => hA z Z hz h, fun e => Status.noConfusion e, fun _ => ⟨fun e => Status.noConfusion e, fun _ => hend hst⟩⟩

/-- A call. -/
theorem callD_x {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} {t : List UInt8} :
    ∀ (space : Nat) (D : Dec) (h : DInv stop D) (buf : ByteArray),
    MemD Ws X L D (D.bits a D.pos stop (bits t)) → CallX Ws L a stop t D (callD a stop hs final D h buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h buf M
    rw [callD]
    dsimp only
    have hr := (runD_x (hs := hs) (t := t) ⟨withCap D space, h.withCap space⟩ (M.withCap _)).uncap
    dsimp only at hr
    obtain ⟨p, hrel⟩ := h.1
    have hok := runD_ok (hs := hs) ⟨withCap D space, h.withCap space⟩ p (hrel.withCap _)
    dsimp only at hok
    by_cases hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO]
      have hM := ((runD_mem (hs := hs) (t := t) ⟨withCap D space, h.withCap space⟩ (M.withCap _)).go (by rw [hO]; decide) (by rw [hO]; decide)).flushed buf space
      obtain ⟨p', hR, b1, _⟩ := hok.needsOutput hO
      obtain ⟨_, _, _, _, _, _, _, _, a8, _⟩ := flushD_spec hR buf space
      have hA : ∀ z Z, SInv z → Anch z Z a stop t D D.pos →
          Anch z Z a stop t (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
            (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.pos :=
        fun z Z hz h0 => (hr.go (by rw [hO]; decide) (by rw [hO]; decide) z Z hz h0).flush buf space
      have hE : D.tag = .ended → False := fun e => absurd ((hr.ended e).1.symm.trans hO) (by decide)
      have hp1 : D.pos.toNat ≤ (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.pos.toNat := by
        rw [a8]
        exact b1
      by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz]
        by_cases hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space
        · rw [dite_eq_left hlt]
          have hin := ih _ hlt _ (flushD_inv (runD_full hO) buf space) (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf hM
          refine ⟨fun e1 e2 z Z hz h0 => hin.go e1 e2 z Z hz (hA z Z hz h0), fun e => ?_, fun e => absurd e hE⟩
          obtain ⟨m1, m2, m3⟩ := hin.why e
          refine ⟨Nat.le_trans hp1 m1, m2, fun z Z hz h0 => ?_⟩
          obtain ⟨D1, pos1, c1, c2, c3, c4, c5⟩ := m3 z Z hz (hA z Z hz h0)
          exact ⟨D1, pos1, Nat.le_trans hp1 c1, c2, c3, c4, c5⟩
        · rw [dite_eq_right hlt]
          exact ⟨fun e => Bool.noConfusion e, fun e => Status.noConfusion e, fun e => absurd e hE⟩
      · rw [ite_eq_right hz]
        exact ⟨fun _ _ z Z hz h0 => hA z Z hz h0, fun e => Status.noConfusion e, fun e => absurd e hE⟩
    · rw [dite_eq_right hO]
      refine afterRun_x hr (fun e => ?_) _ _
      obtain ⟨st, b1, _⟩ := hok.next e
      exact b1.1

/-! ### WBITS in the reading in order -/

/-- Going on from WBITS reads it. -/
theorem reach_wbits_read {q : SPhase} {bs c : List Bool} (h : Reach sStep .wbits bs q c) (hq : q ≠ .wbits) :
    ∃ kv r, readWBITS bs = some (kv, r) := by
  cases h with
  | refl => exact absurd rfl hq
  | next hs _ =>
    cases e : readWBITS bs with
    | some v =>
      obtain ⟨kv, r⟩ := v
      exact ⟨kv, r, rfl⟩
    | none =>
      simp only [sStep, readIn, e] at hs
      split at hs <;> cases hs

/-! ### Between calls -/

/-- Bytes from a place on, as the bytes up to further on and the rest. -/
private theorem drop_take_append {α : Type} (x : List α) {m n : Nat} (hm : m ≤ n) (hx : m ≤ x.length) :
    (x.take n).drop m ++ x.drop n = x.drop m := by
  conv => rhs; rw [← List.take_append_drop n x]
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]

/-- What every run of the decoder holds before the stream's end: in a header, where its meta-block began, which the reading in
order of the stream reaches; and every meta-block's start the reading in order has read past, whose header the state is
reading or which needs tables within the state's limit. -/
def HdTop (x : List UInt8) (R : Run DState) : Prop :=
  R.status.stopped = false → R.state.val.tag ≠ .ended →
  (R.state.val.tag = .hdr → ∃ w st last mlen g q um u, HdLoc R.state.val.hd R.state.val.limit last mlen g q um u ∧
    Reach sStep .wbits (bits x) (.mblock w st) (um ++ u ++ (R.state.val.held ++ bits (x.drop R.read)))) ∧
  (∀ w st b q, Reach sStep .wbits (bits x) (.mblock w st) b →
    Reach sStep (.mblock w st) b q (R.state.val.held ++ bits (x.drop R.read)) → b ≠ R.state.val.held ++ bits (x.drop R.read) →
    (R.state.val.tag = .hdr ∧ ∃ last mlen g q um u, HdLoc R.state.val.hd R.state.val.limit last mlen g q um u ∧
      b = um ++ u ++ (R.state.val.held ++ bits (x.drop R.read))) ∨ Cert R.state.val.limit.toNat b)

/-- The reply to a call the caller may make, for where a header began and where the limit binds. -/
private theorem reply_x {Ws : Option Nat} {X L : Nat} {x : List UInt8} {R : Run DState} {c : Call} (ha : R.Allowed x c)
    (M : MemD Ws X L R.state.val (R.state.val.held ++ bits (x.drop R.read))) :
    ∃ o : Out, (R.reply decoder x c).state.val = o.D ∧ (R.reply decoder x c).used = o.pos.toNat - c.pre.length ∧ (R.reply decoder x c).status = o.status ∧
      o.pos.toNat ≤ c.pre.length + c.size ∧ c.pre.length ≤ o.pos.toNat ∧
      CallX Ws L (R.input x c) (USize.ofNat (c.pre.length + c.size)) (x.drop (R.read + c.size)) (atPos R.state.val c.pre.length) o := by
  have hin := ha.inside
  have hfit := ha.fits
  have hg : c.pre.length + c.size ≤ (R.input x c).size ∧ c.pre.length ≤ c.pre.length + c.size ∧ c.pre.length + c.size < USize.size :=
    ⟨by rw [input_size hin]; omega, by omega, by omega⟩
  have hs : (USize.ofNat (c.pre.length + c.size)).toNat ≤ (R.input x c).size := by
    rw [usize_of hg.2.2]
    exact hg.1
  have hinv := atPos_inv (start := c.pre.length) R.state hg.2.1 hg.2.2
  obtain ⟨p, hrel, hw⟩ := M.place
  have hok := callD_ok (hs := hs) (final := c.final) c.space _ hinv p _ c.buf.toByteArray (atPos_rel hrel _) rfl
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of hg.2.2
  have hpos0 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
  have hpos1 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := hpos0
  have h1 := hok.posLe
  have h2 := hok.posStop
  rw [hpos0] at h1
  rw [hstop] at h2
  have hb0 : (atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
      R.state.val.held ++ bits (x.drop R.read) := by
    have := bits_at (R := R) (c := c) hin (atPos R.state.val c.pre.length) hpos1 (Nat.zero_le _) hstop
    rw [this]
    rfl
  have M0 : MemD Ws X L (atPos R.state.val c.pre.length)
      ((atPos R.state.val c.pre.length).bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size)))) :=
    M.move hb0 ⟨p, atPos_rel hrel _, by rw [hb0]; exact hw⟩ rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨callD (R.input x c) (USize.ofNat (c.pre.length + c.size)) hs c.final (atPos R.state.val c.pre.length) hinv c.buf.toByteArray c.space, ?_, ?_, ?_, h2, h1, callD_x _ _ _ _ M0⟩
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).state.val = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).used = _
    unfold decStep
    rw [dite_eq_left hg]
  · unfold Run.reply
    show (decStep _ _ _ _ _ _ _).status = _
    unfold decStep
    rw [dite_eq_left hg]

/-- A call's first state, reached from WBITS with the stream's bits. -/
private theorem start_anch {limit : Nat} {x : List UInt8} {R : Run DState} {c : Call} (hR : Reaches decoder limit x R) (ha : R.Allowed x c)
    (hH : HdTop x R) (hne : R.state.val.tag ≠ .ended) :
    Anch .wbits (bits x) (R.input x c) (USize.ofNat (c.pre.length + c.size)) (x.drop (R.read + c.size)) (atPos R.state.val c.pre.length)
      (atPos R.state.val c.pre.length).pos := by
  have hin := ha.inside
  have hfit := ha.fits
  have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
  have hpos1 : (atPos R.state.val c.pre.length).pos.toNat = c.pre.length + 0 := usize_of (by omega)
  have hb : ∀ D' : Dec, D'.bits (R.input x c) (atPos R.state.val c.pre.length).pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R.read + c.size))) =
      D'.held ++ bits (x.drop R.read) := fun D' => by
    have e := bits_at hin D' hpos1 (Nat.zero_le _) hstop
    rw [Nat.add_zero] at e
    exact e
  obtain ⟨p, hrel, _, hro, hreach, _⟩ := (order_inv hR).running ha.running
  have hrd := (top_inv hR).read
  have hx : Reach sStep .wbits (bits x) p (R.state.val.held ++ bits (x.drop R.read)) := by
    have g := hreach (x.drop R.offered)
    rwa [List.take_append_drop, drop_take_append x hro hrd] at g
  obtain ⟨hH1, hH2⟩ := hH ha.running hne
  refine ⟨⟨p, atPos_rel hrel _, by rw [hb]; exact hx⟩, fun ht => ?_, fun w st b q h1 h2 h3 => ?_⟩
  · obtain ⟨w, st, last, mlen, g, q, um, u, hL, hm⟩ := hH1 ht
    refine ⟨w, st, last, mlen, g, q, um, u, hL, ?_⟩
    rw [← Dec.bits_hdr ht, hb]
    exact hm
  · rw [hb] at h2 h3
    rcases hH2 w st b q h1 h2 h3 with ⟨ht, last, mlen, g, q', um, u, hL, hbu⟩ | hc
    · refine Or.inl ⟨ht, last, mlen, g, q', um, u, hL, ?_⟩
      rw [← Dec.bits_hdr (D := atPos R.state.val c.pre.length) ht, hb]
      exact hbu
    · exact Or.inr hc

/-- Every run of the decoder holds where its header began. -/
theorem hd_top {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) : HdTop x R := by
  induction h with
  | start =>
    show HdTop x { state := (decStart limit).1, status := (decStart limit).2, read := 0, offered := 0, emitted := [], ended := false }
    by_cases hl : limit < fixedCost
    · have e : decStart limit = (⟨deadD, _, deadD_rel⟩, .memoryLimit) := by
        unfold decStart
        rw [ite_eq_left hl]
      rw [e]
      exact fun hs => Bool.noConfusion hs
    · have e : decStart limit = (⟨liveD limit, _, liveD_rel limit⟩, .needsInput) := by
        unfold decStart
        rw [ite_eq_right hl]
      rw [e]
      refine fun _ _ => ⟨fun ht => DTag.noConfusion ht, fun w st b q h1 h2 h3 => ?_⟩
      have hB : (liveD limit).held = [] := rfl
      dsimp only at h2 h3
      rw [hB, List.nil_append, List.drop_zero] at h2 h3
      obtain ⟨v1, hv1⟩ := reach_suffix nfaith_sStep h1
      obtain ⟨v2, hv2⟩ := reach_suffix nfaith_sStep h2
      have l1 := congrArg List.length hv1
      have l2 := congrArg List.length hv2
      rw [List.length_append] at l1 l2
      have : v2 = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this
      exact absurd hv2 h3
  | @call R0 c hR ha ih =>
    intro hs hne
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨_, M⟩ := (mem_top hR).running ha.running
    obtain ⟨o, e1, e2, e4, h1, h2, hX⟩ := reply_x ha M
    have hstate : (R0.after decoder x c).state.val = o.D := e1
    have hstatus : (R0.after decoder x c).status = o.status := e4
    have hread : (R0.after decoder x c).read = R0.read + (o.pos.toNat - c.pre.length) := by
      show R0.read + (R0.reply decoder x c).used = _
      rw [e2]
    rw [hstatus] at hs
    rw [hstate] at hne
    have hne0 : R0.state.val.tag ≠ .ended := fun e => hne ((hX.ended e).2 hs)
    obtain ⟨⟨p1, _, _⟩, hA1, hA2⟩ := hX.go hs hne .wbits (bits x) trivial (start_anch hR ha ih hne0)
    have hb : o.D.bits (R0.input x c) o.pos (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size))) =
        o.D.held ++ bits (x.drop (R0.read + (o.pos.toNat - c.pre.length))) :=
      bits_at hin o.D (q := o.pos.toNat - c.pre.length) (by omega) (by omega) (usize_of (by omega))
    rw [hstate, hread]
    refine ⟨fun ht => ?_, fun w st b q g1 g2 g3 => ?_⟩
    · obtain ⟨w, st, last, mlen, g, q, um, u, hL, hm⟩ := hA1 ht
      refine ⟨w, st, last, mlen, g, q, um, u, hL, ?_⟩
      rw [← Dec.bits_hdr ht, hb] at hm
      exact hm
    · rw [← hb] at g2 g3
      rcases hA2 w st b q g1 g2 g3 with ⟨ht, last, mlen, g, q', um, u, hL, hbu⟩ | hc
      · refine Or.inl ⟨ht, last, mlen, g, q', um, u, hL, ?_⟩
        rw [← Dec.bits_hdr ht, hb] at hbu
        exact hbu
      · exact Or.inr hc

/-! ### The limit, truthfully -/

/-- The limit, when the window WBITS declares doesn't fit. -/
private theorem limit_wbits {limit kv X : Nat} (hlim : fixedCost ≤ limit) (h : min (limit - fixedCost) 4294835199 < 2 ^ kv)
    (hpw : 2 ^ kv ≤ 2 ^ 24) : limit < fixedCost + 2 ^ kv + X := by
  have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
  omega

/-- The limit, when a header's tables don't fit with the window. -/
private theorem limit_hdr {limit lim K A R H B F kv : Nat} (hlim : fixedCost ≤ limit) (hroom : lim + K = min (limit - fixedCost) 4294835199)
    (hbind : lim < A + R) (hT : H = A + R) (hht : H ≤ B) (hdr : B ≤ F) (hmax : H ≤ headerTablesMax * tableMax) (hK : 2 ^ kv = K)
    (hpw : 2 ^ kv ≤ 2 ^ 24) : limit < fixedCost + 2 ^ kv + F := by
  have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
  have hcap : headerTablesMax * tableMax = 102242304 := rfl
  omega

/-- Memory usage correctness, for the input used: when the decoder reports the limit, the bytes it reports as used already
demand more than the limit, and the spec's reading in order of some of those bytes got through all but at most 64 bits of
them. -/
theorem decoder_limitAt {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .memoryLimit) :
    limit < demand (x.take R.read) ∧
      ∃ (n : Nat) (q : SPhase) (cb : List Bool), n ≤ R.read ∧ Reach sStep .wbits (bits (x.take n)) q cb ∧
        8 * R.read + cb.length ≤ 8 * n + 64 := by
  cases h with
  | start =>
    have hl : limit < fixedCost := by
      change (decStart limit).2 = .memoryLimit at hs
      unfold decStart at hs
      by_cases hl : limit < fixedCost
      · exact hl
      · rw [ite_eq_right hl] at hs
        cases hs
    refine ⟨?_, 0, .wbits, bits (x.take 0), Nat.le_refl _, .refl _ _, ?_⟩
    · unfold demand
      omega
    · show 8 * 0 + (bits (x.take 0)).length ≤ 8 * 0 + 64
      rw [List.take_zero, bits_length]
      decide
  | @call R0 c hR ha =>
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨hlim, M⟩ := (mem_top hR).running ha.running
    obtain ⟨o, e1, e2, e4, h1, h2, hX⟩ := reply_x ha M
    have hst : o.status = .memoryLimit := by rw [← e4]; exact hs
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R0.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
    have hread : (R0.after decoder x c).read = R0.read + (o.pos.toNat - c.pre.length) := by
      show R0.read + (R0.reply decoder x c).used = _
      rw [e2]
    rw [hread]
    obtain ⟨_, _, hw⟩ := hX.why hst
    have hne0 : R0.state.val.tag ≠ .ended := fun e => (hX.ended e).1 hst
    obtain ⟨D1, pos1, d1, d2, d3, ⟨⟨p1, hp1, hz⟩, hh, _⟩, hB⟩ := hw .wbits (bits x) trivial (start_anch hR ha (hd_top hR) hne0)
    rw [hpos0] at d1
    generalize hk1 : pos1.toNat - c.pre.length = k1
    generalize hkq : o.pos.toNat - c.pre.length = kq
    have hq1 : pos1.toNat = c.pre.length + k1 := by omega
    have hqq : o.pos.toNat = c.pre.length + kq := by omega
    have hk : k1 ≤ kq := by omega
    have hks : kq ≤ c.size := by omega
    -- The deciding state's bits, as the bytes used and the rest.
    have hsplit : D1.bits (R0.input x c) pos1 (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size))) =
        (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat) ++ bits (x.drop (R0.read + kq)) := by
      have e : D1.held ++ (chunkBits (R0.input x c) o.pos.toNat (USize.ofNat (c.pre.length + c.size)).toNat ++ bits (x.drop (R0.read + c.size))) =
          D1.held ++ bits (x.drop (R0.read + kq)) := bits_at hin D1 hqq hks hstop
      have hc := chunkBits_split (R0.input x c) (show pos1.toNat ≤ o.pos.toNat by omega) (show o.pos.toNat ≤ (USize.ofNat (c.pre.length + c.size)).toNat by omega)
      show D1.held ++ (chunkBits (R0.input x c) pos1.toNat (USize.ofNat (c.pre.length + c.size)).toNat ++ bits (x.drop (R0.read + c.size))) = _
      rw [hc, List.append_assoc, List.append_assoc, List.append_cancel_left e]
    have hxs : bits x = bits (x.take (R0.read + kq)) ++ bits (x.drop (R0.read + kq)) := by
      rw [← bits_append, List.take_append_drop]
    have hF : (bits (x.drop (R0.read + kq))).length % 8 = 0 := by
      rw [bits_length]
      omega
    have hb0 : bits ([] : List UInt8) = [] := rfl
    -- Where the limit was found to bind, reached by the reading in order of the bytes before it.
    have htight : Reach sStep .wbits (bits (x.take (R0.read + k1))) p1 D1.held := by
      have e := bits_at hin D1 hq1 (by omega) hstop
      rw [e] at hz
      have hxs1 : bits x = bits (x.take (R0.read + k1)) ++ bits (x.drop (R0.read + k1)) := by
        rw [← bits_append, List.take_append_drop]
      exact reach_restrict nfaith_sStep hz _ _ _ hxs1 rfl (by rw [bits_length]; omega)
    refine ⟨?_, R0.read + k1, p1, D1.held, by omega, htight, by omega⟩
    have hroom : roomOf limit = min (limit - fixedCost) 4294835199 := rfl
    rcases hB with ⟨htw, hbw⟩ | ⟨hth, w, g1, g2, g3, g4⟩
    · -- At WBITS: the window the stream declares doesn't fit.
      have hp1w : p1 = .wbits := by
        cases p1 with
        | wbits => rfl
        | mblock => exact absurd (hp1.1.symm.trans htw) (by decide)
        | skip => exact absurd (hp1.1.symm.trans htw) (by decide)
        | raw => exact absurd (hp1.1.symm.trans htw) (by decide)
        | hdr => exact absurd (hp1.1.symm.trans htw) (by decide)
        | cmds => exact absurd (hp1.1.symm.trans htw) (by decide)
        | ended => exact absurd (hp1.1.symm.trans htw) (by decide)
      subst hp1w
      have heq := (reach_to_wbits hz).2
      rw [hsplit, hxs] at heq
      have hcut := List.append_cancel_right heq
      obtain ⟨kv, rest, r1, r2⟩ := hbw []
      dsimp only at r1
      rw [hb0, List.append_nil, hcut] at r1
      have hwb : windowBytes (bits (x.take (R0.read + kq))) = 2 ^ kv := by
        unfold windowBytes
        rw [r1]
      have hpw : 2 ^ kv ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (readWBITS_range r1).2
      rw [hroom] at r2
      unfold demand
      rw [hwb]
      exact limit_wbits hlim r2 hpw
    · -- In a header: its tables so far and the next one don't fit with the window.
      obtain ⟨w0, st0, last, mlen, g, q, um, u, hL, hm⟩ := hh hth
      rw [← Dec.bits_hdr hth, hsplit, hxs] at hm
      have hr := reach_restrict nfaith_sStep hm (bits (x.take (R0.read + kq))) (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat))
        (bits (x.drop (R0.read + kq))) rfl (by simp only [List.append_assoc]) hF
      have hdr := demand_reach hr
      have hbt : (srest demandSem (.mblock w0 st0) (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat))).getD 0 =
          blocksT w0 st0 (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat)) := rfl
      have hfirst : (srest demandSem .wbits (bits (x.take (R0.read + kq)))).getD 0 = (demandSem.first (bits (x.take (R0.read + kq)))).getD 0 := rfl
      have hht := headerTables_le w0 st0 (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat))
      have hmax := headerTables_le_max (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat))
      have hT : headerTables (um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat)) =
          D1.hd.d.arena.size + (hrest tableK g q (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat)).getD 0 := by
        have e := hL.start (chunkBits (R0.input x c) pos1.toNat o.pos.toNat)
        have e2 := hL.tables (chunkBits (R0.input x c) pos1.toNat o.pos.toNat)
        rw [← Dec.held_hdr hth] at e e2
        unfold headerTables
        rw [show um ++ u ++ (D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat) =
          um ++ u ++ D1.held ++ chunkBits (R0.input x c) pos1.toNat o.pos.toNat by simp only [List.append_assoc], e]
        exact e2
      have hbind := g4 last mlen g q um u hL []
      dsimp only at hbind
      rw [hb0, List.append_nil, hL.max] at hbind
      obtain ⟨kv, r', hr1⟩ := reach_wbits_read hr (fun e => SPhase.noConfusion e)
      obtain ⟨u1, hu1, hf1⟩ := faith_readWBITS _ _ _ hr1
      have hrx : readWBITS (bits x) = some (kv, r' ++ bits (x.drop (R0.read + kq))) := by
        rw [hxs, hu1, List.append_assoc]
        exact hf1 _
      have hWs : winSem.first (bits x) = some (windowSize kv) := by
        show (readWBITS (bits x) >>= fun p => some (windowSize p.1)) = _
        rw [hrx]
        rfl
      rw [hWs] at g1
      have hw : windowSize kv = w := Option.some.inj g1
      have hrange := readWBITS_range hr1
      have hws := (windowSize_range hrange.1 hrange.2).1
      have hwb : windowBytes (bits (x.take (R0.read + kq))) = 2 ^ kv := by
        unfold windowBytes
        rw [hr1]
      have hpw : 2 ^ kv ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hrange.2
      have hK : 2 ^ kv = 2 ^ D1.k.toNat := by rw [← hws, hw, g2]
      rw [hbt, hfirst] at hdr
      rw [hroom] at g3
      unfold demand
      rw [hwb]
      exact limit_hdr hlim g3 hbind hT hht hdr hmax hK hpw

/-- The demand of bytes before where the limit binds, within the limit. -/
private theorem limit_tight_arith {limit lim K W T : Nat} (hlim : fixedCost ≤ limit) (hroom : lim + K = min (limit - fixedCost) 4294835199)
    (hW : W ≤ K) (hT : T ≤ lim) : fixedCost + W + T ≤ limit := by
  omega

/-- Memory usage correctness, for the input used, the other way: when the decoder reports the limit, it reports it no later than
nine bytes after the stream's first bytes demand more than the limit. Nine bytes before the bytes it reports as used, the stream
didn't yet demand more. -/
theorem decoder_limitTight {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .memoryLimit) :
    ∀ n, n + 9 ≤ R.read → demand (x.take n) ≤ limit := by
  cases h with
  | start =>
    intro n hn
    have h0 : (Run.initial decoder limit).read = 0 := rfl
    omega
  | @call R0 c hR ha =>
    intro n hn
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨hlim, M⟩ := (mem_top hR).running ha.running
    obtain ⟨o, e1, e2, e4, h1, h2, hX⟩ := reply_x ha M
    have hst : o.status = .memoryLimit := by rw [← e4]; exact hs
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R0.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
    have hread : (R0.after decoder x c).read = R0.read + (o.pos.toNat - c.pre.length) := by
      show R0.read + (R0.reply decoder x c).used = _
      rw [e2]
    rw [hread] at hn
    obtain ⟨_, _, hw⟩ := hX.why hst
    have hne0 : R0.state.val.tag ≠ .ended := fun e => (hX.ended e).1 hst
    obtain ⟨D1, pos1, d1, d2, d3, ⟨⟨p1, hp1, hz⟩, _, hd⟩, hB⟩ := hw .wbits (bits x) trivial (start_anch hR ha (hd_top hR) hne0)
    rw [hpos0] at d1
    generalize hk1 : pos1.toNat - c.pre.length = k1 at *
    generalize hkq : o.pos.toNat - c.pre.length = kq at *
    have hq1 : pos1.toNat = c.pre.length + k1 := by omega
    have hqq : o.pos.toNat = c.pre.length + kq := by omega
    have hks : kq ≤ c.size := by omega
    -- The deciding state's bits, and the cut `n` strictly before them.
    have e := bits_at hin D1 hq1 (by omega) hstop
    have hxs : bits x = bits (x.take n) ++ bits (x.drop n) := by rw [← bits_append, List.take_append_drop]
    have hF8 : (bits (x.drop n)).length % 8 = 0 := by rw [bits_length]; omega
    have hlenF : (D1.bits (R0.input x c) pos1 (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size)))).length <
        (bits (x.drop n)).length := by
      rw [e, List.length_append, bits_length, bits_length, List.length_drop, List.length_drop]
      omega
    rw [hxs] at hz
    obtain ⟨s', c', r1, r2, _, r4⟩ := reach_cut8 nfaith_sStep hz hlenF hF8
    rcases hB with ⟨htw, _⟩ | ⟨hth, w, g1, g2, g3, _⟩
    · -- At WBITS nothing was read yet, so no bytes lie before the deciding state.
      have hp0 := hp1.wbits_place htw
      subst hp0
      rw [← hxs] at hz
      have := (reach_to_wbits hz).2
      have l := congrArg List.length this
      rw [hxs, List.length_append] at l
      omega
    · -- In a header: every meta-block's start before the cut needs tables within the limit.
      have hT : (demandSem.first (bits (x.take n))).getD 0 ≤ D1.limit.toNat := by
        show (srest demandSem .wbits (bits (x.take n))).getD 0 ≤ _
        refine demand_bound r1 r2 (fun w' st' b hmb => ?_)
        have hmb' : Reach sStep (.mblock w' st') b s' c' := by
          rcases Reach.total hmb r1 with e5 | e5
          · exact e5
          · obtain ⟨e6, e7⟩ := Reach.stuck e5 r2
            rw [e6, e7]
            exact .refl _ _
        have g5 : Reach sStep .wbits (bits x) (.mblock w' st') (b ++ bits (x.drop n)) := by
          rw [hxs]
          exact reach_extend nfaith_sStep hmb hF8
        have g6 : Reach sStep (.mblock w' st') (b ++ bits (x.drop n)) p1
            (D1.bits (R0.input x c) pos1 (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size)))) :=
          (reach_extend nfaith_sStep hmb' hF8).trans r4
        have g7 : b ++ bits (x.drop n) ≠ D1.bits (R0.input x c) pos1 (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size))) := by
          intro e8
          have l := congrArg List.length e8
          rw [List.length_append] at l
          omega
        rcases hd w' st' (b ++ bits (x.drop n)) p1 g5 g6 g7 with ⟨_, last, mlen, g, q, um, u, hL, hbu⟩ | hc
        · rw [avail_mk, ← List.append_assoc] at hbu
          refine cert_within (X := chunkBits (R0.input x c) pos1.toNat (USize.ofNat (c.pre.length + c.size)).toNat ++
            bits (x.drop (R0.read + c.size))) hL hbu.symm ?_
          have hb1 := Dec.bits_hdr hth (R0.input x c) pos1 (USize.ofNat (c.pre.length + c.size)) (bits (x.drop (R0.read + c.size)))
          rw [avail_mk] at hb1
          rw [← hb1]
          exact hlenF
        · exact hc b (bits (x.drop n)) rfl
      have hW : windowBytes (bits (x.take n)) ≤ 2 ^ D1.k.toNat := by
        unfold windowBytes
        cases hr : readWBITS (bits (x.take n)) with
        | none => exact Nat.zero_le _
        | some v =>
          obtain ⟨kv, r'⟩ := v
          obtain ⟨u1, hu1, hf1⟩ := faith_readWBITS _ _ _ hr
          have hrx : readWBITS (bits x) = some (kv, r' ++ bits (x.drop n)) := by
            rw [hxs, hu1, List.append_assoc]
            exact hf1 _
          have hWs : winSem.first (bits x) = some (windowSize kv) := by
            show (readWBITS (bits x) >>= fun p => some (windowSize p.1)) = _
            rw [hrx]
            rfl
          rw [hWs] at g1
          have hw' : windowSize kv = w := Option.some.inj g1
          have hrange := readWBITS_range hr
          have hws := (windowSize_range hrange.1 hrange.2).1
          show 2 ^ kv ≤ _
          omega
      unfold demand
      exact limit_tight_arith hlim g3 hW hT

/-- Memory usage correctness, for the bytes used: when the decoder reports the limit, those bytes alone demand more. -/
theorem decoder_limitUsed : LimitUsed decoder demand := fun h hs => (decoder_limitAt h hs).1

/-- Streaming correctness, for the limit: the decoder reports it within nine bytes of where the input first demands more. -/
theorem decoder_limitPrompt : LimitPrompt decoder demand := fun h hs => decoder_limitTight h hs

/-- Soundness, for the bytes used: a rejection's bytes used are the whole stream after the end signal, or bytes no
continuation makes valid. -/
theorem decoder_rejectUsed : RejectUsed decoder := fun h hs => (decoder_rejectsAt h hs).imp id (·.1)

end Brotli.Decoder
