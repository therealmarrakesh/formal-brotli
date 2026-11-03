import Brotli.Decoder.Interface
import Brotli.Decoder.StreamOut

/-!
# A call

What one call does: hand out waiting bytes, run the loop, hand out what it left, and read the verdict at the stream's end.
`callD_ok` is what a call does in the spec's terms.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### What the loop leaves -/

/-- What the loop must do, for the input so far and whatever whole bytes follow. -/
structure RunD (a : ByteArray) (stop : USize) (p : SPhase) (D r : Dec) : Prop where
  next : r.status = .next → ∃ st, DRel r (.ended st) ∧ D.pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ OutD p (.ended st) D r ∧
    (∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem (.ended st) (r.bits a r.pos stop (bits t))) ∧
    ∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) (.ended st) (r.bits a r.pos stop (bits t))
  needsInput : r.status = .needsInput → r.pos = stop ∧ D.pos.toNat ≤ stop.toNat ∧ ∃ p', DRel r p' ∧ OutD p p' D r ∧
    (∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem p' (r.bits a r.pos stop (bits t))) ∧ srest specSem p' r.held = none ∧
    (∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (r.bits a r.pos stop (bits t))) ∧ SShort p' r.held
  needsOutput : r.status = .needsOutput → ∃ p', DRel r p' ∧ D.pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ OutD p p' D r ∧
    (∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem p' (r.bits a r.pos stop (bits t))) ∧ r.cmd.pend.toNat ≠ 0 ∧
    ∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (r.bits a r.pos stop (bits t))
  bad : r.status = .bad → ∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = none
  memory : r.status = .memory → ∃ p' D', DRel D' p' ∧ D.pos.toNat ≤ D'.pos.toNat ∧ D'.pos.toNat ≤ stop.toNat ∧ OutD p p' D D' ∧
    (∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (D'.bits a D'.pos stop (bits t))) ∧ D'.cmd.pend = 0 ∧
    (p' = .wbits ∨ ∃ w st last mlen g q, p' = .hdr w st last mlen g q)

/-- The cap on waiting bytes changes nothing the loop's contract says of where it started. -/
theorem RunD.uncap {a : ByteArray} {stop : USize} {p : SPhase} {D r : Dec} {x : USize}
    (h : RunD a stop p { D with cmd := { D.cmd with cap := x } } r) : RunD a stop p D r :=
  ⟨h.1, h.2, h.3, h.4, h.5⟩

/-- Two moves' bytes together. -/
theorem OutD.trans {p p1 p2 : SPhase} {D r1 r : Dec} (h1 : OutD p p1 D r1) (h2 : OutD p1 p2 r1 r) : OutD p p2 D r := by
  obtain ⟨l1, a1, b1⟩ := h1
  obtain ⟨l2, a2, b2⟩ := h2
  refine ⟨l2 ++ l1, by rw [a2, a1, List.append_assoc], ?_⟩
  rw [b2, b1, List.length_append]
  omega

/-- What the loop does, in the spec's terms. -/
theorem runD_ok {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} : ∀ (x : RunArg a stop hs) (p : SPhase), DRel x.D p →
    RunD a stop p x.D (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    intro p hrel
    obtain ⟨D, hinv⟩ := x
    dsimp only at hrel ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      cases p with
      | ended st =>
        have hrel' : DRel { D with status := .next } (.ended st) := by
          obtain ⟨h1, h2, w, h3, h4, h5⟩ := hrel
          exact ⟨h1, h2, w, { h3 with }, h4, h5⟩
        refine ⟨fun _ => ⟨st, hrel', Nat.le_refl _, hinv.2, ⟨[], rfl, rfl⟩, (fun t => ?_), fun t => Reach.refl _ _⟩, fun e => DStatus.noConfusion e,
          fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
        have hb : Dec.bits { D with status := .next } a D.pos stop (bits t) = Dec.bits D a D.pos stop (bits t) := rfl
        show _ = srest specSem (.ended st) (Dec.bits { D with status := .next } a D.pos stop (bits t))
        rw [hb]
      | wbits => exact absurd (he.symm.trans hrel.1) (by decide)
      | mblock => exact absurd (he.symm.trans hrel.1) (by decide)
      | skip => exact absurd (he.symm.trans hrel.1) (by decide)
      | raw => exact absurd (he.symm.trans hrel.1) (by decide)
      | hdr => exact absurd (he.symm.trans hrel.1) (by decide)
      | cmds => exact absurd (he.symm.trans hrel.1) (by decide)
    · rw [dite_eq_right he]
      dsimp only
      have hstep := stepD_ok specSem (a := a) (hs := hs) hrel he hinv.2
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        obtain ⟨p', hR, h1, h2, h3, _, h4, h5⟩ := hstep.next hn
        have hih := ih ⟨stepD a stop hs D, hinv.step he hn⟩ ⟨he, hn, rfl⟩ p' hR
        dsimp only at hih
        generalize runD a stop hs (stepD a stop hs D) (hinv.step he hn) = r at hih ⊢
        refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e t => ?_, fun e => ?_⟩
        rotate_right
        · obtain ⟨p2, D2, b1, b2, b3, b4, b5, b6, b7⟩ := hih.memory e
          exact ⟨p2, D2, b1, Nat.le_trans h1 b2, b3, h4.trans b4, fun t => (h5 t).trans (b5 t), b6, b7⟩
        · obtain ⟨st, b1, b2, b3, b4, b5, b6⟩ := hih.next e
          refine ⟨st, b1, Nat.le_trans h1 b2, b3, h4.trans b4, (fun t => ?_), fun t => (h5 t).trans (b6 t)⟩
          rw [← sLeave_spec, h3, b5]
        · obtain ⟨b1, b2, p2, b3, b4, b5, b6, b7, b8⟩ := hih.needsInput e
          refine ⟨b1, Nat.le_trans h1 b2, p2, b3, h4.trans b4, (fun t => ?_), b6, (fun t => (h5 t).trans (b7 t)), b8⟩
          rw [← sLeave_spec, h3, b5]
        · obtain ⟨p2, b1, b2, b3, b4, b5, b6, b7⟩ := hih.needsOutput e
          refine ⟨p2, b1, Nat.le_trans h1 b2, b3, h4.trans b4, (fun t => ?_), b6, fun t => (h5 t).trans (b7 t)⟩
          rw [← sLeave_spec, h3, b5]
        · rw [← sLeave_spec, h3, hih.bad e t]
      · rw [dite_eq_right hn]
        refine ⟨fun e => absurd e hn, fun e => ?_, fun e => ?_, fun e t => ?_, fun e => ?_⟩
        rotate_right
        · obtain ⟨_, b2, b3⟩ := hstep.memory e
          exact ⟨p, D, hrel, Nat.le_refl _, hinv.2, ⟨[], rfl, rfl⟩, fun t => .refl _ _, b2, b3⟩
        · obtain ⟨b1, b2, p2, b3, b4, b5, _, _, b6, b7, b8⟩ := hstep.needsInput e
          refine ⟨b1, b2, p2, b3, b6, (fun t => ?_), ?_, b7, b8⟩
          · rw [← sLeave_spec, ← sLeave_spec, b4]
          · rw [← sLeave_spec, b5]
        · obtain ⟨p2, b1, b2, b3, b4, b5, _, _, b6, b7⟩ := hstep.needsOutput e
          refine ⟨p2, b1, b2, b3, b6, (fun t => ?_), b5, b7⟩
          rw [← sLeave_spec, ← sLeave_spec, b4]
        · rw [← sLeave_spec]
          exact hstep.bad e t

/-! ### Handing bytes out -/

/-- What handing bytes out leaves. -/
structure Flush where
  st : Cmd
  buf : ByteArray
  space : Nat

/-- Hands out waiting bytes while there are bytes and room. -/
def flushAll (k : USize) (st : Cmd) (buf : ByteArray) (space : Nat) : Flush :=
  let p0 := st.pend
  if p0 = 0 ∨ space = 0 then ⟨st, buf, space⟩
  else
    let r := flushCmd k st buf (USize.ofNat (min space 16777216))
    if _h : r.st.pend < p0 then flushAll k r.st r.buf (space - (p0 - r.st.pend).toNat)
    else ⟨r.st, r.buf, space⟩
termination_by st.pend.toNat
decreasing_by exact USize.lt_iff_toNat_lt.mp _h

/-- The bytes newly handed out, on the list of the bytes handed out so far. -/
theorem drop_take_reverse {out : List Nat} {pend len : Nat} (hp : pend ≤ out.length) (hl : len ≤ pend) :
    (out.drop (pend - len)).reverse = (out.drop pend).reverse ++ ((out.take pend).reverse).take len := by
  have h1 : out.drop (pend - len) = (out.take pend).drop (pend - len) ++ out.drop pend := by
    conv => lhs; rw [← List.take_append_drop pend out]
    rw [List.drop_append_of_le_length (by simp only [List.length_take]; omega)]
  have h2 : ((out.take pend).drop (pend - len)).reverse = ((out.take pend).reverse).take len := by
    rw [List.reverse_drop, List.length_take, Nat.min_eq_left hp]
    congr 1
    omega
  rw [h1, List.reverse_append, h2]

/-- What handing bytes out does. -/
theorem flushAll_spec {k : USize} {out : List Nat} (hk : k.toNat ≤ 24) : ∀ (N : Nat) (st : Cmd) (buf : ByteArray) (space : Nat), st.pend.toNat = N →
    RingOk st.ring k.toNat st.wpos.toNat out → st.pend.toNat ≤ 2 ^ k.toNat → st.pend.toNat ≤ out.length →
    ∃ len, len ≤ N ∧ len ≤ space ∧ (flushAll k st buf space).space = space - len ∧ (flushAll k st buf space).st = { st with pend := (flushAll k st buf space).st.pend } ∧
      (flushAll k st buf space).st.pend.toNat = N - len ∧ (N - len ≠ 0 → space - len = 0) ∧
      (flushAll k st buf space).buf.data.toList.map UInt8.toNat = buf.data.toList.map UInt8.toNat ++ ((out.take N).reverse).take len := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro st buf space hN hring hle hout
    rw [flushAll]
    dsimp only
    by_cases hz : st.pend = 0 ∨ space = 0
    · rw [ite_eq_left hz]
      refine ⟨0, Nat.zero_le _, Nat.zero_le _, rfl, rfl, by simpa using hN, ?_, by simp⟩
      rcases hz with h | h
      · intro h0
        have : st.pend.toNat = 0 := by rw [h]; rfl
        omega
      · intro _
        omega
    · rw [ite_eq_right hz]
      have hp0 : st.pend.toNat ≠ 0 := fun e => hz (Or.inl (USize.toNat_inj.mp e))
      have hs0 : space ≠ 0 := fun e => hz (Or.inr e)
      have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
      have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
      have hsp : (USize.ofNat (min space 16777216)).toNat = min space 16777216 := usize_ofNat' (by omega)
      obtain ⟨len, l1, l2, l3, l4, l5, l6⟩ := flushCmd_spec (buf := buf) (space := USize.ofNat (min space 16777216)) hring hle hout hk
      rw [hsp] at l1 l3
      generalize flushCmd k st buf (USize.ofNat (min space 16777216)) = r at l1 l2 l3 l4 l5 l6 ⊢
      have hlen1 : 1 ≤ len := l3 hp0 (by omega)
      have hlt : r.st.pend < st.pend := USize.lt_iff_toNat_lt.mpr (by omega)
      rw [dite_eq_left hlt]
      have hsub : (st.pend - r.st.pend).toNat = len := by
        rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
        omega
      rw [hsub]
      have hrst : r.st.ring = st.ring ∧ r.st.wpos = st.wpos := by
        rw [l5]
        exact ⟨rfl, rfl⟩
      have hring2 : RingOk r.st.ring k.toNat r.st.wpos.toNat out := by
        rw [hrst.1, hrst.2]
        exact hring
      obtain ⟨len2, a1, a2, a3, a4, a5, a6, a7⟩ := ih r.st.pend.toNat (by omega) r.st r.buf (space - len) rfl hring2 (by omega) (by omega)
      refine ⟨len + len2, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
      · rw [a3]
        omega
      · generalize (flushAll k r.st r.buf (space - len)) = f at a4 a5 a3 a7 ⊢
        rw [a4, l5]
      · rw [a5]
        omega
      · intro h
        have := a6 (by omega)
        omega
      · have hpe : r.st.pend.toNat = N - len := by omega
        have hZ : out.take r.st.pend.toNat = (out.take N).take (N - len) := by
          rw [List.take_take, hpe, Nat.min_eq_left (by omega)]
        have hrev : (out.take r.st.pend.toNat).reverse = ((out.take N).reverse).drop len := by
          rw [hZ, List.reverse_take, List.length_take, Nat.min_eq_left (by omega)]
          congr 1
          omega
        rw [a7, l6, List.append_assoc, hN, hrev, List.take_add]

/-! ### What a state keeps -/

theorem WinAll.congr {D D' : Dec} {w : Nat} {st : StreamState} (h : WinAll D w st) (ek : D'.k = D.k) (ec : D'.cmd = D.cmd) (el : D'.limit = D.limit) :
    WinAll D' w st :=
  ⟨by rw [ek, ec]; exact h.win, h.produced, by rw [el]; exact h.limit⟩

/-- A state's place doesn't depend on its position or status. -/
theorem DRel.congr {D D' : Dec} {p : SPhase} (h : DRel D p) (e1 : D'.tag = D.tag) (e2 : D'.cmd = D.cmd) (e3 : D'.hd = D.hd) (e4 : D'.H = D.H) (e5 : D'.k = D.k)
    (e6 : D'.last = D.last) (e7 : D'.left = D.left) (e8 : D'.limit = D.limit) : DRel D' p := by
  cases p with
  | wbits =>
    obtain ⟨a1, a2, a3, a4⟩ := h
    exact ⟨e1.trans a1, by rw [e2]; exact a2, by rw [e8]; exact a3, by rw [e2]; exact a4⟩
  | mblock =>
    obtain ⟨a1, a2, a3⟩ := h
    exact ⟨e1.trans a1, by rw [e2]; exact a2, a3.congr e5 e2 e8⟩
  | skip =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨e1.trans a1, by rw [e2]; exact a2, a3.congr e5 e2 e8, e6.trans a4, by rw [e7]; exact a5, by rw [e2]; exact a6, a7⟩
  | raw =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨e1.trans a1, by rw [e2]; exact a2, a3.congr e5 e2 e8, e6.trans a4, by rw [e7]; exact a5, a6⟩
  | hdr =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    exact ⟨e1.trans a1, a2.congr e5 e2 e8, e6.trans a3, by rw [e7]; exact a4, a5, a6, by rw [e3]; exact a7, by rw [e2]; exact a8⟩
  | cmds =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨e1.trans a1, e6.trans a2, by rw [e8]; exact a3, by rw [e4]; exact a4, by rw [e5, e2]; exact a5⟩
  | ended =>
    obtain ⟨a1, a2, w, a3⟩ := h
    exact ⟨e1.trans a1, by rw [e2]; exact a2, w, a3.congr e5 e2 e8⟩

/-- Fewer bytes waiting keeps a state's place. -/
theorem DRel.withPend {D : Dec} {p : SPhase} (h : DRel D p) {x : USize} (hx : x.toNat ≤ D.cmd.pend.toNat) : DRel { D with cmd := { D.cmd with pend := x } } p := by
  have hwin : ∀ {w st}, WinAll D w st → WinAll { D with cmd := { D.cmd with pend := x } } w st := by
    intro w st a
    have h1 := a.win.pendLe
    have h2 := a.win.pendOut
    exact ⟨{ a.win with pendLe := Nat.le_trans hx h1, pendOut := Nat.le_trans hx h2 }, a.produced, a.limit⟩
  cases p with
  | wbits =>
    obtain ⟨a1, a2, a3, a4⟩ := h
    refine ⟨a1, a2, a3, ?_⟩
    have h0 : D.cmd.pend.toNat = 0 := by rw [a4]; rfl
    show x = 0
    exact USize.toNat_inj.mp (by show x.toNat = 0; omega)
  | mblock =>
    obtain ⟨a1, a2, a3⟩ := h
    exact ⟨a1, a2, hwin a3⟩
  | skip =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨a1, a2, hwin a3, a4, a5, a6, a7⟩
  | raw =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨a1, a2, hwin a3, a4, a5, a6⟩
  | hdr =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    have h0 : D.cmd.pend.toNat = 0 := by rw [a8]; rfl
    exact ⟨a1, hwin a2, a3, a4, a5, a6, a7, USize.toNat_inj.mp (by show x.toNat = 0; omega)⟩
  | cmds =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1, a2, a3, a4, a5.withPend hx⟩
  | ended =>
    obtain ⟨a1, a2, w, a3⟩ := h
    exact ⟨a1, a2, w, hwin a3⟩

/-- The cap on waiting bytes keeps a state's place. -/
theorem DRel.withCap {D : Dec} {p : SPhase} (h : DRel D p) (x : USize) : DRel { D with cmd := { D.cmd with cap := x } } p := by
  have hwin : ∀ {w st}, WinAll D w st → WinAll { D with cmd := { D.cmd with cap := x } } w st :=
    fun a => ⟨{ a.win with }, a.produced, a.limit⟩
  cases p with
  | wbits =>
    obtain ⟨a1, a2, a3, a4⟩ := h
    exact ⟨a1, a2, a3, a4⟩
  | mblock =>
    obtain ⟨a1, a2, a3⟩ := h
    exact ⟨a1, a2, hwin a3⟩
  | skip =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨a1, a2, hwin a3, a4, a5, a6, a7⟩
  | raw =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := h
    exact ⟨a1, a2, hwin a3, a4, a5, a6⟩
  | hdr =>
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
    exact ⟨a1, hwin a2, a3, a4, a5, a6, a7, a8⟩
  | cmds =>
    obtain ⟨a1, a2, a3, a4, a5⟩ := h
    exact ⟨a1, a2, a3, a4, a5.withCap x⟩
  | ended =>
    obtain ⟨a1, a2, w, a3⟩ := h
    exact ⟨a1, a2, w, hwin a3⟩

/-- What handing bytes out needs of a state. -/
theorem DRel.window {D : Dec} {p : SPhase} (h : DRel D p) :
    D.cmd.pend = 0 ∨ (RingOk D.cmd.ring D.k.toNat D.cmd.wpos.toNat p.out ∧ D.cmd.pend.toNat ≤ 2 ^ D.k.toNat ∧ D.cmd.pend.toNat ≤ p.out.length ∧ D.k.toNat ≤ 24) := by
  have hwin : ∀ {w st}, WinAll D w st → (RingOk D.cmd.ring D.k.toNat D.cmd.wpos.toNat st.output ∧ D.cmd.pend.toNat ≤ 2 ^ D.k.toNat ∧ D.cmd.pend.toNat ≤ st.output.length ∧ D.k.toNat ≤ 24) :=
    fun a => ⟨a.win.ring, a.win.pendLe, a.win.pendOut, a.win.k24⟩
  cases p with
  | wbits => exact Or.inl h.2.2.2
  | mblock => exact Or.inr (hwin h.2.2)
  | skip => exact Or.inr (hwin h.2.2.1)
  | raw => exact Or.inr (hwin h.2.2.1)
  | hdr => exact Or.inr (hwin h.2.1)
  | cmds => exact Or.inr h.2.2.2.2.window
  | ended =>
    obtain ⟨_, _, _, a⟩ := h
    exact Or.inr (hwin a)

/-- A state with nothing in it, left when a stream has stopped. -/
def deadD : Dec := ⟨.wbits, Cmd.none, Hd.none, Hdr.none, 0, false, 0, 0, 0, .next⟩

theorem deadD_rel : DRel deadD .wbits :=
  ⟨rfl, ⟨by decide, by decide⟩, by decide, rfl⟩

/-! ### Handing out a state's bytes -/

/-- What handing out a state's bytes leaves. -/
structure FlushD where
  D : Dec
  buf : ByteArray
  space : Nat

/-- Hands out a state's waiting bytes while there are bytes and room. -/
@[inline] def flushD (D : Dec) (buf : ByteArray) (space : Nat) : FlushD :=
  let f := flushAll D.k D.cmd buf space
  ⟨{ D with cmd := f.st }, f.buf, f.space⟩

/-- What handing out a state's bytes does. -/
theorem flushD_spec {D : Dec} {p : SPhase} (h : DRel D p) (buf : ByteArray) (space : Nat) :
    ∃ len, len ≤ D.cmd.pend.toNat ∧ len ≤ space ∧ (flushD D buf space).space = space - len ∧ DRel (flushD D buf space).D p ∧
      (flushD D buf space).D.cmd.pend.toNat = D.cmd.pend.toNat - len ∧ (D.cmd.pend.toNat - len ≠ 0 → space - len = 0) ∧
      (flushD D buf space).buf.data.toList.map UInt8.toNat = buf.data.toList.map UInt8.toNat ++ ((p.out.take D.cmd.pend.toNat).reverse).take len ∧
      (flushD D buf space).D.pos = D.pos ∧ (flushD D buf space).D.status = D.status ∧
      (∀ a pos stop F, (flushD D buf space).D.bits a pos stop F = D.bits a pos stop F) ∧ (flushD D buf space).D.held = D.held := by
  have hbits : ∀ {x : Cmd}, x.word = D.cmd.word → x.count = D.cmd.count → (∀ a pos stop F, Dec.bits { D with cmd := x } a pos stop F = D.bits a pos stop F) ∧
      Dec.held { D with cmd := x } = D.held := by
    intro x h1 h2
    constructor
    · intro a pos stop F
      unfold Dec.bits Dec.word Dec.count
      dsimp only
      cases D.tag <;> simp only [h1, h2]
    · unfold Dec.held Dec.word Dec.count
      dsimp only
      cases D.tag <;> simp only [h1, h2]
  rcases h.window with h0 | ⟨hring, hle, hout, hk⟩
  · have hN : D.cmd.pend.toNat = 0 := by rw [h0]; rfl
    have hf : flushAll D.k D.cmd buf space = ⟨D.cmd, buf, space⟩ := by
      rw [flushAll]
      dsimp only
      rw [ite_eq_left (Or.inl h0)]
    have e : flushD D buf space = ⟨{ D with cmd := D.cmd }, buf, space⟩ := by
      unfold flushD
      rw [hf]
    rw [e]
    obtain ⟨b1, b2⟩ := hbits (x := D.cmd) rfl rfl
    refine ⟨0, Nat.zero_le _, Nat.zero_le _, rfl, h.congr rfl rfl rfl rfl rfl rfl rfl rfl, by simp only [Nat.sub_zero], ?_, by simp, rfl, rfl, b1, b2⟩
    intro h1
    omega
  · obtain ⟨len, a1, a2, a3, a4, a5, a6, a7⟩ := flushAll_spec hk _ D.cmd buf space rfl hring hle hout
    unfold flushD
    dsimp only
    generalize flushAll D.k D.cmd buf space = f at a3 a4 a5 a7
    obtain ⟨b1, b2⟩ := hbits (x := f.st) (by rw [a4]) (by rw [a4])
    refine ⟨len, a1, a2, a3, ?_, a5, a6, a7, rfl, rfl, b1, b2⟩
    rw [a4]
    exact h.withPend (by omega)

/-- Handing out a state's bytes keeps a state the loop can run from. -/
theorem flushD_inv {stop : USize} {D : Dec} (h : DInv stop D) (buf : ByteArray) (space : Nat) : DInv stop (flushD D buf space).D := by
  obtain ⟨⟨p, hrel⟩, hp⟩ := h
  obtain ⟨_, _, _, _, a1, _, _, _, a2, _⟩ := flushD_spec hrel buf space
  exact ⟨⟨p, a1⟩, by rw [a2]; exact hp⟩

/-! ### A call -/

/-- What a call leaves. -/
structure Out where
  D : Dec
  buf : ByteArray
  pos : USize
  status : Status

/-- The stream's end: any bits past the fill bits are rejected, and with none, it ends here if the caller says so. -/
def endCheck (D : Dec) (stop : USize) (final : Bool) (buf : ByteArray) : Out :=
  let c := D.cmd
  let b : BitBuffer := ⟨c.word, c.count⟩
  let k := c.count &&& 7
  if b.peek k = 0 then
    let b1 := b.drop k
    if b1.count = 0 ∧ D.pos = stop then
      if final then ⟨deadD, buf, D.pos, .done⟩
      else ⟨{ D with cmd := { c with word := b1.word, count := b1.count }, status := .needsInput }, buf, D.pos, .needsInput⟩
    else ⟨deadD, buf, D.pos, .rejected⟩
  else ⟨deadD, buf, D.pos, .rejected⟩

/-- What a call does with what the loop left, unless that needs more room. -/
def afterRun (r : Dec) (stop : USize) (final : Bool) (pos0 : USize) (buf : ByteArray) (space : Nat) : Out :=
  match r.status with
  | .bad => ⟨deadD, buf, pos0, .rejected⟩
  | .memory => ⟨deadD, buf, pos0, .memoryLimit⟩
  | .needsInput =>
    let f := flushD r buf space
    if f.D.cmd.pend = 0 then
      if final then ⟨deadD, f.buf, f.D.pos, .rejected⟩ else ⟨f.D, f.buf, f.D.pos, .needsInput⟩
    else ⟨f.D, f.buf, f.D.pos, .needsOutput⟩
  | .next =>
    let f := flushD r buf space
    if f.D.cmd.pend = 0 then endCheck f.D stop final f.buf else ⟨f.D, f.buf, f.D.pos, .needsOutput⟩
  | .needsOutput => ⟨r, buf, r.pos, .needsOutput⟩

/-- The loop stopped with the window full: a state it can go on from. -/
theorem runD_full {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {h : DInv stop D} (hn : (runD a stop hs D h).status = .needsOutput) :
    DInv stop (runD a stop hs D h) := by
  obtain ⟨p, hrel⟩ := h.1
  obtain ⟨p', a1, _, a2, _⟩ := (runD_ok (hs := hs) ⟨D, h⟩ p hrel).needsOutput hn
  exact ⟨⟨p', a1⟩, a2⟩

/-- The cap on waiting bytes for a round with `space` bytes of room: one more than the room, so that a round decodes no more
than it can hand out and one byte, and stops for output space only with a byte waiting. -/
def capFor (space : Nat) : USize := USize.ofNat (min space 16777216 + 1)

/-- A state with the cap for a round. -/
@[inline] def withCap (D : Dec) (space : Nat) : Dec := { D with cmd := { D.cmd with cap := capFor space } }

theorem DInv.withCap {stop : USize} {D : Dec} (h : DInv stop D) (space : Nat) : DInv stop (withCap D space) := by
  obtain ⟨⟨p, hrel⟩, hp⟩ := h
  exact ⟨⟨p, hrel.withCap _⟩, hp⟩

/-- Runs the loop, handing out what it leaves, until the input or the room runs out or the stream stops. -/
def callD (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (final : Bool) (D : Dec) (h : DInv stop D) (buf : ByteArray) (space : Nat) : Out :=
  let pos0 := D.pos
  let r := runD a stop hs (withCap D space) (h.withCap space)
  if hO : r.status = .needsOutput then
    let f := flushD r buf space
    if f.D.cmd.pend = 0 then
      if _hlt : f.space < space then callD a stop hs final f.D (flushD_inv (runD_full hO) buf space) f.buf f.space
      else ⟨deadD, f.buf, pos0, .rejected⟩
    else ⟨f.D, f.buf, f.D.pos, .needsOutput⟩
  else afterRun r stop final pos0 buf space
termination_by space
decreasing_by exact _hlt

/-! ### What a call does -/

/-- With whole bytes, the stream's end is having none left. -/
theorem endOf_whole (st : StreamState) {f : List Bool} (hf : f.length % 8 = 0) :
    endOf st f = if f.isEmpty then some (st.output.reverse.map Nat.toUInt8) else none := by
  have h := readFill_held (b := ⟨0, 0⟩) f hf
  have e : readFill f = some f := by
    have h0 : (BitBuffer.mk 0 0).held = [] := rfl
    have h1 : (BitBuffer.mk 0 0).peek ((BitBuffer.mk 0 0).count &&& 7) = 0 := by decide
    rw [h0, List.nil_append, ite_eq_left h1] at h
    rw [h]
    rfl
  unfold endOf readEnd
  show ((readFill f >>= _) >>= _) = _
  rw [e]
  show ((if f.isEmpty then some () else none) >>= _) = _
  cases f.isEmpty <;> rfl

/-- The stream's end, in terms of the fill bits. -/
theorem endOf_held (st : StreamState) {b : BitBuffer} (hw : b.Wf) {f : List Bool} (hf : f.length % 8 = 0) :
    endOf st (b.held ++ f) = if b.peek (b.count &&& 7) = 0 then endOf st ((b.drop (b.count &&& 7)).held ++ f) else none := by
  have hr := readFill_held (b := b) f hf
  obtain ⟨fa1, _⟩ := fill_aligned hw
  have hlen : ((b.drop (b.count &&& 7)).held ++ f).length % 8 = 0 := by
    simp only [List.length_append, BitBuffer.held, lowBits_length]
    omega
  by_cases hz : b.peek (b.count &&& 7) = 0
  · rw [ite_eq_left hz] at hr ⊢
    rw [endOf_whole st hlen]
    unfold endOf readEnd
    show ((readFill _ >>= _) >>= _) = _
    rw [hr]
    show ((if ((b.drop (b.count &&& 7)).held ++ f).isEmpty then some () else none) >>= _) = _
    cases ((b.drop (b.count &&& 7)).held ++ f).isEmpty <;> rfl
  · rw [ite_eq_right hz] at hr ⊢
    unfold endOf readEnd
    show ((readFill _ >>= _) >>= _) = _
    rw [hr]
    rfl

/-- What the stream's end does. -/
theorem endCheck_ok {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {st : StreamState} {D : Dec} (hrel : DRel D (.ended st)) (hp : D.pos.toNat ≤ stop.toNat)
    (final : Bool) (buf : ByteArray) :
    D.pos.toNat ≤ (endCheck D stop final buf).pos.toNat ∧ (endCheck D stop final buf).pos.toNat ≤ stop.toNat ∧ (endCheck D stop final buf).buf = buf ∧
      (∃ p', DRel (endCheck D stop final buf).D p') ∧
      ((endCheck D stop final buf).status = .needsInput → final = false ∧ (endCheck D stop final buf).pos = stop ∧
        (endCheck D stop final buf).D.pos = (endCheck D stop final buf).pos ∧ DRel (endCheck D stop final buf).D (.ended st) ∧
        (endCheck D stop final buf).D.cmd.pend = D.cmd.pend ∧
        (∀ t : List UInt8, endOf st (D.bits a D.pos stop (bits t)) =
          endOf st ((endCheck D stop final buf).D.bits a (endCheck D stop final buf).pos stop (bits t))) ∧
        (∃ n, ∀ t : List UInt8, (D.bits a D.pos stop (bits t)).length = ((endCheck D stop final buf).D.bits a (endCheck D stop final buf).pos stop (bits t)).length + n) ∧
        (∀ t : List UInt8, Reach sStep (.ended st) (D.bits a D.pos stop (bits t)) (.ended st)
          ((endCheck D stop final buf).D.bits a (endCheck D stop final buf).pos stop (bits t))) ∧
        (endCheck D stop final buf).D.held = []) ∧
      ((endCheck D stop final buf).status = .done → final = true ∧ (endCheck D stop final buf).pos = stop ∧
        endOf st (D.bits a D.pos stop (bits [])) = some (st.output.reverse.map Nat.toUInt8)) ∧
      ((endCheck D stop final buf).status = .rejected → ∀ t : List UInt8, endOf st (D.bits a D.pos stop (bits t)) = none) ∧
      (endCheck D stop final buf).status ≠ .needsOutput ∧ (endCheck D stop final buf).status ≠ .memoryLimit := by
  have hw : (BitBuffer.mk D.cmd.word D.cmd.count).Wf := hrel.2.1
  have hne : D.tag ≠ .hdr := by rw [hrel.1]; decide
  have hb : ∀ t : List UInt8, D.bits a D.pos stop (bits t) = (BitBuffer.mk D.cmd.word D.cmd.count).held ++ (chunkBits a D.pos.toNat stop.toNat ++ bits t) :=
    fun t => Dec.bits_cmd hne a D.pos stop (bits t)
  have hfill := fun t : List UInt8 => endOf_held st hw (whole_bytes (p := D.pos.toNat) hs t)
  have hd : (∃ p', DRel deadD p') := ⟨_, deadD_rel⟩
  unfold endCheck
  dsimp only
  by_cases hz : (BitBuffer.mk D.cmd.word D.cmd.count).peek (D.cmd.count &&& 7) = 0
  · rw [ite_eq_left hz]
    obtain ⟨fa1, fa2⟩ := fill_aligned hw
    by_cases hc : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count = 0 ∧ D.pos = stop
    · rw [ite_eq_left hc]
      obtain ⟨hc0, hps⟩ := hc
      have hc0N : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count.toNat = 0 := by rw [hc0]; rfl
      have hheld : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).held = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [BitBuffer.held, lowBits_length]
        exact hc0N
      have hchunk : chunkBits a D.pos.toNat stop.toNat = [] := by
        apply List.eq_nil_of_length_eq_zero
        rw [chunkBits_length hs, hps]
        simp
      have hall : ∀ t : List UInt8, endOf st (D.bits a D.pos stop (bits t)) = endOf st (bits t) := by
        intro t
        rw [hb, hfill, ite_eq_left (show (BitBuffer.mk D.cmd.word D.cmd.count).peek ((BitBuffer.mk D.cmd.word D.cmd.count).count &&& 7) = 0 from hz), hheld, hchunk]
        rfl
      cases final with
      | true =>
        refine ⟨Nat.le_refl _, hp, rfl, hd, fun e => Status.noConfusion e, fun _ => ⟨rfl, hps, ?_⟩, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
        rw [hall, endOf_whole st (by rw [bits_length]; simp)]
        rfl
      | false =>
        generalize hb1 : (BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7) = b1 at hheld fa2
        have hb2 : ∀ t : List UInt8, Dec.bits { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } a D.pos stop (bits t) = bits t := by
          intro t
          have e : Dec.bits { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } a D.pos stop (bits t) =
              b1.held ++ (chunkBits a D.pos.toNat stop.toNat ++ bits t) :=
            Dec.bits_cmd (D := { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput }) hne a D.pos stop (bits t)
          rw [e, hheld, hchunk]
          rfl
        have hrelN : DRel { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } (.ended st) := by
          obtain ⟨a1, _, w, a3⟩ := hrel
          exact ⟨a1, fa2, w, ⟨{ a3.win with }, a3.produced, a3.limit⟩⟩
        show D.pos.toNat ≤ D.pos.toNat ∧ D.pos.toNat ≤ stop.toNat ∧ buf = buf ∧ (∃ p', DRel { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } p') ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
        refine ⟨Nat.le_refl _, hp, rfl, ⟨.ended st, hrelN⟩, fun _ => ⟨rfl, hps, rfl, hrelN, rfl, (fun t => ?_), ⟨(BitBuffer.mk D.cmd.word D.cmd.count).count.toNat, fun t => ?_⟩,
          (fun t => ?_), ?_⟩, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
        · rw [hall]
          show _ = endOf st (Dec.bits { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } a D.pos stop (bits t))
          rw [hb2]
        · show _ = (Dec.bits { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } a D.pos stop (bits t)).length + _
          rw [hb2, hb, hchunk]
          simp only [List.nil_append, List.length_append, BitBuffer.held, lowBits_length]
          omega
        · show Reach sStep (.ended st) _ (.ended st) (Dec.bits { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } a D.pos stop (bits t))
          rw [hb2, hb, hchunk, List.nil_append]
          have hfr := readFill_held (b := BitBuffer.mk D.cmd.word D.cmd.count) (bits t) (by rw [bits_length]; omega)
          rw [ite_eq_left (show (BitBuffer.mk D.cmd.word D.cmd.count).peek ((BitBuffer.mk D.cmd.word D.cmd.count).count &&& 7) = 0 from hz), hb1, hheld,
            List.nil_append] at hfr
          by_cases hc8 : ((BitBuffer.mk D.cmd.word D.cmd.count).held ++ bits t).length % 8 = 0
          · have hf0 : readFill ((BitBuffer.mk D.cmd.word D.cmd.count).held ++ bits t) = some ((BitBuffer.mk D.cmd.word D.cmd.count).held ++ bits t) := by
              unfold readFill
              rw [hc8]
              rfl
            rw [hf0] at hfr
            rw [Option.some.inj hfr]
            exact Reach.refl _ _
          · refine Reach.one ?_
            simp only [sStep, hc8, ↓reduceIte, hfr]
        · show Dec.held { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } = []
          rw [Dec.held_cmd (D := { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput }) hne]
          exact hheld
    · rw [ite_eq_right hc]
      refine ⟨Nat.le_refl _, hp, rfl, hd, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun _ t => ?_, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
      rw [hb, hfill, ite_eq_left (show (BitBuffer.mk D.cmd.word D.cmd.count).peek ((BitBuffer.mk D.cmd.word D.cmd.count).count &&& 7) = 0 from hz)]
      have hl : (((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).held ++ (chunkBits a D.pos.toNat stop.toNat ++ bits t)).length % 8 = 0 := by
        have := whole_bytes (a := a) (p := D.pos.toNat) hs t
        have fa1' : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count.toNat % 8 = 0 := fa1
        simp only [List.length_append, BitBuffer.held, lowBits_length] at this ⊢
        omega
      rw [endOf_whole st hl]
      have hnz : (((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).held ++ (chunkBits a D.pos.toNat stop.toNat ++ bits t)).isEmpty = false := by
        rw [List.isEmpty_eq_false_iff]
        intro he
        have hlen := congrArg List.length he
        simp only [List.length_append, BitBuffer.held, lowBits_length, chunkBits_length hs, List.length_nil] at hlen
        apply hc
        constructor
        · exact UInt64.toNat_inj.mp (by show _ = 0; omega)
        · exact USize.toNat_inj.mp (by omega)
      rw [hnz]
      rfl
  · rw [ite_eq_right hz]
    refine ⟨Nat.le_refl _, hp, rfl, hd, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun _ t => ?_, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
    rw [hb, hfill, ite_eq_right (show ¬ (BitBuffer.mk D.cmd.word D.cmd.count).peek ((BitBuffer.mk D.cmd.word D.cmd.count).count &&& 7) = 0 from hz)]

/-- The bytes handed out so far: those of a place's output not waiting. -/
def Pend (p : SPhase) (D : Dec) (E : List Nat) : Prop := (p.out.drop D.cmd.pend.toNat).reverse = E

/-- A move adds only bytes that wait. -/
theorem Pend.move {p p' : SPhase} {D r : Dec} {E : List Nat} (h : Pend p D E) (ho : OutD p p' D r) : Pend p' r E := by
  obtain ⟨l, h1, h2⟩ := ho
  unfold Pend at h ⊢
  rw [h1, h2, ← h]
  congr 1
  rw [List.drop_append]
  have e1 : l.drop (D.cmd.pend.toNat + l.length) = [] := List.drop_eq_nil_of_le (by omega)
  have e2 : D.cmd.pend.toNat + l.length - l.length = D.cmd.pend.toNat := by omega
  rw [e1, e2, List.nil_append]

/-- A state's waiting bytes are in its place's output. -/
theorem DRel.pendOut {D : Dec} {p : SPhase} (h : DRel D p) : D.cmd.pend.toNat ≤ p.out.length := by
  rcases h.window with h0 | ⟨_, _, h2, _⟩
  · have : D.cmd.pend.toNat = 0 := by rw [h0]; rfl
    omega
  · exact h2

/-- Handing bytes out moves them from waiting to handed out. -/
theorem Pend.flush {p : SPhase} {D D' : Dec} {E : List Nat} {len : Nat} (h : Pend p D E) (hrel : DRel D p) (hl : len ≤ D.cmd.pend.toNat)
    (he : D'.cmd.pend.toNat = D.cmd.pend.toNat - len) : Pend p D' (E ++ ((p.out.take D.cmd.pend.toNat).reverse).take len) := by
  unfold Pend at h ⊢
  rw [he, drop_take_reverse hrel.pendOut hl, h]

/-- How many bytes were handed out. -/
theorem flush_length {p : SPhase} {D : Dec} {len : Nat} (hrel : DRel D p) (hl : len ≤ D.cmd.pend.toNat) :
    (((p.out.take D.cmd.pend.toNat).reverse).take len).length = len := by
  have := hrel.pendOut
  simp only [List.length_take, List.length_reverse]
  omega

/-- A state's bits at the chunk's end are the bits it holds. -/
theorem Dec.bits_stop {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) (D : Dec) (F : List Bool) : D.bits a stop stop F = D.held ++ F := by
  have hchunk : chunkBits a stop.toNat stop.toNat = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [chunkBits_length hs]
    simp
  show (BitBuffer.mk D.word D.count).held ++ (chunkBits a stop.toNat stop.toNat ++ F) = _
  rw [hchunk]
  rfl

/-- What a call must do. `E` is the bytes handed out before it. -/
structure CallOk (a : ByteArray) (stop : USize) (final : Bool) (p : SPhase) (D : Dec) (E : List Nat) (buf : ByteArray) (space : Nat) (o : Out) : Prop where
  posLe : D.pos.toNat ≤ o.pos.toNat
  posStop : o.pos.toNat ≤ stop.toNat
  rel : ∃ p', DRel o.D p'
  new : ∃ n : List Nat, o.buf.data.toList.map UInt8.toNat = buf.data.toList.map UInt8.toNat ++ n ∧ n.length ≤ space ∧
    (o.status = .needsInput → final = false ∧ o.pos = stop ∧ o.D.pos = o.pos ∧ ∃ p', DRel o.D p' ∧ Pend p' o.D (E ++ n) ∧
      (∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem p' (o.D.bits a o.pos stop (bits t))) ∧
      (∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (o.D.bits a o.pos stop (bits t))) ∧ SPause p' o.D.held) ∧
    (o.status = .needsOutput → n.length = space ∧ o.D.pos = o.pos ∧ ∃ p', DRel o.D p' ∧ Pend p' o.D (E ++ n) ∧
      (∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem p' (o.D.bits a o.pos stop (bits t))) ∧
      ∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (o.D.bits a o.pos stop (bits t))) ∧
    (o.status = .done → final = true ∧ o.pos = stop ∧ srest specSem p (D.bits a D.pos stop (bits [])) = some ((E ++ n).map Nat.toUInt8)) ∧
    (o.status = .rejected → ∀ t : List UInt8, (final = true → t = []) → srest specSem p (D.bits a D.pos stop (bits t)) = none) ∧
    (o.status = .memoryLimit → (∀ (t : List UInt8) (y : List UInt8), srest specSem p (D.bits a D.pos stop (bits t)) = some y → (E ++ n).map Nat.toUInt8 <+: y) ∧
      ∃ p' D', DRel D' p' ∧ D.pos.toNat ≤ D'.pos.toNat ∧ D'.pos.toNat ≤ stop.toNat ∧ Pend p' D' (E ++ n) ∧
        (∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (D'.bits a D'.pos stop (bits t))) ∧ D'.cmd.pend = 0 ∧
        (p' = .wbits ∨ ∃ w st last mlen g q, p' = .hdr w st last mlen g q))

/-- The bytes handed out are the start of any output a place gets to. -/
theorem Pend.prefix {p : SPhase} {D : Dec} {E : List Nat} {y : List UInt8} (h : Pend p D E) (hx : Ext p.out y) : E.map Nat.toUInt8 <+: y := by
  unfold Pend at h
  unfold Ext at hx
  rw [← List.take_append_drop D.cmd.pend.toNat p.out, List.reverse_append, List.map_append, h] at hx
  exact (List.prefix_append _ _).trans hx

/-- A call that stopped, with no bytes handed out. -/
private theorem callOk_stop {a : ByteArray} {stop : USize} {final : Bool} {p : SPhase} {D : Dec} {E : List Nat} {buf : ByteArray} {space : Nat} {s : Status}
    (hp : D.pos.toNat ≤ stop.toNat) (hE : Pend p D E) (hr : s = .rejected → ∀ t : List UInt8, (final = true → t = []) → srest specSem p (D.bits a D.pos stop (bits t)) = none)
    (h1 : s ≠ .needsInput) (h2 : s ≠ .needsOutput) (h3 : s ≠ .done)
    (hm : s = .memoryLimit → ∃ p' D', DRel D' p' ∧ D.pos.toNat ≤ D'.pos.toNat ∧ D'.pos.toNat ≤ stop.toNat ∧ Pend p' D' E ∧
      (∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (D'.bits a D'.pos stop (bits t))) ∧ D'.cmd.pend = 0 ∧
      (p' = .wbits ∨ ∃ w st last mlen g q, p' = .hdr w st last mlen g q)) :
    CallOk a stop final p D E buf space ⟨deadD, buf, D.pos, s⟩ :=
  ⟨Nat.le_refl _, hp, ⟨_, deadD_rel⟩, [], by simp, Nat.zero_le _, fun e => absurd e h1, fun e => absurd e h2, fun e => absurd e h3, hr,
    fun e => ⟨fun t y hy => by rw [List.append_nil]; exact hE.prefix (srest_out hy), by rw [List.append_nil]; exact hm e⟩⟩

/-- A call that paused for room after handing out what it could. -/
private theorem callOk_full {a : ByteArray} {stop : USize} {final : Bool} {p p' : SPhase} {D r : Dec} {E : List Nat} {buf : ByteArray} {space : Nat}
    (hp : D.pos.toNat ≤ r.pos.toNat) (hps : r.pos.toNat ≤ stop.toNat) (hR : DRel r p') (hE : Pend p' r E)
    (heq : ∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = srest specSem p' (r.bits a r.pos stop (bits t)))
    (hj : ∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p' (r.bits a r.pos stop (bits t)))
    (hz : ¬ (flushD r buf space).D.cmd.pend = 0) :
    CallOk a stop final p D E buf space ⟨(flushD r buf space).D, (flushD r buf space).buf, (flushD r buf space).D.pos, .needsOutput⟩ := by
  obtain ⟨len, a1, a2, _, a4, a5, a6, a7, a8, _, a9, _⟩ := flushD_spec hR buf space
  have hzN : (flushD r buf space).D.cmd.pend.toNat ≠ 0 := fun e => hz (USize.toNat_inj.mp e)
  refine ⟨by show _ ≤ (flushD r buf space).D.pos.toNat; rw [a8]; exact hp, by show (flushD r buf space).D.pos.toNat ≤ _; rw [a8]; exact hps, ⟨p', a4⟩,
    _, a7, by rw [flush_length hR a1]; exact a2, fun e => Status.noConfusion e, fun _ => ⟨?_, rfl, p', a4, hE.flush hR a1 a5, (fun t => ?_), fun t => ?_⟩,
    fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
  · rw [flush_length hR a1]
    have := a6 (by omega)
    omega
  · rw [heq]
    show _ = srest specSem p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t))
    rw [a8, a9]
  · show Reach sStep p _ p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t))
    rw [a8, a9]
    exact hj t

/-- What a call does with what the loop left. -/
theorem afterRun_ok {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {final : Bool} {p : SPhase} {D r : Dec} {E : List Nat} (hp : D.pos.toNat ≤ stop.toNat) (hE : Pend p D E)
    (hr : RunD a stop p D r) (hn : r.status ≠ .needsOutput) (buf : ByteArray) (space : Nat) : CallOk a stop final p D E buf space (afterRun r stop final D.pos buf space) := by
  unfold afterRun
  cases hst : r.status with
  | needsOutput => exact absurd hst hn
  | bad =>
    exact callOk_stop hp hE (fun _ t _ => hr.bad hst t) (fun e => Status.noConfusion e) (fun e => Status.noConfusion e) (fun e => Status.noConfusion e)
      (fun e => Status.noConfusion e)
  | memory =>
    obtain ⟨p', D', b1, b2, b3, b4, b5, b6, b7⟩ := hr.memory hst
    exact callOk_stop hp hE (fun e => Status.noConfusion e) (fun e => Status.noConfusion e) (fun e => Status.noConfusion e) (fun e => Status.noConfusion e)
      (fun _ => ⟨p', D', b1, b2, b3, hE.move b4, b5, b6, b7⟩)
  | needsInput =>
    obtain ⟨b1, b2, p', hR, ho, heq, hnone, hj, hsh⟩ := hr.needsInput hst
    have hE' := hE.move ho
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      obtain ⟨len, a1, a2, _, a4, a5, _, a7, a8, _, a9, a10⟩ := flushD_spec hR buf space
      have hps : (flushD r buf space).D.pos = stop := a8.trans b1
      cases final with
      | true =>
        refine ⟨by rw [show (flushD r buf space).D.pos = stop from hps]; exact b2, by rw [show (flushD r buf space).D.pos = stop from hps]; exact Nat.le_refl _, ⟨_, deadD_rel⟩,
          _, a7, by rw [flush_length hR a1]; exact a2, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e, (fun _ t ht => ?_), fun e => Status.noConfusion e⟩
        have ht0 := ht rfl
        subst ht0
        rw [heq, b1, Dec.bits_stop hs]
        show srest specSem p' (r.held ++ []) = none
        rw [List.append_nil]
        exact hnone
      | false =>
        show CallOk a stop false p D E buf space ⟨(flushD r buf space).D, (flushD r buf space).buf, (flushD r buf space).D.pos, .needsInput⟩
        refine ⟨by rw [show (flushD r buf space).D.pos = stop from hps]; exact b2, by rw [show (flushD r buf space).D.pos = stop from hps]; exact Nat.le_refl _, ⟨p', a4⟩,
          _, a7, by rw [flush_length hR a1]; exact a2, fun _ => ⟨rfl, hps, rfl, p', a4, hE'.flush hR a1 a5, (fun t => ?_), (fun t => ?_), ?_⟩,
          fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
        · rw [heq, b1]
          show _ = srest specSem p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t))
          rw [hps, a9]
        · have := hj t
          rw [b1] at this
          show Reach sStep p _ p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t))
          rw [hps, a9]
          exact this
        · show SPause p' (flushD r buf space).D.held
          rw [a10]
          exact hsh.pause
    · rw [ite_eq_right hz]
      exact callOk_full (by rw [b1]; exact b2) (by rw [b1]; exact Nat.le_refl _) hR hE' heq hj hz
  | next =>
    obtain ⟨st, hR, b1, b2, ho, heq, hj⟩ := hr.next hst
    have hE' := hE.move ho
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      obtain ⟨len, a1, a2, _, a4, a5, _, a7, a8, _, a9, _⟩ := flushD_spec hR buf space
      obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := endCheck_ok (a := a) hs (D := (flushD r buf space).D) a4 (by rw [a8]; exact b2) final (flushD r buf space).buf
      have hE2 := hE'.flush hR a1 a5
      have hchain : ∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) = endOf st ((flushD r buf space).D.bits a (flushD r buf space).D.pos stop (bits t)) := by
        intro t
        rw [heq, a8, a9]
        rfl
      refine ⟨Nat.le_trans (by rw [a8]; exact b1) c1, c2, c4, _, by rw [c3]; exact a7, by rw [flush_length hR a1]; exact a2, fun e => ?_, fun e => absurd e c8, fun e => ?_, (fun e t _ => ?_), fun e => absurd e c9⟩
      · obtain ⟨d1, d2, d3, d4, d5, d6, _, d7, d8⟩ := c5 e
        refine ⟨d1, d2, d3, .ended st, d4, ?_, (fun t => ?_), (fun t => ?_), ?_⟩
        · unfold Pend at hE2 ⊢
          rw [d5]
          exact hE2
        · rw [hchain, d6]
          rfl
        · have h7 := d7 t
          rw [a8, a9] at h7
          exact (hj t).trans h7
        · rw [d8]
          exact ⟨.ended st, [], .refl _ _, rfl, Or.inr ⟨st.output.reverse.map Nat.toUInt8, by simp [sStep]⟩⟩
      · obtain ⟨d1, d2, d3⟩ := c6 e
        refine ⟨d1, d2, ?_⟩
        rw [hchain, d3]
        unfold Pend at hE2
        have h0 : (flushD r buf space).D.cmd.pend.toNat = 0 := by rw [hz]; rfl
        rw [h0] at hE2
        show _ = some (List.map Nat.toUInt8 _)
        rw [← hE2]
        rfl
      · rw [hchain]
        exact c7 e t
    · rw [ite_eq_right hz]
      exact callOk_full b1 b2 hR hE' heq hj hz

/-- What a call does. -/
theorem callD_ok {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} : ∀ (space : Nat) (D : Dec) (h : DInv stop D) (p : SPhase) (E : List Nat) (buf : ByteArray),
    DRel D p → Pend p D E → CallOk a stop final p D E buf space (callD a stop hs final D h buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h p E buf hrel hE
    rw [callD]
    dsimp only
    have hr := (runD_ok (hs := hs) ⟨withCap D space, h.withCap space⟩ p (hrel.withCap _)).uncap
    dsimp only at hr
    by_cases hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO]
      obtain ⟨p', hR, b1, b2, ho, heq, hfull, hj⟩ := hr.needsOutput hO
      have hE' := hE.move ho
      obtain ⟨len, a1, a2, a3, a4, a5, _, a7, a8, _, a9, _⟩ := flushD_spec hR buf space
      by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz]
        have hz0 : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat = 0 := by rw [hz]; rfl
        have hpos : 1 ≤ 2 ^ (runD a stop hs (withCap D space) (h.withCap space)).k.toNat := Nat.two_pow_pos _
        have hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space := by
          rw [a3]
          omega
        rw [dite_eq_left hlt]
        have hin := ih _ hlt (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D (flushD_inv (runD_full hO) buf space) p' _ (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf a4 (hE'.flush hR a1 a5)
        generalize callD a stop hs final (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D (flushD_inv (runD_full hO) buf space)
          (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space = o at hin ⊢
        obtain ⟨c1, c2, c3, n, c4, c5, c6, c7, c8, c9, c10⟩ := hin
        have hchain : ∀ t : List UInt8, srest specSem p (D.bits a D.pos stop (bits t)) =
            srest specSem p' ((flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.bits a (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.pos stop (bits t)) := by
          intro t
          rw [heq, a8, a9]
        have hjoin : ∀ t : List UInt8, Reach sStep p (D.bits a D.pos stop (bits t)) p'
            ((flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.bits a (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.pos stop (bits t)) := by
          intro t
          rw [a8, a9]
          exact hj t
        rw [a7] at c4
        have hl1 := flush_length (p := p') hR a1
        refine ⟨Nat.le_trans (by rw [a8]; exact b1) c1, c2, c3, ((p'.out.take (runD a stop hs (withCap D space) (h.withCap space)).cmd.pend.toNat).reverse).take len ++ n,
          by rw [c4, List.append_assoc], ?_, fun e => ?_, fun e => ?_, fun e => ?_, (fun e t ht => ?_), fun e => ⟨fun t y hy => ?_, ?_⟩⟩
        · rw [List.length_append, hl1]
          rw [a3] at c5
          omega
        · obtain ⟨d1, d2, d3, p2, d4, d5, d6, d7, d8⟩ := c6 e
          refine ⟨d1, d2, d3, p2, d4, by rw [← List.append_assoc]; exact d5, (fun t => ?_), (fun t => (hjoin t).trans (d7 t)), d8⟩
          rw [hchain, d6]
        · obtain ⟨d1, d2, p2, d4, d5, d6, d7⟩ := c7 e
          refine ⟨?_, d2, p2, d4, by rw [← List.append_assoc]; exact d5, (fun t => ?_), fun t => (hjoin t).trans (d7 t)⟩
          · rw [List.length_append, hl1, d1, a3]
            omega
          · rw [hchain, d6]
        · obtain ⟨d1, d2, d3⟩ := c8 e
          refine ⟨d1, d2, ?_⟩
          rw [hchain, d3, ← List.append_assoc]
        · rw [hchain]
          exact c9 e t ht
        · rw [hchain] at hy
          rw [← List.append_assoc]
          exact (c10 e).1 t y hy
        · obtain ⟨p2, D2, d1, d2, d3, d4, d5, d6, d7⟩ := (c10 e).2
          refine ⟨p2, D2, d1, Nat.le_trans (by rw [a8]; exact b1) d2, d3, by rw [← List.append_assoc]; exact d4,
            fun t => (hjoin t).trans (d5 t), d6, d7⟩
      · rw [ite_eq_right hz]
        exact callOk_full b1 b2 hR hE' heq hj hz
    · rw [dite_eq_right hO]
      exact afterRun_ok hs h.2 hE hr hO buf space

/-! ### What a call does to the measure -/

theorem MLt.trans {a b c : Meas} (h1 : MLt a b) (h2 : MLt b c) : MLt a c := by
  rcases h1 with h | ⟨e1, h⟩
  · rcases h2 with h' | ⟨e2, _⟩
    · exact Or.inl (Nat.lt_trans h h')
    · exact Or.inl (by rw [← e2]; exact h)
  · rcases h2 with h' | ⟨e2, h'⟩
    · exact Or.inl (by rw [e1]; exact h')
    · refine Or.inr ⟨e1.trans e2, ?_⟩
      rcases h with h | ⟨e3, h⟩
      · rcases h' with h' | ⟨e4, _⟩
        · exact Or.inl (Nat.lt_trans h h')
        · exact Or.inl (by rw [← e4]; exact h)
      · rcases h' with h' | ⟨e4, h'⟩
        · exact Or.inl (by rw [e3]; exact h')
        · exact Or.inr ⟨e3.trans e4, h.trans h'⟩

/-- What the loop does to the measure. -/
structure RunM (a : ByteArray) (stop : USize) (p : SPhase) (D r : Dec) : Prop where
  next : r.status = .next → ∃ st, DRel r (.ended st) ∧ r.pos.toNat ≤ stop.toNat ∧ MPause a stop p (.ended st) D D.pos r
  needsInput : r.status = .needsInput → ∃ p', DRel r p' ∧ MPause a stop p p' D D.pos r
  needsOutput : r.status = .needsOutput → ∃ p', DRel r p' ∧ r.cmd.pend.toNat ≠ 0 ∧ MPause a stop p p' D D.pos r

/-- The cap on waiting bytes changes nothing the loop's measure says of where it started. -/
theorem RunM.uncap {a : ByteArray} {stop : USize} {p : SPhase} {D r : Dec} {x : USize}
    (h : RunM a stop p { D with cmd := { D.cmd with cap := x } } r) : RunM a stop p D r :=
  ⟨h.1, h.2, h.3⟩

/-- A step that moved on, then a pause, lowers the measure. -/
private theorem MPause.after {a : ByteArray} {stop : USize} {p p1 p' : SPhase} {D r1 r : Dec}
    (h1 : ∀ t : List UInt8, MLt (mOf p1 (r1.bits a r1.pos stop (bits t))) (mOf p (D.bits a D.pos stop (bits t)))) (h2 : MPause a stop p1 p' r1 r1.pos r) :
    MPause a stop p p' D D.pos r := by
  rcases h2 with h | ⟨_, h⟩
  · exact Or.inl fun t => (h t).trans (h1 t)
  · exact Or.inl fun t => by rw [h t]; exact h1 t

/-- What the loop does to the measure. -/
theorem runD_down {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} : ∀ (x : RunArg a stop hs) (p : SPhase), DRel x.D p →
    RunM a stop p x.D (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    intro p hrel
    obtain ⟨D, hinv⟩ := x
    dsimp only at hrel ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      cases p with
      | ended st =>
        have hrel' : DRel { D with status := .next } (.ended st) := hrel.congr rfl rfl rfl rfl rfl rfl rfl rfl
        exact ⟨fun _ => ⟨st, hrel', hinv.2, Or.inr ⟨rfl, fun t => rfl⟩⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      | wbits => exact absurd (he.symm.trans hrel.1) (by decide)
      | mblock => exact absurd (he.symm.trans hrel.1) (by decide)
      | skip => exact absurd (he.symm.trans hrel.1) (by decide)
      | raw => exact absurd (he.symm.trans hrel.1) (by decide)
      | hdr => exact absurd (he.symm.trans hrel.1) (by decide)
      | cmds => exact absurd (he.symm.trans hrel.1) (by decide)
    · rw [dite_eq_right he]
      dsimp only
      have hstep := stepD_down (a := a) (hs := hs) hrel he hinv.2
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        obtain ⟨p', hR, _, _, h3⟩ := hstep.next hn
        have hih := ih ⟨stepD a stop hs D, hinv.step he hn⟩ ⟨he, hn, rfl⟩ p' hR
        dsimp only at hih
        generalize runD a stop hs (stepD a stop hs D) (hinv.step he hn) = r at hih ⊢
        refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
        · obtain ⟨st, b1, b0, b2⟩ := hih.next e
          exact ⟨st, b1, b0, MPause.after h3 b2⟩
        · obtain ⟨p2, b1, b2⟩ := hih.needsInput e
          exact ⟨p2, b1, MPause.after h3 b2⟩
        · obtain ⟨p2, b1, b2, b3⟩ := hih.needsOutput e
          exact ⟨p2, b1, b2, MPause.after h3 b3⟩
      · rw [dite_eq_right hn]
        refine ⟨fun e => absurd e hn, fun e => ?_, fun e => ?_⟩
        · obtain ⟨_, p2, b1, b2⟩ := hstep.needsInput e
          exact ⟨p2, b1, b2⟩
        · obtain ⟨p2, b1, _, _, b2, b3⟩ := hstep.needsOutput e
          exact ⟨p2, b1, b2, b3⟩

/-- A call's effect on the measure, and on the bytes waiting: lower, or the same with fewer bytes waiting if some could go out. -/
def MCall (a : ByteArray) (stop : USize) (p p' : SPhase) (D : Dec) (space : Nat) (o : Out) : Prop :=
  (∀ t : List UInt8, MLt (mOf p' (o.D.bits a o.pos stop (bits t))) (mOf p (D.bits a D.pos stop (bits t)))) ∨
    ((∀ t : List UInt8, mOf p' (o.D.bits a o.pos stop (bits t)) = mOf p (D.bits a D.pos stop (bits t))) ∧ o.D.cmd.pend.toNat ≤ D.cmd.pend.toNat ∧
      (D.cmd.pend.toNat ≠ 0 → space ≠ 0 → o.D.cmd.pend.toNat < D.cmd.pend.toNat))

/-- What a call does to the measure. -/
structure CallM (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (space : Nat) (o : Out) : Prop where
  needsInput : o.status = .needsInput → o.D.cmd.pend = 0 ∧ ∃ p', DRel o.D p' ∧ MCall a stop p p' D space o
  needsOutput : o.status = .needsOutput → o.D.cmd.pend ≠ 0 ∧ ∃ p', DRel o.D p' ∧ MCall a stop p p' D space o

/-- Handing out a state's bytes, after a pause. -/
private theorem mcall_flush {a : ByteArray} {stop : USize} {p p' : SPhase} {D r : Dec} {buf : ByteArray} {space : Nat} {status : Status} (hR : DRel r p')
    (h : MPause a stop p p' D D.pos r) :
    MCall a stop p p' D space ⟨(flushD r buf space).D, (flushD r buf space).buf, (flushD r buf space).D.pos, status⟩ := by
  obtain ⟨len, a1, a2, _, _, a5, a6, _, a8, _, a9, _⟩ := flushD_spec hR buf space
  rcases h with h | ⟨h1, h2⟩
  · refine Or.inl fun t => ?_
    show MLt (mOf p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t))) _
    rw [a8, a9]
    exact h t
  · refine Or.inr ⟨fun t => ?_, ?_, fun h3 h4 => ?_⟩
    · show mOf p' (Dec.bits _ a (flushD r buf space).D.pos stop (bits t)) = _
      rw [a8, a9]
      exact h2 t
    · show (flushD r buf space).D.cmd.pend.toNat ≤ _
      rw [a5, h1]
      omega
    · show (flushD r buf space).D.cmd.pend.toNat < _
      rw [a5, ← h1] at *
      by_cases h5 : r.cmd.pend.toNat - len = 0
      · omega
      · have := a6 h5
        omega

/-- What a call does with what the loop left, to the measure. -/
theorem afterRun_down {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {final : Bool} {p : SPhase} {D r : Dec}
    (hr : RunM a stop p D r) (hn : r.status ≠ .needsOutput) (buf : ByteArray) (space : Nat) : CallM a stop p D space (afterRun r stop final D.pos buf space) := by
  unfold afterRun
  cases hst : r.status with
  | needsOutput => exact absurd hst hn
  | bad => exact ⟨fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
  | memory => exact ⟨fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
  | needsInput =>
    obtain ⟨p', hR, hm⟩ := hr.needsInput hst
    obtain ⟨_, _, _, _, a4, _, _, _, _, _, _, _⟩ := flushD_spec hR buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      cases final with
      | true => exact ⟨fun e => Status.noConfusion e, fun e => Status.noConfusion e⟩
      | false => exact ⟨fun _ => ⟨hz, p', a4, mcall_flush hR hm⟩, fun e => Status.noConfusion e⟩
    · rw [ite_eq_right hz]
      exact ⟨fun e => Status.noConfusion e, fun _ => ⟨hz, p', a4, mcall_flush hR hm⟩⟩
  | next =>
    obtain ⟨st, hR, hp, hm⟩ := hr.next hst
    obtain ⟨_, _, _, _, a4, _, _, _, a8, _, a9, _⟩ := flushD_spec hR buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      obtain ⟨_, _, _, _, c5, _, _, c8, _⟩ := endCheck_ok (a := a) hs (D := (flushD r buf space).D) a4 (by rw [a8]; exact hp) final (flushD r buf space).buf
      generalize endCheck (flushD r buf space).D stop final (flushD r buf space).buf = o at c5 c8 ⊢
      refine ⟨fun e => ?_, fun e => absurd e c8⟩
      obtain ⟨_, _, _, d4, d5, _, ⟨n, d6⟩, _, _⟩ := c5 e
      have hz0 : o.D.cmd.pend = 0 := d5.trans hz
      have hz0N : o.D.cmd.pend.toNat = 0 := by rw [hz0]; rfl
      refine ⟨hz0, .ended st, d4, ?_⟩
      have hf : ∀ t : List UInt8, (flushD r buf space).D.bits a (flushD r buf space).D.pos stop (bits t) = r.bits a r.pos stop (bits t) := by
        intro t
        rw [a8, a9]
      by_cases hn0 : n = 0
      · have he1 : ∀ t : List UInt8, mOf (.ended st) (o.D.bits a o.pos stop (bits t)) = mOf (.ended st) (r.bits a r.pos stop (bits t)) := by
          intro t
          have := d6 t
          rw [hf] at this
          show ((o.D.bits a o.pos stop (bits t)).length + 1, _) = ((r.bits a r.pos stop (bits t)).length + 1, _)
          rw [this, hn0]
        rcases hm with h | ⟨_, h⟩
        · exact Or.inl fun t => by rw [he1]; exact h t
        · exact Or.inr ⟨fun t => by rw [he1]; exact h t, by omega, fun h3 _ => by omega⟩
      · have he2 : ∀ t : List UInt8, MLt (mOf (.ended st) (o.D.bits a o.pos stop (bits t))) (mOf (.ended st) (r.bits a r.pos stop (bits t))) := by
          intro t
          have := d6 t
          rw [hf] at this
          refine Or.inl ?_
          show (o.D.bits a o.pos stop (bits t)).length + 1 < (r.bits a r.pos stop (bits t)).length + 1
          omega
        rcases hm with h | ⟨_, h⟩
        · exact Or.inl fun t => (he2 t).trans (h t)
        · exact Or.inl fun t => by rw [← h t]; exact he2 t
    · rw [ite_eq_right hz]
      exact ⟨fun e => Status.noConfusion e, fun _ => ⟨hz, .ended st, a4, mcall_flush hR hm⟩⟩

/-- What a call does to the measure. -/
theorem callD_down {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} : ∀ (space : Nat) (D : Dec) (h : DInv stop D) (p : SPhase) (buf : ByteArray),
    DRel D p → CallM a stop p D space (callD a stop hs final D h buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h p buf hrel
    rw [callD]
    dsimp only
    have hr := (runD_down (hs := hs) ⟨withCap D space, h.withCap space⟩ p (hrel.withCap _)).uncap
    dsimp only at hr
    by_cases hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO]
      obtain ⟨p', hR, hfull, hm⟩ := hr.needsOutput hO
      obtain ⟨len, a1, a2, a3, a4, a5, _, _, a8, _, a9, _⟩ := flushD_spec hR buf space
      by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz]
        have hz0 : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend.toNat = 0 := by rw [hz]; rfl
        have hpos : 1 ≤ 2 ^ (runD a stop hs (withCap D space) (h.withCap space)).k.toNat := Nat.two_pow_pos _
        have hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space := by
          rw [a3]
          omega
        rw [dite_eq_left hlt]
        have hin := ih _ hlt (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D (flushD_inv (runD_full hO) buf space) p' (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf a4
        generalize callD a stop hs final (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D (flushD_inv (runD_full hO) buf space)
          (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space = o at hin ⊢
        have hf : ∀ t : List UInt8, (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.bits a (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.pos stop (bits t) =
            (runD a stop hs (withCap D space) (h.withCap space)).bits a (runD a stop hs (withCap D space) (h.withCap space)).pos stop (bits t) := by
          intro t
          rw [a8, a9]
        have hjoin : ∀ {p2 : SPhase}, MCall a stop p' p2 (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space o → MCall a stop p p2 D space o := by
          intro p2 hc
          rcases hc with hc | ⟨hc1, hc2, _⟩
          · refine Or.inl fun t => ?_
            have hc' := hc t
            rw [hf] at hc'
            rcases hm with h1 | ⟨_, h1⟩
            · exact hc'.trans (h1 t)
            · rw [← h1 t]
              exact hc'
          · have hc1' : ∀ t : List UInt8, mOf p2 (o.D.bits a o.pos stop (bits t)) = mOf p' ((runD a stop hs (withCap D space) (h.withCap space)).bits a (runD a stop hs (withCap D space) (h.withCap space)).pos stop (bits t)) := by
              intro t
              rw [hc1, hf]
            rcases hm with h1 | ⟨_, h1⟩
            · exact Or.inl fun t => by rw [hc1']; exact h1 t
            · exact Or.inr ⟨fun t => by rw [hc1', h1], by omega, fun _ _ => by omega⟩
        refine ⟨fun e => ?_, fun e => ?_⟩
        · obtain ⟨b1, p2, b2, b3⟩ := hin.needsInput e
          exact ⟨b1, p2, b2, hjoin b3⟩
        · obtain ⟨b1, p2, b2, b3⟩ := hin.needsOutput e
          exact ⟨b1, p2, b2, hjoin b3⟩
      · rw [ite_eq_right hz]
        exact ⟨fun e => Status.noConfusion e, fun _ => ⟨hz, p', a4, mcall_flush hR hm⟩⟩
    · rw [dite_eq_right hO]
      exact afterRun_down hs hr hO buf space

end Brotli.Decoder
