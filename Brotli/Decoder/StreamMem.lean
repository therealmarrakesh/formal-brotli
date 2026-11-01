import Brotli.Decoder.StreamCall

/-!
# What a state holds

Goal 3's measure and demand, and what each step does to what the state holds. The demand counts the window the stream
declares, the bytes of the tables its headers' prefix codes need, one meta-block at a time, and a fixed cost for the rest.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The demand -/

/-- What a state's fields and the buffers a header's reading needs cost. -/
def fixedCost : Nat := 1048576

/-- What a state's fields cost. -/
def fieldBytes : Nat := 1024

/-- A header's reading, counting the bytes of its tables. -/
def tableK : HK Nat := ⟨fun _ _ => some 0, fun c x => some (tableBytes c + x.getD 0)⟩

/-- The bytes of the tables a meta-block's header needs, as far as its bits go. -/
def headerTables (bs : List Bool) : Nat :=
  match metaStart bs with
  | some (.data _ _ false, b) => (hrest tableK Gh.start (.cat .L) b).getD 0
  | _ => 0

/-- The most bytes of tables any meta-block from here needs, as far as the bits go. -/
def blocksT (w : Nat) (st : StreamState) (bs : List Bool) : Nat :=
  max (headerTables bs) (match _h : readMetaBlock w st bs with
    | some ((st1, last), b) => if last then 0 else blocksT w st1 b
    | none => 0)
termination_by bs.length
decreasing_by exact readMetaBlock_lt _h

theorem blocksT_eq (w : Nat) (st : StreamState) (bs : List Bool) : blocksT w st bs =
    max (headerTables bs) ((readMetaBlock w st bs).elim 0 fun p => if p.1.2 then 0 else blocksT w p.1.1 p.2) := by
  conv => lhs; rw [blocksT]
  split <;> rename_i h <;> rw [h] <;> rfl

theorem headerTables_le (w : Nat) (st : StreamState) (bs : List Bool) : headerTables bs ≤ blocksT w st bs := by
  rw [blocksT_eq]
  exact Nat.le_max_left _ _

/-- What a place is worth to the demand: the most bytes of tables the meta-blocks after it need. -/
def demandSem : Sem Nat where
  after w last st bs := some (if last then 0 else blocksT w st bs)
  block w st bs := some (blocksT w st bs)
  finish _ _ := some 0
  first bs := readWBITS bs >>= fun p => some (blocksT (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2)
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- What a place is worth to the window: the window itself, from a meta-block's start. -/
def winSem : Sem Nat where
  after w last _ _ := some (if last then 0 else w)
  block w _ _ := some w
  finish _ _ := some 0
  first bs := readWBITS bs >>= fun p => some (windowSize p.1)
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- The bytes of the window a stream declares. -/
def windowBytes (bs : List Bool) : Nat :=
  match readWBITS bs with
  | some p => 2 ^ p.1
  | none => 0

/-- What the input so far demands. -/
def demand (y : List UInt8) : Nat := fixedCost + windowBytes (bits y) + (demandSem.first (bits y)).getD 0

theorem window_eq (bs : List Bool) : (winSem.first bs).elim 0 (· + 16) = windowBytes bs := by
  show (readWBITS bs >>= fun p => some (windowSize p.1)).elim 0 (· + 16) = _
  unfold windowBytes
  cases h : readWBITS bs with
  | none => rfl
  | some p =>
    obtain ⟨kv, r⟩ := p
    obtain ⟨h1, h2⟩ := readWBITS_range h
    exact (windowSize_range h1 h2).1

/-- Leaving a meta-block's start is worth no more than arriving at it. -/
theorem leave_le (w : Nat) (st : StreamState) (bs : List Bool) : (sLeave demandSem (.mblock w st) bs).getD 0 ≤ blocksT w st bs := by
  show (metaStart bs >>= fun p => afterStart w (demandSem.after w) st p.1 p.2).getD 0 ≤ _
  rw [← block_start w (demandSem.after w) st bs, blocksT_eq]
  cases readMetaBlock w st bs with
  | none => exact Nat.zero_le _
  | some p =>
    show (if p.1.2 = true then 0 else blocksT w p.1.1 p.2) ≤ max (headerTables bs) (if p.1.2 = true then 0 else blocksT w p.1.1 p.2)
    exact Nat.le_max_right _ _

theorem wr_tableK (oc : Option PrefixCode) (x : Option Nat) : (Wr tableK oc x).getD 0 = tableOf oc + x.getD 0 := by
  cases oc with
  | none =>
    show x.getD 0 = 0 + x.getD 0
    omega
  | some c => rfl

/-! ### The measure -/

/-- The bytes a settled record holds. -/
def Done.holds (d : Done) : Nat := d.arena.size + d.modes.size + d.lMap.size + d.dMap.size + d.litBase.size + d.icBase.size + d.dBase.size

/-- The bytes a header's reading holds. -/
def Hd.holds (h : Hd) : Nat := h.d.holds + h.fill.size + h.lens.size + h.clLens.size + h.clt.t.size + h.mapT.t.size

/-- The bytes a meta-block's fast header holds. -/
def Hdr.holds (H : Hdr) : Nat := H.arena.size + H.litBase.size + H.lMap.size + H.icBase.size + H.dBase.size + H.dMap.size + H.modes.size

/-- The bytes a state holds, and a constant for its fields. -/
def Dec.holds (D : Dec) : Nat := D.cmd.ring.size + D.cmd.seen.size + D.cmd.wordBuf.size + D.hd.holds + D.H.holds + fieldBytes

/-- The bytes a fast header holds outside its arena, with bounds set by the format. -/
structure HSmall (H : Hdr) : Prop where
  litBase : H.litBase.size ≤ 1024
  lMap : H.lMap.size ≤ 16384
  icBase : H.icBase.size ≤ 1024
  dBase : H.dBase.size ≤ 1024
  dMap : H.dMap.size ≤ 1024
  modes : H.modes.size ≤ 256

/-- Why a stream's memory limit was reached: `L` is below what it needs, and not because it was clipped. -/
def MemWhy (Ws : Option Nat) (X L : Nat) : Prop := L < Ws.elim 0 (· + 16) + X ∧ L < 4294835199

/-- What a state holds, for a stream whose window's worth is `Ws`, whose tables' worth is `X`, and with `L` left for the window and
the tables. `B` is the bits still to be read. -/
structure MemD (Ws : Option Nat) (X L : Nat) (D : Dec) (B : List Bool) : Prop where
  place : ∃ p, DRel D p ∧ (sLeave demandSem p B).getD 0 ≤ X
  block : D.tag = .mblock → headerTables B ≤ X
  hdr : D.tag = .hdr → ∃ g q, HRel D.hd g q ∧ D.hd.d.arena.size + (hrest tableK g q B).getD 0 ≤ X ∧ D.hd.d.arenaMax = D.limit ∧
    D.hd.d.arena.size + 132096 * capH q ≤ 132096 * 774
  cmds : D.tag = .cmds → D.H.arena.size ≤ X ∧ D.H.arena.size ≤ D.limit.toNat
  hdOut : D.tag ≠ .hdr → D.hd.d.arena.size = 0
  HOut : D.tag ≠ .cmds → D.H.arena.size = 0
  hd : HSize D.hd
  H : HSmall D.H
  win : (D.tag = .wbits ∧ D.cmd.ring.size = 0 ∧ D.cmd.seen.size = 0 ∧ D.cmd.wordBuf.size = 0 ∧ D.limit.toNat = L ∧ winSem.first B = Ws) ∨
    (D.tag ≠ .wbits ∧ ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L)

/-- What a state's place says of its arrays. -/
theorem DRel.arrays {D : Dec} {p : SPhase} (h : DRel D p) (ht : D.tag ≠ .wbits) :
    D.cmd.ring.size = 2 ^ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.cmd.seen.size ≤ 768 ∧ D.cmd.wordBuf.size ≤ 38 := by
  have hwin : ∀ {w st}, WinAll D w st → D.cmd.ring.size = 2 ^ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.cmd.seen.size ≤ 768 ∧ D.cmd.wordBuf.size ≤ 38 :=
    fun a => ⟨a.win.ring.size, a.win.k24, a.win.seenLe, a.win.wordLe⟩
  cases p with
  | wbits => exact absurd h.1 ht
  | mblock => exact hwin h.2.2
  | skip => exact hwin h.2.2.1
  | raw => exact hwin h.2.2.1
  | hdr => exact hwin h.2.1
  | cmds => exact h.2.2.2.2.arrays
  | ended =>
    obtain ⟨_, _, _, a⟩ := h
    exact hwin a

/-- What a state holds is within what the stream demands and what's left of the limit. -/
theorem MemD.holds_le {Ws : Option Nat} {X L : Nat} {D : Dec} {B : List Bool} (M : MemD Ws X L D B) :
    D.holds ≤ fixedCost + Ws.elim 0 (· + 16) + X ∧ D.holds ≤ fixedCost + L := by
  obtain ⟨p, hrel, _⟩ := M.place
  have a1 := M.hd.fill
  have a2 := M.hd.lens
  have a3 := M.hd.clLens
  have a4 := M.hd.clt
  have a5 := M.hd.mapT
  have a6 := M.hd.modes
  have a7 := M.hd.lMap
  have a8 := M.hd.dMap
  have a9 := M.hd.litBase
  have a10 := M.hd.icBase
  have a11 := M.hd.dBase
  have b1 := M.H.litBase
  have b2 := M.H.lMap
  have b3 := M.H.icBase
  have b4 := M.H.dBase
  have b5 := M.H.dMap
  have b6 := M.H.modes
  unfold Dec.holds Hd.holds Done.holds Hdr.holds fixedCost fieldBytes
  rcases M.win with ⟨ht, r0, s0, w0, hl, _⟩ | ⟨ht, w, hw, hk, hl⟩
  · have e1 := M.hdOut (by rw [ht]; decide)
    have e2 := M.HOut (by rw [ht]; decide)
    omega
  · obtain ⟨r1, _, s1, w1⟩ := hrel.arrays ht
    have he : (some w : Option Nat).elim 0 (· + 16) = w + 16 := rfl
    rw [hw, he]
    have hA : D.hd.d.arena.size + D.H.arena.size ≤ X ∧ D.hd.d.arena.size + D.H.arena.size ≤ D.limit.toNat := by
      by_cases t1 : D.tag = .hdr
      · obtain ⟨g, q, hR, h1, h2, _⟩ := M.hdr t1
        have h3 := M.HOut (by rw [t1]; decide)
        have hle := hR.2.1.le
        rw [h2] at hle
        omega
      · have h3 := M.hdOut t1
        by_cases t2 : D.tag = .cmds
        · obtain ⟨c1, c2⟩ := M.cmds t2
          omega
        · have h4 := M.HOut t2
          omega
    omega

/-- A state with what it holds unchanged, but for its place. -/
theorem MemD.move {Ws : Option Nat} {X L : Nat} {D D' : Dec} {B B' : List Bool} (M : MemD Ws X L D B) (hB : B' = B) (hp : ∃ p, DRel D' p ∧ (sLeave demandSem p B').getD 0 ≤ X)
    (e1 : D'.tag = D.tag) (e2 : D'.cmd.ring = D.cmd.ring) (e3 : D'.cmd.seen = D.cmd.seen) (e4 : D'.cmd.wordBuf = D.cmd.wordBuf) (e5 : D'.hd = D.hd) (e6 : D'.H = D.H)
    (e7 : D'.k = D.k) (e8 : D'.limit = D.limit) : MemD Ws X L D' B' := by
  subst hB
  refine ⟨hp, fun h => M.block (e1 ▸ h), fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
  · rw [e5, e8]
    exact M.hdr (e1 ▸ h)
  · rw [e6, e8]
    exact M.cmds (e1 ▸ h)
  · rw [e5]
    exact M.hdOut (e1 ▸ h)
  · rw [e6]
    exact M.HOut (e1 ▸ h)
  · rw [e5]
    exact M.hd
  · rw [e6]
    exact M.H
  · rw [e1, e2, e3, e4, e7, e8]
    exact M.win

/-! ### What a step leaves -/

/-- Arriving at a place, what the state holds is settled for leaving it. -/
theorem arrive {X : Nat} {D : Dec} {p : SPhase} {B : List Bool} (hrel : DRel D p) (h : (srest demandSem p B).getD 0 ≤ X) :
    (sLeave demandSem p B).getD 0 ≤ X ∧ (D.tag = .mblock → headerTables B ≤ X) := by
  cases p with
  | mblock w st =>
    have h' : blocksT w st B ≤ X := h
    exact ⟨Nat.le_trans (leave_le w st B) h', fun _ => Nat.le_trans (headerTables_le w st B) h'⟩
  | wbits => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | skip => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | raw => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | hdr => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | cmds => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | ended => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩

/-- A step's place and bits, given what the place was worth. -/
theorem placed {X : Nat} {a : ByteArray} {stop : USize} {p : SPhase} {D r : Dec} {t : List UInt8}
    (hrel : DRel D p) (hstep : DStepOk demandSem a stop p D D.pos r) (hw : (sLeave demandSem p (D.bits a D.pos stop (bits t))).getD 0 ≤ X)
    (hblock : D.tag = .mblock → headerTables (D.bits a D.pos stop (bits t)) ≤ X) (hn0 : r.status ≠ .memory) (hn1 : r.status ≠ .bad) (hpaused : r.status ≠ .next → r.tag = D.tag) :
    (∃ p', DRel r p' ∧ (sLeave demandSem p' (r.bits a r.pos stop (bits t))).getD 0 ≤ X) ∧ (r.tag = .mblock → headerTables (r.bits a r.pos stop (bits t)) ≤ X) := by
  cases hs : r.status with
  | memory => exact absurd hs hn0
  | bad => exact absurd hs hn1
  | next =>
    obtain ⟨p', hR, _, _, heq, _, _⟩ := hstep.next hs
    rw [heq] at hw
    obtain ⟨h1, h2⟩ := arrive hR hw
    exact ⟨⟨p', hR, h1⟩, h2⟩
  | needsInput =>
    obtain ⟨_, _, p', hR, heq, _, _, hb, _⟩ := hstep.needsInput hs
    rw [heq] at hw
    refine ⟨⟨p', hR, hw⟩, fun e => ?_⟩
    have ht : D.tag = .mblock := by rw [← hpaused (by rw [hs]; decide)]; exact e
    cases p with
    | mblock w st =>
      rw [hb w st rfl t]
      exact hblock ht
    | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | needsOutput =>
    obtain ⟨p', hR, _, _, heq, _, _, hb, _⟩ := hstep.needsOutput hs
    rw [heq] at hw
    refine ⟨⟨p', hR, hw⟩, fun e => ?_⟩
    have ht : D.tag = .mblock := by rw [← hpaused (by rw [hs]; decide)]; exact e
    cases p with
    | mblock w st => exact absurd rfl (hb w st)
    | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)

/-- What the loop or a step leaves, for what a state holds. -/
structure StepM (Ws : Option Nat) (X L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (r : Dec) : Prop where
  go : r.status ≠ .memory → r.status ≠ .bad → MemD Ws X L r (r.bits a r.pos stop (bits t))
  why : r.status = .memory → MemWhy Ws X L

/-- A state past WBITS and outside a header, moved to another such state. -/
theorem MemD.keep {Ws : Option Nat} {X L : Nat} {D r : Dec} {B B' : List Bool} (M : MemD Ws X L D B) (hne : D.tag ≠ .wbits) (hnh : D.tag ≠ .hdr)
    (ek : r.k = D.k) (el : r.limit = D.limit) (ed : r.hd = D.hd) (hr : r.tag ≠ .wbits) (hrh : r.tag ≠ .hdr) (hH : HSmall r.H)
    (hc : r.tag = .cmds → r.H.arena.size ≤ X ∧ r.H.arena.size ≤ r.limit.toNat) (hO : r.tag ≠ .cmds → r.H.arena.size = 0)
    (hp : ∃ p, DRel r p ∧ (sLeave demandSem p B').getD 0 ≤ X) (hb : r.tag = .mblock → headerTables B' ≤ X) : MemD Ws X L r B' := by
  refine ⟨hp, hb, fun e => absurd e hrh, hc, fun _ => by rw [ed]; exact M.hdOut hnh, hO, by rw [ed]; exact M.hd, hH, Or.inr ⟨hr, ?_⟩⟩
  rcases M.win with ⟨ht, _⟩ | ⟨_, w, h1, h2, h3⟩
  · exact absurd ht hne
  · exact ⟨w, h1, by rw [ek]; exact h2, by rw [ek, el]; exact h3⟩

private theorem ite_status_ne (c : Prop) [Decidable c] : (if c then DStatus.next else DStatus.needsInput) ≠ .memory := by
  split <;> decide

theorem stepDSkip_keeps (stop : USize) (D : Dec) (pos : USize) (ht : D.tag = .skip) :
    (stepDSkip stop D pos).k = D.k ∧ (stepDSkip stop D pos).limit = D.limit ∧ (stepDSkip stop D pos).hd = D.hd ∧ (stepDSkip stop D pos).H = D.H ∧
      (stepDSkip stop D pos).status ≠ .memory ∧ ((stepDSkip stop D pos).status ≠ .next → (stepDSkip stop D pos).tag = D.tag) ∧
      (stepDSkip stop D pos).tag ≠ .wbits ∧ (stepDSkip stop D pos).tag ≠ .hdr ∧ (stepDSkip stop D pos).tag ≠ .cmds := by
  unfold stepDSkip moveOn
  dsimp only
  have h1 : D.tag ≠ .wbits ∧ D.tag ≠ .hdr ∧ D.tag ≠ .cmds := by rw [ht]; decide
  split
  · refine ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, ?_⟩
    show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _
    split <;> decide
  · split
    · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, h1⟩
    · split
      · refine ⟨rfl, rfl, rfl, rfl, ?_, fun _ => rfl, h1⟩
        exact ite_status_ne _
      · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩

theorem stepDRaw_keeps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) (ht : D.tag = .raw) :
    (stepDRaw a stop hs D pos).k = D.k ∧ (stepDRaw a stop hs D pos).limit = D.limit ∧ (stepDRaw a stop hs D pos).hd = D.hd ∧ (stepDRaw a stop hs D pos).H = D.H ∧
      (stepDRaw a stop hs D pos).status ≠ .memory ∧ ((stepDRaw a stop hs D pos).status ≠ .next → (stepDRaw a stop hs D pos).tag = D.tag) ∧
      (stepDRaw a stop hs D pos).tag ≠ .wbits ∧ (stepDRaw a stop hs D pos).tag ≠ .hdr ∧ (stepDRaw a stop hs D pos).tag ≠ .cmds := by
  unfold stepDRaw moveOn
  dsimp only
  have h1 : D.tag ≠ .wbits ∧ D.tag ≠ .hdr ∧ D.tag ≠ .cmds := by rw [ht]; decide
  split
  · refine ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, ?_⟩
    show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _
    split <;> decide
  · split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩
      · unfold rawFinish
        dsimp only
        refine ⟨rfl, rfl, rfl, rfl, ?_, fun _ => rfl, h1⟩
        exact ite_status_ne _
    · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩

theorem stepDCmds_keeps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    (stepDCmds a stop hs D pos).k = D.k ∧ (stepDCmds a stop hs D pos).limit = D.limit ∧ (stepDCmds a stop hs D pos).hd = D.hd ∧
      (stepDCmds a stop hs D pos).status ≠ .memory ∧ ((stepDCmds a stop hs D pos).status ≠ .next → (stepDCmds a stop hs D pos).tag = D.tag) ∧
      (((stepDCmds a stop hs D pos).tag = D.tag ∧ (stepDCmds a stop hs D pos).H = D.H) ∨
        ((stepDCmds a stop hs D pos).tag ≠ .wbits ∧ (stepDCmds a stop hs D pos).tag ≠ .hdr ∧ (stepDCmds a stop hs D pos).tag ≠ .cmds ∧ (stepDCmds a stop hs D pos).H = Hdr.none)) := by
  unfold stepDCmds
  dsimp only
  generalize runCmd D.H D.k a stop hs cmdBudget D.cmd pos = r
  split
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · split
    · refine ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, Or.inr ?_⟩
      show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ _
      refine ⟨?_, ?_, ?_, rfl⟩ <;> split <;> decide
    · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- `Hdr.none` holds nothing. -/
theorem hsmall_none : HSmall Hdr.none := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- `Hd.none` holds only small tables. -/
theorem hsize_none : HSize Hd.none where
  fill := Nat.zero_le _
  lens := Nat.zero_le _
  clLens := Nat.zero_le _
  clt := by
    show (zeroBytes 1024).size ≤ 132096
    rw [zeroBytes_size (by decide)]
    decide
  mapT := by
    show (zeroBytes 1024).size ≤ 132096
    rw [zeroBytes_size (by decide)]
    decide
  modes := Nat.zero_le _
  lMap := Nat.zero_le _
  dMap := Nat.zero_le _
  litBase := Nat.zero_le _
  icBase := Nat.zero_le _
  dBase := Nat.zero_le _

/-! ### WBITS -/

/-- What WBITS's step does to what a state holds. -/
structure WbitsFacts (a : ByteArray) (stop : USize) (D : Dec) (pos : USize) (r : Dec) : Prop where
  hd : r.hd = D.hd
  H : r.H = D.H
  paused : r.status ≠ .next → r.tag = D.tag ∧ r.limit = D.limit ∧ r.cmd.ring = D.cmd.ring ∧ r.cmd.seen = D.cmd.seen ∧ r.cmd.wordBuf = D.cmd.wordBuf
  next : r.status = .next → r.tag = .mblock ∧ r.limit.toNat + 2 ^ r.k.toNat = D.limit.toNat
  memory : r.status = .memory → ∀ t : List UInt8, ∃ kv rest, readWBITS (D.bits a pos stop (bits t)) = some (kv, rest) ∧ D.limit.toNat < 2 ^ kv

theorem stepDWbits_facts {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D .wbits) (hpos : pos.toNat ≤ stop.toNat) :
    WbitsFacts a stop D pos (stepDWbits a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hlim, hz⟩ := hrel
  have ht' : tag = .wbits := ht
  subst ht'
  unfold stepDWbits
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hpos)]
  dsimp only
  obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := cmd.word) (count := cmd.count) hs hpos hw
  have hbits : ∀ F, availBits cmd.word cmd.count a pos stop F =
      availBits (refill cmd.word cmd.count a pos stop hs hpos).word (refill cmd.word cmd.count a pos stop hs hpos).count a
        (refill cmd.word cmd.count a pos stop hs hpos).pos stop F := by
    intro F
    show (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
      (refill cmd.word cmd.count a pos stop hs hpos).buf.held ++ (chunkBits a (refill cmd.word cmd.count a pos stop hs hpos).pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, r4]
  generalize refill cmd.word cmd.count a pos stop hs hpos = rf at r1 r2 r3 r4 r5 hbits
  have R := wbitsFast_ok (b0 := ⟨rf.word, rf.count⟩) r1
  have hval := R.ok
  generalize wbitsFast ⟨rf.word, rf.count⟩ = r at hval
  cases hsr : r.status with
  | short =>
    dsimp only
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | bad =>
    dsimp only
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | ok =>
    dsimp only
    obtain ⟨h10, h24⟩ := readWBITS_range (by simpa using (hval hsr).2 [])
    have hneed : ((1 : UInt64) <<< r.a).toNat = 2 ^ r.a.toNat := by
      have hpw : 2 ^ r.a.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h24
      have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
      rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega), Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hc : (1 : UInt64) <<< r.a ≤ limit
    · rw [ite_eq_left hc]
      have hle := UInt64.le_iff_toNat_le.mp hc
      rw [hneed] at hle
      have hus : r.a.toUSize.toNat = r.a.toNat := word_toUSize (by omega)
      refine ⟨rfl, rfl, fun e => absurd rfl e, fun _ => ⟨rfl, ?_⟩, fun e => DStatus.noConfusion e⟩
      show (limit - (1 : UInt64) <<< r.a).toNat + 2 ^ r.a.toUSize.toNat = limit.toNat
      rw [UInt64.toNat_sub_of_le _ _ hc, hneed, hus]
      omega
    · rw [ite_eq_right hc]
      refine ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩, fun e => DStatus.noConfusion e, fun _ t => ⟨r.a.toNat, r.buf.held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t), ?_, ?_⟩⟩
      · show readWBITS (availBits cmd.word cmd.count a pos stop (bits t)) = _
        rw [hbits]
        exact (hval hsr).2 _
      · exact Nat.lt_of_not_le fun e => hc (UInt64.le_iff_toNat_le.mpr (by rw [hneed]; exact e))

/-- WBITS's step. -/
theorem wbits_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .wbits) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDWbits a stop hs D D.pos) := by
  have hWin : D.cmd.ring.size = 0 ∧ D.cmd.seen.size = 0 ∧ D.cmd.wordBuf.size = 0 ∧ D.limit.toNat = L ∧ winSem.first (D.bits a D.pos stop (bits t)) = Ws := by
    rcases M.win with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · exact absurd ht h
  obtain ⟨_, _, _, hL, hWs⟩ := hWin
  obtain ⟨p, hrel, hw⟩ := M.place
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
  have hD := stepDWbits_ok (S := demandSem) (a := a) (hs := hs) hrel hp
  have hW := stepDWbits_ok (S := winSem) (a := a) (hs := hs) hrel hp
  generalize stepDWbits a stop hs D D.pos = r at hF hD hW
  refine ⟨fun h0 h1 => ?_, fun e => ?_⟩
  · have hpaused : r.status ≠ .next → r.tag = D.tag := fun e => (hF.paused e).1
    obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) h0 h1 hpaused
    have hHO : D.H.arena.size = 0 := M.HOut (by rw [ht]; decide)
    have hdO : D.hd.d.arena.size = 0 := M.hdOut (by rw [ht]; decide)
    by_cases hn : r.status = .next
    · obtain ⟨g1, g2⟩ := hF.next hn
      obtain ⟨p', hR, _, _, heq, hdown, _⟩ := hW.next hn
      cases p' with
      | mblock w st =>
        have hq : Ws = some w := by rw [← hWs]; exact heq t
        have hk : w + 16 = 2 ^ r.k.toNat := hR.2.2.win.win
        refine ⟨hA, hB, fun e => absurd (g1.symm.trans e) (by decide), fun e => absurd (g1.symm.trans e) (by decide),
          fun _ => by rw [hF.hd]; exact hdO, fun _ => by rw [hF.H]; exact hHO, by rw [hF.hd]; exact M.hd, by rw [hF.H]; exact M.H,
          Or.inr ⟨by rw [g1]; decide, w, hq, hk, by omega⟩⟩
      | wbits => exact hdown.elim
      | skip => exact hdown.elim
      | raw => exact hdown.elim
      | hdr => exact hdown.elim
      | cmds => exact hdown.elim
      | ended => exact hdown.elim
    · obtain ⟨g1, g2, g3, g4, g5⟩ := hF.paused hn
      refine ⟨hA, hB, fun e => absurd (ht.symm.trans (g1.symm.trans e)) (by decide), fun e => absurd (ht.symm.trans (g1.symm.trans e)) (by decide),
        fun _ => by rw [hF.hd]; exact hdO, fun _ => by rw [hF.H]; exact hHO, by rw [hF.hd]; exact M.hd, by rw [hF.H]; exact M.H,
        Or.inl ⟨by rw [g1]; exact ht, by rw [g3]; assumption, by rw [g4]; assumption, by rw [g5]; assumption, by rw [g2]; exact hL, ?_⟩⟩
      cases hst : r.status with
      | next => exact absurd hst hn
      | memory => exact absurd hst h0
      | bad => exact absurd hst h1
      | needsInput =>
        obtain ⟨_, _, p', _, heq, _, hdown, _⟩ := hW.needsInput hst
        cases p' with
        | wbits =>
          rw [← hWs]
          exact (heq t).symm
        | mblock => exact hdown.elim
        | skip => exact hdown.elim
        | raw => exact hdown.elim
        | hdr => exact hdown.elim
        | cmds => exact hdown.elim
        | ended => exact hdown.elim
      | needsOutput =>
        obtain ⟨p', _, _, _, heq, _, hdown, _⟩ := hW.needsOutput hst
        cases p' with
        | wbits =>
          rw [← hWs]
          exact (heq t).symm
        | mblock => exact hdown.elim
        | skip => exact hdown.elim
        | raw => exact hdown.elim
        | hdr => exact hdown.elim
        | cmds => exact hdown.elim
        | ended => exact hdown.elim
  · obtain ⟨kv, rest, g1, g2⟩ := hF.memory e t
    have hrange := readWBITS_range g1
    have hsz := (windowSize_range hrange.1 hrange.2).1
    have hq : Ws = some (windowSize kv) := by
      rw [← hWs]
      show (readWBITS _ >>= fun p => some (windowSize p.1)) = _
      rw [g1]
      rfl
    have hpw : 2 ^ kv ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hrange.2
    have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
    rw [hL] at g2
    have he : (some (windowSize kv) : Option Nat).elim 0 (· + 16) = windowSize kv + 16 := rfl
    refine ⟨?_, by omega⟩
    rw [hq, he]
    omega

/-! ### A meta-block's start -/

/-- What a meta-block's start does to what a state holds. -/
structure MetaFacts (a : ByteArray) (stop : USize) (D : Dec) (pos : USize) (r : Dec) : Prop where
  k : r.k = D.k
  limit : r.limit = D.limit
  H : r.H = D.H
  status : r.status ≠ .memory
  paused : r.status ≠ .next → r.tag = D.tag
  other : r.tag ≠ .hdr → r.hd = D.hd
  tag : r.tag ≠ .wbits ∧ r.tag ≠ .cmds
  start : r.tag = .hdr → r.status = .next ∧ (∀ t : List UInt8, ∃ last mlen, metaStart (D.bits a pos stop (bits t)) = some (.data last mlen false, r.bits a r.pos stop (bits t))) ∧
    HRel r.hd Gh.start (.cat .L) ∧ r.hd.d.arena.size = 0 ∧ r.hd.d.arenaMax = D.limit ∧ HSize r.hd

/-- The header machine's first state holds only small tables. -/
theorem hsize_start (word count limit : UInt64) : HSize (hdStart word count limit) where
  fill := Nat.zero_le _
  lens := Nat.zero_le _
  clLens := Nat.zero_le _
  clt := hsize_none.clt
  mapT := hsize_none.mapT
  modes := Nat.zero_le _
  lMap := Nat.zero_le _
  dMap := Nat.zero_le _
  litBase := Nat.zero_le _
  icBase := Nat.zero_le _
  dBase := Nat.zero_le _

theorem stepDMeta_facts {w : Nat} {st : StreamState} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.mblock w st)) (hpos : pos.toNat ≤ stop.toNat) : MetaFacts a stop D pos (stepDMeta a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hall⟩ := hrel
  have ht' : tag = .mblock := ht
  subst ht'
  have hlim : limit.toNat + 132096 < 2 ^ 32 := hall.limit
  have hdec : (DTag.mblock ≠ DTag.wbits) ∧ (DTag.mblock ≠ DTag.cmds) := by decide
  have hnh : DTag.mblock ≠ DTag.hdr := by decide
  unfold stepDMeta
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hpos)]
  dsimp only
  obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := cmd.word) (count := cmd.count) hs hpos hw
  have hbits : ∀ F, availBits cmd.word cmd.count a pos stop F =
      availBits (refill cmd.word cmd.count a pos stop hs hpos).word (refill cmd.word cmd.count a pos stop hs hpos).count a
        (refill cmd.word cmd.count a pos stop hs hpos).pos stop F := by
    intro F
    show (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
      (refill cmd.word cmd.count a pos stop hs hpos).buf.held ++ (chunkBits a (refill cmd.word cmd.count a pos stop hs hpos).pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, r4]
  generalize refill cmd.word cmd.count a pos stop hs hpos = rf at r1 r2 r3 r4 r5 hbits
  have R := metaStartFast_ok (b0 := ⟨rf.word, rf.count⟩) r1
  have hval := R.ok
  generalize metaStartFast ⟨rf.word, rf.count⟩ = r at hval
  cases hsr : r.status with
  | short =>
    dsimp only
    exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh⟩
  | bad =>
    dsimp only
    exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh⟩
  | ok =>
    dsimp only
    have hw2 := (hval hsr).1
    unfold metaGo
    by_cases h0 : r.a = 0
    · rw [ite_eq_left h0]
      exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩, fun e => DTag.noConfusion e⟩
    rw [ite_eq_right h0]
    by_cases h1 : r.a = 1
    · rw [ite_eq_left h1]
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩, fun e => DTag.noConfusion e⟩
      · rw [ite_eq_right hz]
        exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh⟩
    rw [ite_eq_right h1]
    have hv : msValue r = .data (r.b != 0) r.c.toNat (r.d != 0) := by
      unfold msValue
      rw [ite_eq_right h0, ite_eq_right h1]
    by_cases hu : (r.d != 0) = true
    · rw [ite_eq_left hu]
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩, fun e => DTag.noConfusion e⟩
      · rw [ite_eq_right hz]
        exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh⟩
    · rw [ite_eq_right hu]
      have hu' : (r.d != 0) = false := by simpa using hu
      refine ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, fun e => absurd rfl e, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩, fun _ => ⟨rfl, fun t => ⟨r.b != 0, r.c.toNat, ?_⟩, hdStart_rel hw2 hlim, rfl, rfl, hsize_start _ _ _⟩⟩
      show metaStart (availBits cmd.word cmd.count a pos stop (bits t)) = some (.data (r.b != 0) r.c.toNat false, availBits r.word r.count a rf.pos stop (bits t))
      rw [hbits, ← hu', ← hv]
      exact (hval hsr).2 _

/-- A meta-block's start. -/
theorem mblock_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .mblock) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDMeta a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  have hWinr : ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L := by
    rcases M.win with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd (ht.symm.trans h) (by decide)
    · exact h
  obtain ⟨w0, g1, g2, g3⟩ := hWinr
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock w st =>
    have hF := stepDMeta_facts (a := a) (hs := hs) hrel hp
    have hD := stepDMeta_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    generalize stepDMeta a stop hs D D.pos = r at hF hD
    refine ⟨fun h0 h1 => ?_, fun e => absurd e hF.status⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 hF.paused
    have hHO : D.H.arena.size = 0 := M.HOut (by rw [ht]; decide)
    have hdO : D.hd.d.arena.size = 0 := M.hdOut (by rw [ht]; decide)
    have hRwin : r.tag ≠ .wbits ∧ _ := hF.tag
    by_cases hth : r.tag = .hdr
    · obtain ⟨_, s2, s3, s4, s5, s6⟩ := hF.start hth
      obtain ⟨last, mlen, hm⟩ := s2 t
      have hTables : headerTables (D.bits a D.pos stop (bits t)) = (hrest tableK Gh.start (.cat .L) (r.bits a r.pos stop (bits t))).getD 0 := by
        unfold headerTables
        rw [hm]
      have hb0 := M.block ht
      rw [hTables] at hb0
      refine ⟨hA, hB, fun _ => ⟨Gh.start, .cat .L, s3, by rw [s4]; omega, by rw [s5, hF.limit], ?_⟩, fun e => absurd (hth.symm.trans e) (by decide), fun e => absurd hth e,
        fun _ => by rw [hF.H]; exact hHO, s6, by rw [hF.H]; exact M.H, Or.inr ⟨hRwin.1, w0, g1, by rw [hF.k]; exact g2, by rw [hF.k, hF.limit]; exact g3⟩⟩
      rw [s4]
      show 0 + 132096 * (770 + 2 * 2) ≤ 132096 * 774
      decide
    · refine M.keep (by rw [ht]; decide) (by rw [ht]; decide) hF.k hF.limit (hF.other hth) hRwin.1 hth (by rw [hF.H]; exact M.H) (fun e => absurd e hF.tag.2) (fun _ => by rw [hF.H]; exact hHO) hA hB

/-! ### Metadata, uncompressed bytes and commands -/

/-- Metadata's step. -/
theorem skip_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .skip) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDSkip stop D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := stepDSkip_keeps stop D D.pos ht
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip w st last n =>
    have hD := stepDSkip_ok (S := demandSem) hs hrel hp
    generalize stepDSkip stop D D.pos = r at hD k1 k2 k3 k4 k5 k6 k7 k8 k9
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k5⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 k6
    exact M.keep (by rw [ht]; decide) (by rw [ht]; decide) k1 k2 k3 k7 k8 (by rw [k4]; exact M.H) (fun e => absurd e k9)
      (fun _ => by rw [k4]; exact M.HOut (by rw [ht]; decide)) hA hB

/-- Uncompressed bytes' step. -/
theorem raw_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .raw) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDRaw a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := stepDRaw_keeps a stop hs D D.pos ht
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw w st last n =>
    have hD := stepDRaw_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    generalize stepDRaw a stop hs D D.pos = r at hD k1 k2 k3 k4 k5 k6 k7 k8 k9
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k5⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 k6
    exact M.keep (by rw [ht]; decide) (by rw [ht]; decide) k1 k2 k3 k7 k8 (by rw [k4]; exact M.H) (fun e => absurd e k9)
      (fun _ => by rw [k4]; exact M.HOut (by rw [ht]; decide)) hA hB

/-- The commands' step. -/
theorem cmds_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .cmds) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDCmds a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := stepDCmds_keeps a stop hs D D.pos
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds w last m q =>
    have hD := stepDCmds_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    generalize stepDCmds a stop hs D D.pos = r at hD k1 k2 k3 k4 k5 k6
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k4⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) h0 h1 k5
    rcases k6 with ⟨t1, t2⟩ | ⟨t1, t2, t3, t4⟩
    · have hc := M.cmds ht
      rw [← t1] at ht
      exact M.keep (by rw [t1] at ht; rw [ht]; decide) (by rw [t1] at ht; rw [ht]; decide) k1 k2 k3 (by rw [ht]; decide) (by rw [ht]; decide) (by rw [t2]; exact M.H)
        (fun _ => by rw [t2, k2]; exact hc) (fun e => absurd ht e) hA hB
    · exact M.keep (by rw [ht]; decide) (by rw [ht]; decide) k1 k2 k3 t1 t2 (by rw [t4]; exact hsmall_none) (fun e => absurd e t3) (fun _ => by rw [t4]; rfl) hA hB

/-! ### A header -/

/-- The bits of a state in a header. -/
theorem Dec.bits_hdr {D : Dec} (h : D.tag = .hdr) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    D.bits a pos stop F = availBits D.hd.word D.hd.count a pos stop F := by
  unfold Dec.bits Dec.word Dec.count
  rw [h]

/-- What a move does to the room left for tables. -/
private theorem cap_step {q q' : HPhase} {oc : Option PrefixCode} (hc : capH q' + (if oc.isSome then 1 else 0) ≤ capH q) (hone : tableOf oc ≤ 132096) :
    tableOf oc + 132096 * capH q' ≤ 132096 * capH q := by
  cases oc with
  | none =>
    have h : capH q' ≤ capH q := by simpa using hc
    exact Nat.zero_add _ ▸ Nat.mul_le_mul_left _ h
  | some c =>
    have h : capH q' + 1 ≤ capH q := by simpa using hc
    have := Nat.mul_le_mul_left 132096 h
    rw [Nat.mul_add] at this
    omega

/-- A header's step. -/
theorem hdr_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .hdr) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDHdr a stop hs D D.pos) := by
  obtain ⟨g, q, hR, h1, h2, h3⟩ := M.hdr ht
  rw [Dec.bits_hdr ht] at h1
  have hWinr : ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L := by
    rcases M.win with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd (ht.symm.trans h) (by decide)
    · exact h
  obtain ⟨w0, g1, g2, g3⟩ := hWinr
  obtain ⟨p, hrel, hw⟩ := M.place
  have hHO : D.H.arena.size = 0 := M.HOut (by rw [ht]; decide)
  obtain ⟨_, hk24, _, _⟩ := hrel.arrays (by rw [ht]; decide)
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr w st last mlen g0 q0 =>
    have hD := stepDHdr_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    have hH := stepH_ok (K := tableK) (a := a) (hs := hs) hR hp
    unfold stepDHdr at hD ⊢
    dsimp only at hD ⊢
    generalize stepH a stop hs D.hd D.pos = r at hH hD ⊢
    have hbitsAt : ∀ D' : Dec, D'.tag = .hdr → D'.hd = r → D'.pos = r.pos → D'.bits a D'.pos stop (bits t) = availBits r.word r.count a r.pos stop (bits t) := by
      intro D' e1 e2 e3
      rw [Dec.bits_hdr e1, e2, e3]
    cases hst : r.status with
    | next =>
      rw [hst] at hD
      dsimp only at hD
      obtain ⟨g', q', oc, hR', a1, a2, a3, _, hm⟩ := hH.next hst
      have hT := a3 (bits t)
      have hN := congrArg (Option.getD · 0) hT
      simp only [wr_tableK] at hN
      have hcap := cap_step hm.cap hm.one
      have hgrow := hm.grow
      have htag : ({ clearHd D with hd := r, pos := r.pos, status := .next } : Dec).tag = .hdr := ht
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun e => absurd rfl e)
      refine ⟨hA, hB, fun _ => ⟨g', q', hR', ?_, ?_, ?_⟩, fun e => absurd (htag.symm.trans e) (by decide), fun e => absurd htag e, fun _ => hHO, hm.size M.hd, M.H,
        Or.inr ⟨by rw [htag]; decide, w0, g1, g2, g3⟩⟩
      · rw [hbitsAt _ htag rfl rfl]
        show r.d.arena.size + _ ≤ X
        omega
      · show r.d.arenaMax = D.limit
        rw [hm.max, h2]
      · show r.d.arena.size + 132096 * capH q' ≤ _
        have hc2 : 132096 * capH q ≤ 132096 * 774 - D.hd.d.arena.size := by omega
        omega
    | needsInput =>
      rw [hst] at hD
      dsimp only at hD
      obtain ⟨a1, a2, hR', a3, _, hm⟩ := hH.needsInput hst
      have hT := a3 (bits t)
      have hgrow := hm.grow
      have htag : ({ clearHd D with hd := r, pos := r.pos, status := .needsInput } : Dec).tag = .hdr := ht
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun _ => rfl)
      have hg0 : tableOf (none : Option PrefixCode) = 0 := rfl
      rw [hg0] at hgrow
      refine ⟨hA, hB, fun _ => ⟨g, q, hR', ?_, ?_, ?_⟩, fun e => absurd (htag.symm.trans e) (by decide), fun e => absurd htag e, fun _ => hHO, hm.size M.hd, M.H,
        Or.inr ⟨by rw [htag]; decide, w0, g1, g2, g3⟩⟩
      · rw [hbitsAt _ htag rfl rfl, ← hT]
        show r.d.arena.size + _ ≤ X
        omega
      · show r.d.arenaMax = D.limit
        rw [hm.max, h2]
      · show r.d.arena.size + 132096 * capH q ≤ _
        omega
    | bad => exact ⟨fun _ e => absurd rfl e, fun e => DStatus.noConfusion e⟩
    | memory =>
      refine ⟨fun e => absurd rfl e, fun _ => ?_⟩
      obtain ⟨c, m1, m2, m3, m4⟩ := hH.memory hst
      obtain ⟨x, hx⟩ := m4 (bits t)
      rw [hx] at h1
      have h1' : D.hd.d.arena.size + (tableBytes c + x.getD 0) ≤ X := h1
      rw [h2] at m1
      have hpos : 132096 ≤ 132096 * capH q := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero m3)
      have hpw : 2 ^ D.k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk24
      have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
      have he : (some w0 : Option Nat).elim 0 (· + 16) = w0 + 16 := rfl
      refine ⟨?_, by omega⟩
      rw [g1, he]
      omega
    | ready =>
      rw [hst] at hD
      dsimp only at hD
      obtain ⟨g', hu, _, _, _, a3, hmax, harena, hsz⟩ := hH.ready hst
      obtain ⟨H', hmk, _, e1, e2, e3, e4, e5, e6, e7⟩ := mkHdr_ok hu
      rw [hmk] at hD ⊢
      dsimp only at hD ⊢
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun e => absurd rfl e)
      have hS := hsz M.hd
      have hle := hu.le
      refine ⟨hA, hB, fun e => DTag.noConfusion e, fun _ => ⟨?_, ?_⟩, fun _ => rfl, fun e => absurd rfl e, hsize_none,
        ⟨by rw [e2]; exact hS.litBase, by rw [e3]; exact hS.lMap, by rw [e4]; exact hS.icBase, by rw [e5]; exact hS.dBase, by rw [e6]; exact hS.dMap, by rw [e7]; exact hS.modes⟩,
        Or.inr ⟨fun e => DTag.noConfusion e, w0, g1, g2, g3⟩⟩
      · show H'.arena.size ≤ X
        rw [e1, harena]
        omega
      · show H'.arena.size ≤ D.limit.toNat
        rw [e1, ← h2, ← hmax]
        exact hle

/-! ### The loop and a call -/

/-- A step of the stream. -/
theorem stepD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepD a stop hs D) := by
  unfold stepD
  cases ht : D.tag with
  | wbits => exact wbits_mem M ht hp
  | mblock => exact mblock_mem M ht hp
  | skip => exact skip_mem hs M ht hp
  | raw => exact raw_mem M ht hp
  | hdr => exact hdr_mem M ht hp
  | cmds => exact cmds_mem M ht hp
  | ended => exact absurd ht he

/-- The loop. -/
theorem runD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} : ∀ x : RunArg a stop hs,
    MemD Ws X L x.D (x.D.bits a x.D.pos stop (bits t)) → StepM Ws X L a stop t (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    intro M
    obtain ⟨D, hinv⟩ := x
    dsimp only at M ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨p, hrel, hw⟩ := M.place
      exact M.move rfl ⟨p, hrel.congr rfl rfl rfl rfl rfl rfl rfl rfl, hw⟩ rfl rfl rfl rfl rfl rfl rfl rfl
    · rw [dite_eq_right he]
      dsimp only
      have hstep := stepD_mem (hs := hs) M he hinv.2
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        have hM := hstep.go (by rw [hn]; decide) (by rw [hn]; decide)
        exact ih ⟨stepD a stop hs D, hinv.step he hn⟩ ⟨he, hn, rfl⟩ hM
      · rw [dite_eq_right hn]
        exact hstep

/-- What a call leaves, for what a state holds. -/
structure CallMem (Ws : Option Nat) (X L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (o : Out) : Prop where
  running : o.status.stopped = false → MemD Ws X L o.D (o.D.bits a o.pos stop (bits t))
  stopped : o.status.stopped = true → o.D = deadD
  why : o.status = .memoryLimit → MemWhy Ws X L

/-- Handing out a state's bytes leaves what it holds. -/
theorem MemD.flush {Ws : Option Nat} {X L : Nat} {D : Dec} {B : List Bool} (M : MemD Ws X L D B) (buf : ByteArray) (space : Nat) : MemD Ws X L (flushD D buf space).D B := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨_, _, _, _, a4, _, _, _, _, _, _, _⟩ := flushD_spec hrel buf space
  have hrings : (flushD D buf space).D.cmd.ring = D.cmd.ring ∧ (flushD D buf space).D.cmd.seen = D.cmd.seen ∧ (flushD D buf space).D.cmd.wordBuf = D.cmd.wordBuf := by
    rcases hrel.window with h0 | ⟨hring, hle, hout, hk⟩
    · have hf : flushAll D.k D.cmd buf space = ⟨D.cmd, buf, space⟩ := by
        rw [flushAll]
        dsimp only
        rw [ite_eq_left (Or.inl h0)]
      unfold flushD
      dsimp only
      rw [hf]
      exact ⟨rfl, rfl, rfl⟩
    · obtain ⟨_, _, _, _, a5, _, _, _⟩ := flushAll_spec hk _ D.cmd buf space rfl hring hle hout
      unfold flushD
      dsimp only
      rw [a5]
      exact ⟨rfl, rfl, rfl⟩
  exact M.move rfl ⟨p, a4, hw⟩ rfl hrings.1 hrings.2.1 hrings.2.2 rfl rfl rfl rfl

/-- Handing out a state's bytes leaves what it holds, with its bits as they were. -/
theorem MemD.flushed {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {D : Dec} {F : List Bool} (M : MemD Ws X L D (D.bits a D.pos stop F)) (buf : ByteArray) (space : Nat) :
    MemD Ws X L (flushD D buf space).D ((flushD D buf space).D.bits a (flushD D buf space).D.pos stop F) := by
  obtain ⟨p, hrel, _⟩ := M.place
  obtain ⟨_, _, _, _, _, _, _, _, a8, _, a9, _⟩ := flushD_spec hrel buf space
  rw [a8, a9]
  exact M.flush buf space

/-- A call that stopped. -/
private theorem callMem_dead {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {buf : ByteArray} {pos : USize} {s : Status} (hs : s.stopped = true)
    (hm : s = .memoryLimit → MemWhy Ws X L) : CallMem Ws X L a stop t ⟨deadD, buf, pos, s⟩ :=
  ⟨fun h => Bool.noConfusion (hs.symm.trans h), fun _ => rfl, hm⟩

/-- A call that paused with a state. -/
private theorem callMem_run {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D : Dec} {buf : ByteArray} {pos : USize} {s : Status} (hs : s.stopped = false)
    (hn : s ≠ .memoryLimit) (M : MemD Ws X L D (D.bits a pos stop (bits t))) : CallMem Ws X L a stop t ⟨D, buf, pos, s⟩ :=
  ⟨fun _ => M, fun h => Bool.noConfusion (hs.symm.trans h), fun e => absurd e hn⟩

/-- The stream's end. -/
theorem endCheck_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {D : Dec} {B : List Bool} {t : List UInt8} {st : StreamState} {final : Bool} (buf : ByteArray)
    (M : MemD Ws X L D B) (hrel : DRel D (.ended st)) : CallMem Ws X L a stop t (endCheck D stop final buf) := by
  have ht : D.tag = .ended := hrel.1
  obtain ⟨a1, hw, w, a3⟩ := hrel
  unfold endCheck
  dsimp only
  by_cases hz : (BitBuffer.mk D.cmd.word D.cmd.count).peek (D.cmd.count &&& 7) = 0
  · rw [ite_eq_left hz]
    by_cases hc : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count = 0 ∧ D.pos = stop
    · rw [ite_eq_left hc]
      cases final with
      | true => exact callMem_dead rfl (fun e => Status.noConfusion e)
      | false =>
        obtain ⟨_, fa2⟩ := fill_aligned hw
        refine callMem_run rfl (fun e => Status.noConfusion e) ?_
        have hne : ∀ d : DTag, d ≠ .ended → D.tag ≠ d := fun d h e => h (e.symm.trans ht)
        refine M.keep (hne _ (by decide)) (hne _ (by decide)) rfl rfl rfl (hne _ (by decide)) (hne _ (by decide)) M.H (fun e => absurd e (hne _ (by decide)))
          M.HOut ⟨.ended st, ⟨a1, fa2, w, ⟨{ a3.win with }, a3.produced, a3.limit⟩⟩, Nat.zero_le _⟩ (fun e => absurd e (hne _ (by decide)))
    · rw [ite_eq_right hc]
      exact callMem_dead rfl (fun e => Status.noConfusion e)
  · rw [ite_eq_right hz]
    exact callMem_dead rfl (fun e => Status.noConfusion e)

/-- What a call does with what the loop left. -/
theorem afterRun_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {r : Dec} {final : Bool} (hr : StepM Ws X L a stop t r)
    (hend : r.status = .next → ∃ st, DRel r (.ended st)) (pos0 : USize) (buf : ByteArray) (space : Nat) : CallMem Ws X L a stop t (afterRun r stop final pos0 buf space) := by
  unfold afterRun
  cases hst : r.status with
  | bad => exact callMem_dead rfl (fun e => Status.noConfusion e)
  | memory => exact callMem_dead rfl (fun _ => hr.why hst)
  | needsOutput => exact callMem_run rfl (fun e => Status.noConfusion e) (hr.go (by rw [hst]; decide) (by rw [hst]; decide))
  | needsInput =>
    have hM := (hr.go (by rw [hst]; decide) (by rw [hst]; decide)).flushed buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      cases final with
      | true => exact callMem_dead rfl (fun e => Status.noConfusion e)
      | false => exact callMem_run rfl (fun e => Status.noConfusion e) hM
    · rw [ite_eq_right hz]
      exact callMem_run rfl (fun e => Status.noConfusion e) hM
  | next =>
    have hM := (hr.go (by rw [hst]; decide) (by rw [hst]; decide)).flushed buf space
    obtain ⟨st, hrel⟩ := hend hst
    obtain ⟨_, _, _, _, a4, _, _, _, _, _, _, _⟩ := flushD_spec hrel buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      exact endCheck_mem _ hM a4
    · rw [ite_eq_right hz]
      exact callMem_run rfl (fun e => Status.noConfusion e) hM

/-- A call, for what a state holds. -/
theorem callD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} {t : List UInt8} : ∀ (space : Nat) (D : Dec) (h : DInv stop D) (buf : ByteArray),
    MemD Ws X L D (D.bits a D.pos stop (bits t)) → CallMem Ws X L a stop t (callD a stop hs final D h buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h buf M
    rw [callD]
    dsimp only
    have hr := runD_mem (hs := hs) (t := t) ⟨D, h⟩ M
    dsimp only at hr
    by_cases hO : (runD a stop hs D h).status = .needsOutput
    · rw [dite_eq_left hO]
      have hM := (hr.go (by rw [hO]; decide) (by rw [hO]; decide)).flushed buf space
      obtain ⟨p, hrel⟩ := h.1
      obtain ⟨p', hR, _, _, _, _, hfull⟩ := (runD_ok (hs := hs) ⟨D, h⟩ p hrel).needsOutput hO
      obtain ⟨len, a1, _, a3, _, a5, _, _, _, _, _, _⟩ := flushD_spec hR buf space
      by_cases hz : (flushD (runD a stop hs D h) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz]
        by_cases hlt : (flushD (runD a stop hs D h) buf space).space < space
        · rw [dite_eq_left hlt]
          exact ih _ hlt _ _ _ hM
        · rw [dite_eq_right hlt]
          exact callMem_dead rfl (fun e => Status.noConfusion e)
      · rw [ite_eq_right hz]
        exact callMem_run rfl (fun e => Status.noConfusion e) hM
    · rw [dite_eq_right hO]
      obtain ⟨p, hrel⟩ := h.1
      refine afterRun_mem hr (fun e => ?_) _ _ _
      obtain ⟨st, b1, _⟩ := (runD_ok (hs := hs) ⟨D, h⟩ p hrel).next e
      exact ⟨st, b1⟩

end Brotli.Decoder
