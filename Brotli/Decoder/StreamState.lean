module

public import Brotli.Decoder.StreamRaw
public import Brotli.Decoder.Progress
public import Brotli.Decoder.FastEq

@[expose] public section

/-!
# The stream's state

`Dec` is the whole decoder's state between steps, and `DRel` ties it to a place in `srest`, which is what the spec still has
to do down to the stream's output.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- What a stream's places are worth: what follows a meta-block, and what a place gives that isn't inside one. The spec's
own worth is its output. Another is what the termination measure counts. -/
structure Sem (α : Type) where
  /-- What follows a meta-block, by whether it is the last. -/
  after : Nat → Bool → StreamState → List Bool → Option α
  /-- The place at a meta-block's start. -/
  block : Nat → StreamState → List Bool → Option α
  /-- The place at the stream's end. -/
  finish : StreamState → List Bool → Option α
  /-- The place at the stream's first bits. -/
  first : List Bool → Option α
  after_true : ∀ w st bs, after w true st bs = finish st bs
  after_false : ∀ w st bs, after w false st bs = block w st bs
  first_eq : ∀ bs, first bs = readWBITS bs >>= fun p => block (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2

/-- The spec's own worth: a place's output. -/
def specSem : Sem (List UInt8) where
  after := amK
  block := metaK
  finish := endOf
  first bs := readWBITS bs >>= fun p => metaK (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- What a place is worth on arriving at it. -/
def srest {α : Type} (S : Sem α) : SPhase → List Bool → Option α
  | .wbits, bs => S.first bs
  | .mblock w st, bs => S.block w st bs
  | .skip w st last n, bs => skipK (S.after w last) st n bs
  | .raw w st last n, bs => rawK (S.after w last) st n bs
  | .hdr w st last mlen g p, bs => hrest (hdrK w (S.after w last) st mlen) g p bs
  | .cmds w last m p, bs => rest w m (cmdK w (S.after w last) m) p bs
  | .ended st, bs => S.finish st bs

/-- A compressed meta-block is worth the same under the window it is read with: they differ only for a last meta-block,
which any worth follows by the stream's end, whatever the window. -/
theorem srest_blockWindow {α : Type} (S : Sem α) (w : Nat) (st : StreamState) (last : Bool) (mlen : Nat) (g : Gh) (p : HPhase)
    (bs : List Bool) : srest S (.hdr w st last mlen g p) bs = srest S (.hdr (blockWindow w st last mlen) st last mlen g p) bs := by
  show hrest (hdrK w (S.after w last) st mlen) g p bs =
    hrest (hdrK (blockWindow w st last mlen) (S.after (blockWindow w st last mlen) last) st mlen) g p bs
  by_cases hc : last = true ∧ st.produced = 0
  · obtain ⟨rfl, _⟩ := hc
    have e : ∀ x, S.after x true = S.finish := fun x => funext fun st => funext fun bs => S.after_true x st bs
    simp only [e]
    rw [← hdrK_blockWindow]
  · unfold blockWindow
    rw [ite_eq_right hc]

/-- What a place does on leaving it: a meta-block's start reads that meta-block. It differs from the worth on arriving only
for a worth that isn't the output. -/
def sLeave {α : Type} (S : Sem α) : SPhase → List Bool → Option α
  | .mblock w st, bs => metaStart bs >>= fun p => afterStart w (S.after w) st p.1 p.2
  | p, bs => srest S p bs

/-- For the spec's own worth, the two are the same. -/
theorem sLeave_spec (p : SPhase) (bs : List Bool) : sLeave specSem p bs = srest specSem p bs := by
  cases p with
  | mblock w st => exact (metaK_start w st bs).symm
  | wbits => rfl
  | skip => rfl
  | raw => rfl
  | hdr => rfl
  | cmds => rfl
  | ended => rfl

/-- `decode` is the first place. -/
theorem decode_srest (input : List UInt8) : decode input = srest specSem .wbits (bits input) := by
  rw [decode_metaK]
  rfl

/-- Which place a stream's state is at. -/
inductive DTag where
  | wbits
  | mblock
  | skip
  | raw
  | hdr
  | cmds
  | ended
  deriving DecidableEq

fast_deceq DTag [wbits, mblock, skip, raw, hdr, cmds, ended]

/-- How a stream step ended. -/
inductive DStatus where
  | next
  | needsInput
  | needsOutput
  | memory
  | bad
  deriving DecidableEq

fast_deceq DStatus [next, needsInput, needsOutput, memory, bad]

/-- A dummy header, between meta-blocks. -/
def Hdr.none : Hdr where
  arena := ByteArray.empty
  arenaCap := 0
  litBase := ByteArray.empty
  lMap := ByteArray.empty
  icBase := ByteArray.empty
  dBase := ByteArray.empty
  dMap := ByteArray.empty
  modes := ByteArray.empty
  nL := 0
  nI := 0
  nD := 0
  treesL := 0
  treesD := 0
  baseTL := 0
  baseCL := 0
  baseTI := 0
  baseCI := 0
  baseTD := 0
  baseCD := 0
  npostfix := 0
  ndirect := 0
  npLe := by decide
  ndLe := by decide
  lit := ⟨by decide, by decide, by decide, rfl, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ h => (Nat.not_lt_zero _ h).elim⟩
  lMapSize := rfl
  modesSize := rfl
  modesLt := fun _ h => (Nat.not_lt_zero _ h).elim
  icSize := rfl
  ic32 := by decide
  icFits := fun _ h => (Nat.not_lt_zero _ h).elim
  dSize := rfl
  d32 := by decide
  dMapSize := rfl
  dMap32 := by decide
  dMapLt := fun _ h => (Nat.not_lt_zero _ h).elim
  dFits := fun _ h => (Nat.not_lt_zero _ h).elim
  swL := fun h => absurd h (by decide)
  swI := fun h => absurd h (by decide)
  swD := fun h => absurd h (by decide)
  lTriv := ByteArray.empty
  trivSize := rfl
  trivOk := fun _ h => (Nat.not_lt_zero _ h).elim
  tabF0 := 0

/-- The whole decoder's state between steps. -/
structure Dec where
  tag : DTag
  /-- The window, and the bit buffer outside a header. -/
  cmd : Cmd
  /-- The header being read. -/
  hd : Hd
  /-- The header of the commands being read. -/
  H : Hdr
  k : USize
  last : Bool
  left : UInt64
  limit : UInt64
  pos : USize
  status : DStatus

/-- The buffer a state reads from. -/
@[inline] def Dec.word (D : Dec) : UInt64 :=
  match D.tag with
  | .hdr => D.hd.word
  | _ => D.cmd.word

/-- The buffer a state reads from. -/
@[inline] def Dec.count (D : Dec) : UInt64 :=
  match D.tag with
  | .hdr => D.hd.count
  | _ => D.cmd.count

/-- The window, as every place after WBITS has it. -/
structure WinRel (w k : Nat) (st : Cmd) (out : List Nat) (ds : Distances) : Prop where
  win : w + 16 = 2 ^ k
  k24 : k ≤ 24
  k10 : 10 ≤ k
  ring : RingOk st.ring k st.wpos.toNat out
  bytes : ∀ b ∈ out, b < 256
  ctx : contextBytes out = (st.p1.toNat, st.p2.toNat)
  pendLe : st.pend.toNat + 16 ≤ 2 ^ k
  pendOut : st.pend.toNat ≤ out.length
  written : st.written.toNat = min w out.length
  d0 : ds.last = st.d0.toNat
  d1 : ds.secondToLast = st.d1.toNat
  d2 : ds.thirdToLast = st.d2.toNat
  d3 : ds.fourthToLast = st.d3.toNat
  dsLt : ds.last < 2 ^ 32 ∧ ds.secondToLast < 2 ^ 32 ∧ ds.thirdToLast < 2 ^ 32 ∧ ds.fourthToLast < 2 ^ 32
  wordLe : st.wordBuf.size ≤ 38

/-- The window part of the command loop's state. -/
theorem Core.toWin {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {out : List Nat} {rem : Nat} {ds : Distances} {ic lit dist : BlockState}
    (h : Core w k m st out rem ds ic lit dist) : WinRel w k st out ds :=
  ⟨h.win, h.k24, h.k10, h.ring, h.bytes, h.ctx, h.pendLe, h.pendOut, h.written, h.d0, h.d1, h.d2, h.d3, h.dsLt, h.wordLe⟩

/-- What every place with a window has. -/
structure WinAll (D : Dec) (w : Nat) (st : StreamState) : Prop where
  win : WinRel w D.k.toNat D.cmd st.output st.distances
  produced : st.produced = st.output.length
  limit : D.limit.toNat + 13304 < 2 ^ 32

/-- No window yet: from WBITS to the stream's first meta-block with data, the ring is empty, nothing is produced or
waiting, and `k` is the log size of the window the stream declares. -/
structure NoRing (D : Dec) (w : Nat) (st : StreamState) : Prop where
  win : w + 16 = 2 ^ D.k.toNat
  k10 : 10 ≤ D.k.toNat
  k24 : D.k.toNat ≤ 24
  ring : D.cmd.ring.size = 0
  pend : D.cmd.pend = 0
  st : st = ⟨[], 0, initialDistances⟩
  limit : D.limit.toNat + 13304 < 2 ^ 32

/-- What a place outside a meta-block's data has: a window, once a meta-block with data has produced bytes, or none
before the first. -/
def WinAt (D : Dec) (w : Nat) (st : StreamState) : Prop := (WinAll D w st ∧ st.produced ≠ 0) ∨ NoRing D w st

/-- A window's place, for a state with the same window and limit. -/
theorem WinAt.congr {D D' : Dec} {w : Nat} {st : StreamState} (h : WinAt D w st) (ek : D'.k = D.k) (ec : D'.cmd = D.cmd)
    (el : D'.limit = D.limit) : WinAt D' w st := by
  rcases h with ⟨⟨h1, h2, h3⟩, h4⟩ | hn
  · exact Or.inl ⟨⟨by rw [ek, ec]; exact h1, h2, by rw [el]; exact h3⟩, h4⟩
  · exact Or.inr ⟨by rw [ek]; exact hn.win, by rw [ek]; exact hn.k10, by rw [ek]; exact hn.k24, by rw [ec]; exact hn.ring,
      by rw [ec]; exact hn.pend, hn.st, by rw [el]; exact hn.limit⟩

/-- A window's place, for a state with the same window and limit and another bit buffer. -/
theorem WinAt.words {D D' : Dec} {w : Nat} {st : StreamState} (h : WinAt D w st) {word count : UInt64} (ek : D'.k = D.k)
    (ec : D'.cmd = { D.cmd with word := word, count := count }) (el : D'.limit = D.limit) : WinAt D' w st := by
  rcases h with ⟨⟨h1, h2, h3⟩, h4⟩ | hn
  · refine Or.inl ⟨⟨?_, h2, by rw [el]; exact h3⟩, h4⟩
    rw [ek, ec]
    exact { h1 with }
  · exact Or.inr ⟨by rw [ek]; exact hn.win, by rw [ek]; exact hn.k10, by rw [ek]; exact hn.k24, by rw [ec]; exact hn.ring,
      by rw [ec]; exact hn.pend, hn.st, by rw [el]; exact hn.limit⟩

theorem WinAt.limit {D : Dec} {w : Nat} {st : StreamState} (h : WinAt D w st) : D.limit.toNat + 13304 < 2 ^ 32 := by
  rcases h with ⟨h1, _⟩ | h1
  · exact h1.limit
  · exact h1.limit

/-- A state stands for a place in a stream. -/
def DRel (D : Dec) : SPhase → Prop
  | .wbits => D.tag = .wbits ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ D.limit.toNat + 13304 < 2 ^ 32 ∧ D.cmd.pend = 0 ∧
    D.cmd.ring.size = 0
  | .mblock w st => D.tag = .mblock ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAt D w st
  | .skip w st last n => D.tag = .skip ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAt D w st ∧ D.last = last ∧ D.left.toNat = n ∧
    D.cmd.count.toNat % 8 = 0 ∧ n < 2 ^ 32
  | .raw w st last n => D.tag = .raw ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAll D w st ∧ D.last = last ∧ D.left.toNat = n ∧
    n < 2 ^ 32 ∧ 1 ≤ st.produced + n
  | .hdr w st last mlen g p => D.tag = .hdr ∧ WinAll D w st ∧ D.last = last ∧ D.left.toNat = mlen ∧ 1 ≤ mlen ∧ mlen ≤ 16777216 ∧ HRel D.hd g p ∧
    D.cmd.pend = 0 ∧ D.hd.d.arena.size + budH g p ≤ D.hd.d.arenaCap.toNat
  | .cmds w last m p => D.tag = .cmds ∧ D.last = last ∧ D.limit.toNat + 13304 < 2 ^ 32 ∧ HdrRel D.H m ∧ Rel w D.k.toNat m D.cmd p ∧
    CLive p
  | .ended st => D.tag = .ended ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ ∃ w, WinAt D w st

/-- The stream's bits at a state and position, with what follows. -/
def Dec.bits (D : Dec) (a : ByteArray) (pos stop : USize) (F : List Bool) : List Bool := availBits D.word D.count a pos stop F

/-- The bits a state holds. -/
def Dec.held (D : Dec) : List Bool := (BitBuffer.mk D.word D.count).held

/-- A state as a step leaves it. -/
@[inline] def markD (D : Dec) (pos : USize) (s : DStatus) : Dec := { D with pos := pos, status := s }

/-- Where a step can go from a place. The command loop's places have their own measure. -/
def SDown : SPhase → SPhase → Prop
  | .wbits, .mblock .. => True
  | .wbits, _ => False
  | .mblock .., .ended .. => True
  | .mblock .., .skip .. => True
  | .mblock .., .raw .. => True
  | .mblock .., .hdr .. => True
  | .mblock .., _ => False
  | .hdr _ _ _ _ _ p, .hdr _ _ _ _ _ p' => HDown p p'
  | .hdr .., .cmds _ _ _ p => ∃ s, p = .command s
  | .hdr .., _ => False
  | .skip _ _ _ n, .skip _ _ _ n' => n' < n
  | .skip .., .mblock .. => True
  | .skip .., .ended .. => True
  | .skip .., _ => False
  | .raw _ _ _ n, .raw _ _ _ n' => n' < n
  | .raw .., .mblock .. => True
  | .raw .., .ended .. => True
  | .raw .., _ => False
  | _, _ => True

/-- Where a step can pause from a place, given whether more bytes wait. -/
def SDownEq : SPhase → SPhase → Prop → Prop
  | .wbits, .wbits, same => same
  | .wbits, _, _ => False
  | .mblock .., .mblock .., same => same
  | .mblock .., _, _ => False
  | .hdr _ _ _ _ _ p, .hdr _ _ _ _ _ p', same => p' = p ∧ same
  | .hdr .., _, _ => False
  | .skip _ _ _ n, .skip _ _ _ n', same => n' < n ∨ (n' = n ∧ same)
  | .skip .., _, _ => False
  | .raw _ _ _ n, .raw _ _ _ n', same => n' < n ∨ (n' = n ∧ same)
  | .raw .., _, _ => False
  | _, _, _ => True

/-- A move's bytes: they go on the front of the output, and they're waiting to go out. -/
def OutD (p p' : SPhase) (D r : Dec) : Prop := ∃ l, p'.out = l ++ p.out ∧ r.cmd.pend.toNat = D.cmd.pend.toNat + l.length

/-- Where a step that stopped decided to: at a place `p1` the reading in order reaches from `p`, at position `pos1` with the
bits `h1` held there, on the bits up to `q` whatever follows them. The decision lies within 64 bits of the first bit held
there. -/
abbrev DecidedAt (a : ByteArray) (stop : USize) (p : SPhase) (B : List UInt8 → List Bool) (pos q : USize)
    (P : SPhase → List Bool → Prop) : Prop :=
  ∃ (p1 : SPhase) (h1 : List Bool) (pos1 : USize), pos.toNat ≤ pos1.toNat ∧ pos1.toNat ≤ q.toNat ∧ q.toNat ≤ stop.toNat ∧
    8 * q.toNat + h1.length ≤ 8 * pos1.toNat + 64 ∧
    (∀ t : List UInt8, Reach sStep p (B t) p1 (h1 ++ (chunkBits a pos1.toNat stop.toNat ++ bits t))) ∧
    ∀ t : List UInt8, P p1 (h1 ++ (chunkBits a pos1.toNat q.toNat ++ bits t))

/-- Deciding after the reading in order moved on is deciding from where it started. -/
theorem DecidedAt.pre {a : ByteArray} {stop : USize} {p p' : SPhase} {B B' : List UInt8 → List Bool} {pos pos' q : USize}
    {P : SPhase → List Bool → Prop} (hj : ∀ t, Reach sStep p (B t) p' (B' t)) (hle : pos.toNat ≤ pos'.toNat)
    (h : DecidedAt a stop p' B' pos' q P) : DecidedAt a stop p B pos q P := by
  obtain ⟨p1, h1, pos1, a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨p1, h1, pos1, Nat.le_trans hle a1, a2, a3, a4, fun t => (hj t).trans (a5 t), a6⟩

/-- A decision another worth gives the same way. -/
theorem DecidedAt.mono {a : ByteArray} {stop : USize} {p : SPhase} {B : List UInt8 → List Bool} {pos q : USize}
    {P Q : SPhase → List Bool → Prop} (hPQ : ∀ p bs, P p bs → Q p bs) (h : DecidedAt a stop p B pos q P) :
    DecidedAt a stop p B pos q Q := by
  obtain ⟨p1, h1, pos1, a1, a2, a3, a4, a5, a6⟩ := h
  exact ⟨p1, h1, pos1, a1, a2, a3, a4, a5, fun t => hPQ _ _ (a6 t)⟩

/-- What a stream step must do, for the input so far and whatever whole bytes follow. -/
structure DStepOk {α : Type} (S : Sem α) (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (pos : USize) (r : Dec) : Prop where
  next : r.status = .next → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ t : List UInt8, sLeave S p (D.bits a pos stop (bits t)) = srest S p' (r.bits a r.pos stop (bits t))) ∧ SDown p p' ∧ OutD p p' D r ∧
    ∀ t : List UInt8, SReach p (D.bits a pos stop (bits t)) p' (r.bits a r.pos stop (bits t))
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', DRel r p' ∧
    (∀ t : List UInt8, sLeave S p (D.bits a pos stop (bits t)) = sLeave S p' (r.bits a r.pos stop (bits t))) ∧ sLeave S p' r.held = none ∧ SDownEq p p' (r.cmd.pend = D.cmd.pend) ∧
    (∀ w st, p = .mblock w st → ∀ t : List UInt8, r.bits a r.pos stop (bits t) = D.bits a pos stop (bits t)) ∧ OutD p p' D r ∧
    (∀ t : List UInt8, SReach p (D.bits a pos stop (bits t)) p' (r.bits a r.pos stop (bits t))) ∧ SShort p' r.held
  needsOutput : r.status = .needsOutput → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ t : List UInt8, sLeave S p (D.bits a pos stop (bits t)) = sLeave S p' (r.bits a r.pos stop (bits t))) ∧ r.cmd.pend.toNat ≠ 0 ∧ SDownEq p p' (r.cmd.pend = D.cmd.pend) ∧
    (∀ w st, p = .mblock w st → ∀ t : List UInt8, r.bits a r.pos stop (bits t) = D.bits a pos stop (bits t)) ∧ OutD p p' D r ∧
    ∀ t : List UInt8, SReach p (D.bits a pos stop (bits t)) p' (r.bits a r.pos stop (bits t))
  memory : r.status = .memory → pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ r.limit = D.limit ∧ D.cmd.pend = 0 ∧
    ((∃ w, p = .mblock w ⟨[], 0, initialDistances⟩) ∨ ∃ w st last mlen g q, p = .hdr w st last mlen g q)
  bad : r.status = .bad → (∀ t : List UInt8, sLeave S p (D.bits a pos stop (bits t)) = none) ∧
    DecidedAt a stop p (fun t => D.bits a pos stop (bits t)) pos r.pos (fun p1 bs => sLeave S p1 bs = none)

end Brotli.Decoder
