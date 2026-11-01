import Brotli.Decoder.StreamRaw

/-!
# The stream's state

`Dec` is the whole decoder's state between steps, and `DRel` ties it to a place in `srest`, which is what the spec still has
to do down to the stream's output.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The places a stream can pause. -/
inductive SPhase where
  | wbits
  | mblock (w : Nat) (st : StreamState)
  | skip (w : Nat) (st : StreamState) (last : Bool) (n : Nat)
  | raw (w : Nat) (st : StreamState) (last : Bool) (n : Nat)
  | hdr (w : Nat) (st : StreamState) (last : Bool) (mlen : Nat) (g : Gh) (p : HPhase)
  | cmds (w : Nat) (last : Bool) (m : MetaBlockHeader) (p : Phase)
  | ended (st : StreamState)

/-- What the spec still has to do from a place in a stream. -/
def srest : SPhase → List Bool → Option (List UInt8)
  | .wbits, bs => readWBITS bs >>= fun p => metaK (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2
  | .mblock w st, bs => metaK w st bs
  | .skip w st last n, bs => skipK w st last n bs
  | .raw w st last n, bs => rawK w st last n bs
  | .hdr w st last mlen g p, bs => hrest (hdrK w st last mlen) g p bs
  | .cmds w last m p, bs => rest w m (cmdK w last m) p bs
  | .ended st, bs => endOf st bs

/-- `decode` is the first place. -/
theorem decode_srest (input : List UInt8) : decode input = srest .wbits (bits input) := by
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

/-- How a stream step ended. -/
inductive DStatus where
  | next
  | needsInput
  | needsOutput
  | memory
  | bad
  deriving DecidableEq

/-- A dummy header, between meta-blocks. -/
def Hdr.none : Hdr where
  arena := ByteArray.empty
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
  ring : RingOk st.ring k st.wpos.toNat out
  bytes : ∀ b ∈ out, b < 256
  ctx : contextBytes out = (st.p1.toNat, st.p2.toNat)
  pendLe : st.pend.toNat ≤ 2 ^ k
  pendOut : st.pend.toNat ≤ out.length
  written : st.written.toNat = min w out.length
  d0 : ds.last = st.d0.toNat
  d1 : ds.secondToLast = st.d1.toNat
  d2 : ds.thirdToLast = st.d2.toNat
  d3 : ds.fourthToLast = st.d3.toNat
  dsLt : ds.last < 2 ^ 32 ∧ ds.secondToLast < 2 ^ 32 ∧ ds.thirdToLast < 2 ^ 32 ∧ ds.fourthToLast < 2 ^ 32

/-- The window part of the command loop's state. -/
theorem Core.toWin {w k : Nat} {m : MetaBlockHeader} {st : Cmd} {out : List Nat} {rem : Nat} {ds : Distances} {ic lit dist : BlockState}
    (h : Core w k m st out rem ds ic lit dist) : WinRel w k st out ds :=
  ⟨h.win, h.k24, h.ring, h.bytes, h.ctx, h.pendLe, h.pendOut, h.written, h.d0, h.d1, h.d2, h.d3, h.dsLt⟩

/-- What every place after WBITS has. -/
structure WinAll (D : Dec) (w : Nat) (st : StreamState) : Prop where
  win : WinRel w D.k.toNat D.cmd st.output st.distances
  produced : st.produced = st.output.length
  limit : D.limit.toNat + 132096 < 2 ^ 32

/-- A state stands for a place in a stream. -/
def DRel (D : Dec) : SPhase → Prop
  | .wbits => D.tag = .wbits ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ D.limit.toNat + 132096 < 2 ^ 32
  | .mblock w st => D.tag = .mblock ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAll D w st
  | .skip w st last n => D.tag = .skip ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAll D w st ∧ D.last = last ∧ D.left.toNat = n ∧
    D.cmd.count.toNat % 8 = 0 ∧ n < 2 ^ 32
  | .raw w st last n => D.tag = .raw ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ WinAll D w st ∧ D.last = last ∧ D.left.toNat = n ∧
    D.cmd.count.toNat % 8 = 0 ∧ n < 2 ^ 32
  | .hdr w st last mlen g p => D.tag = .hdr ∧ WinAll D w st ∧ D.last = last ∧ D.left.toNat = mlen ∧ 1 ≤ mlen ∧ mlen ≤ 16777216 ∧ HRel D.hd g p
  | .cmds w last m p => D.tag = .cmds ∧ D.last = last ∧ D.limit.toNat + 132096 < 2 ^ 32 ∧ HdrRel D.H m ∧ Rel w D.k.toNat m D.cmd p
  | .ended st => D.tag = .ended ∧ (BitBuffer.mk D.cmd.word D.cmd.count).Wf ∧ ∃ w, WinAll D w st

/-- The stream's bits at a state and position, with what follows. -/
def Dec.bits (D : Dec) (a : ByteArray) (pos stop : USize) (F : List Bool) : List Bool := availBits D.word D.count a pos stop F

/-- The bits a state holds. -/
def Dec.held (D : Dec) : List Bool := (BitBuffer.mk D.word D.count).held

/-- A state as a step leaves it. -/
@[inline] def markD (D : Dec) (pos : USize) (s : DStatus) : Dec := { D with pos := pos, status := s }

/-- What a stream step must do, for the input so far and whatever whole bytes follow. -/
structure DStepOk (a : ByteArray) (stop : USize) (p : SPhase) (D : Dec) (pos : USize) (r : Dec) : Prop where
  next : r.status = .next → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    ∀ t : List UInt8, srest p (D.bits a pos stop (bits t)) = srest p' (r.bits a r.pos stop (bits t))
  needsInput : r.status = .needsInput → r.pos = stop ∧ pos.toNat ≤ stop.toNat ∧ ∃ p', DRel r p' ∧
    (∀ t : List UInt8, srest p (D.bits a pos stop (bits t)) = srest p' (r.bits a r.pos stop (bits t))) ∧ srest p' r.held = none
  needsOutput : r.status = .needsOutput → ∃ p', DRel r p' ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    (∀ t : List UInt8, srest p (D.bits a pos stop (bits t)) = srest p' (r.bits a r.pos stop (bits t))) ∧ r.cmd.pend.toNat = 2 ^ r.k.toNat
  memory : r.status = .memory → r.limit = D.limit
  bad : r.status = .bad → ∀ t : List UInt8, srest p (D.bits a pos stop (bits t)) = none

end Brotli.Decoder
