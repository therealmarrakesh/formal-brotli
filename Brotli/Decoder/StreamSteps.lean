import Brotli.Decoder.StreamCmds

/-!
# The stream's steps

The places outside a header's and a meta-block's own machines: reading a header through the header machine, WBITS, a
meta-block's start, and the stream's end.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Through the header machine -/

/-- The place in a header. -/
def stepDHdr (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  let h := D.hd
  let c := D.cmd
  let left := D.left
  let D0 := clearHd D
  let r := stepH a stop hs h pos
  let rp := r.pos
  match r.status with
  | .next => { D0 with hd := r, pos := rp, status := .next }
  | .needsInput => { D0 with hd := r, pos := rp, status := .needsInput }
  | .bad => { D0 with hd := r, pos := rp, status := .bad }
  | .memory => { D0 with hd := r, pos := rp, status := .memory }
  | .ready =>
    match mkHdr r.d with
    | some H => { D0 with tag := .cmds, H := H, cmd := cmdStart c r.d r.word r.count left seenInit, pos := rp, status := .next }
    | none => { D0 with hd := r, pos := rp, status := .bad }

theorem stepDHdr_ok {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.hdr w st last mlen g p)) (hpos : pos.toNat ≤ stop.toNat) :
    DStepOk a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hall, hl, hleft, hm1, hm2, hR⟩ := hrel
  have ht' : tag = .hdr := ht
  subst ht'
  have hstep := stepH_ok (K := hdrK w st last mlen) (a := a) (hs := hs) hR hpos
  unfold stepDHdr
  dsimp only
  generalize stepH a stop hs hd pos = r at hstep
  cases hst : r.status with
  | next =>
    dsimp only
    obtain ⟨g', p', hR', h1, h2, h3⟩ := hstep.next hst
    exact ⟨fun _ => ⟨.hdr w st last mlen g' p', ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR'⟩, h1, h2, fun t => h3 _⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | needsInput =>
    dsimp only
    obtain ⟨h1, h2, hR', h3, h4⟩ := hstep.needsInput hst
    exact ⟨fun e => DStatus.noConfusion e, fun _ => ⟨h1, h2, .hdr w st last mlen g p, ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR'⟩,
      fun t => h3 _, h4⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | bad =>
    dsimp only
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ t => hstep.bad hst _⟩
  | memory =>
    dsimp only
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => rfl, fun e => DStatus.noConfusion e⟩
  | ready =>
    dsimp only
    obtain ⟨g', hu, hw, h1, h2, h3⟩ := hstep.ready hst
    obtain ⟨H', hmk, hrelH, _⟩ := mkHdr_ok hu
    rw [hmk]
    dsimp only
    have hRel := cmdStart_rel (c := cmd) (word := r.word) (count := r.count) (mlen := left) (seen := seenInit) seenInit_size seenInit_at hw hu
      (w := w) hall.win hall.produced
    rw [show left.toNat = mlen from hleft] at hRel
    exact ⟨fun _ => ⟨.cmds w last g'.m (.command (startState st mlen g'.m)), ⟨rfl, hl, hall.limit, hrelH, hRel⟩, h1, h2, fun t => h3 _⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩

/-! ### The stream's end -/

/-- A step's result at the stream's end: the stream is done if no more input comes, whatever came before. -/
def stepDEnded (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  let c := D.cmd
  let b : BitBuffer := ⟨c.word, c.count⟩
  let k := c.count &&& 7
  if b.peek k = 0 then
    let b1 := b.drop k
    if b1.count = 0 ∧ pos = stop then { D with cmd := { c with word := b1.word, count := b1.count }, pos := pos, status := .needsInput }
    else { D with pos := pos, status := .bad }
  else { D with pos := pos, status := .bad }

end Brotli.Decoder
