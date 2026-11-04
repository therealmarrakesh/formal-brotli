import Brotli.Decoder.WorkCmd

/-!
# The work of the stream's steps and of a call

Each function here mirrors the stream's step, loop or call function of the same name without its `W`, branch by branch,
and counts the rounds of its loops. A loop that can stop early counts all the rounds it could take.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The steps -/

/-- The work of `stepDWbits`: the refill, and the window's zeros. -/
def stepDWbitsW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  if hp : pos ≤ stop then
    let rf := refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let r := wbitsFast ⟨rf.word, rf.count⟩
    refillW D.cmd.word D.cmd.count a pos stop hs + match r.status with
      | .ok => if (1 : UInt64) <<< r.a ≤ D.limit then zbW ((1 : UInt64) <<< r.a).toNat + 1 else 1
      | _ => 1
  else 1

/-- The work of `stepDMeta`: the refill, the start's read, and the header's first state. -/
def stepDMetaW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  if D.cmd.pend = 0 then
    if pos ≤ stop then refillW D.cmd.word D.cmd.count a pos stop hs + 2 else 1
  else 1

/-- The work of `rawRun`: a round for each byte, with a refill when the buffer runs low, and one for the round that
stops it. -/
def rawRunW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize) (p1 _p2 : UInt8)
    (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : Nat :=
  if hn : n = 0 then 1
  else
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hr : wpos.toNat < ring.size := by omega
    if 8 ≤ count then
      let byte := word.toUInt8
      1 + rawRunW a stop hs mask k hk hmask (n - USize.ofNat 1) (word >>> 8) (count - 8) pos (ringWrite ring wpos byte hr)
        (ringNext wpos mask) byte p1 hp ((size_ringWrite ring wpos byte hr).trans hsize) hnext
    else
      let r := refill word count a pos stop hs hp
      if h8 : 8 ≤ r.count ∧ r.pos ≤ stop then
        let byte := r.word.toUInt8
        refillW word count a pos stop hs + 1 + rawRunW a stop hs mask k hk hmask (n - USize.ofNat 1) (r.word >>> 8) (r.count - 8) r.pos
          (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1 (USize.le_iff_toNat_le.mp h8.2)
          ((size_ringWrite ring wpos byte hr).trans hsize) hnext
      else refillW word count a pos stop hs + 1
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred hn
    have := usize_ne hn
    omega

/-- The work of `stepDRaw`. -/
def stepDRawW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  let left := D.left
  if left = 0 then 1
  else
    let k := D.k
    let c := D.cmd
    if h : winCheck k c.wpos c.ring = true ∧ pos ≤ stop then
      if room k c.cap ≤ c.pend then 1
      else
        let n := usmin left.toUSize (room k c.cap - c.pend)
        have hsize := winCheck_size h.1
        have hwp := winCheck_pos h.1
        rawRunW a stop hs (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) n c.word c.count pos c.ring c.wpos c.p1 c.p2
          (USize.le_iff_toNat_le.mp h.2) hsize hwp + 1
    else 1

/-- The work of `mkHdr`: its sizes, a round for each byte of the maps and modes it checks, a table's check for each
tree and each block switch's two tables. -/
def mkHdrW (d : Done) : Nat :=
  20 + (d.lMap.size + 1) + (d.modes.size + 1) + (d.dMap.size + 1) +
    (d.treesL.toNat + d.nI.toNat + d.treesD.toNat + 3) * (fitsW + 1) + 6 * fitsW

/-- The work of `stepDHdr`: the header step, and at a header's end the command loop's header and first state, its
block type flags copied from the shared ones. -/
def stepDHdrW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  stepHW a stop hs D.hd pos +
    if (stepH a stop hs D.hd pos).status = .ready then mkHdrW (stepH a stop hs D.hd pos).d + 769 else 0

/-- The work of `stepDCmds`: the command loop, and at the commands' end the check that every block type occurred. -/
def stepDCmdsW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  runCmdW D.H D.k a stop hs cmdBudget D.cmd pos +
    if (runCmd D.H D.k a stop hs cmdBudget D.cmd pos).status = .done then 772 else 0

/-- The work of a step of the whole decoder. -/
def stepDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) : Nat :=
  match D.tag with
  | .wbits => stepDWbitsW a stop hs D D.pos
  | .mblock => stepDMetaW a stop hs D D.pos
  | .skip => 1
  | .raw => stepDRawW a stop hs D D.pos
  | .hdr => stepDHdrW a stop hs D D.pos
  | .cmds => stepDCmdsW a stop hs D D.pos
  | .ended => 1

/-- The work of the decoder's loop: its rounds and their steps. -/
def runDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Nat :=
  if he : D.tag = .ended then 1
  else
    let r := stepD a stop hs D
    stepDW a stop hs D + 1 + if hn : r.status = .next then runDW a stop hs r (h.step he hn) else 0
termination_by (RunArg.mk D h : RunArg a stop hs)
decreasing_by exact ⟨he, hn, rfl⟩

/-- The work of `flushAll`: a round for each byte it hands out, and two for each of its rounds. -/
def flushAllW (k : USize) (st : Cmd) (buf : ByteArray) (space : Nat) : Nat :=
  let p0 := st.pend
  if p0 = 0 ∨ space = 0 then 1
  else
    let r := flushCmd k st buf (USize.ofNat (min space 16777216))
    (p0 - r.st.pend).toNat + 2 +
      if _h : r.st.pend < p0 then flushAllW k r.st r.buf (space - (p0 - r.st.pend).toNat) else 0
termination_by st.pend.toNat
decreasing_by exact USize.lt_iff_toNat_lt.mp _h

/-- The work of `afterRun`: the bytes it hands out, and the end's check. -/
def afterRunW (r : Dec) (buf : ByteArray) (space : Nat) : Nat :=
  match r.status with
  | .needsInput => flushAllW r.k r.cmd buf space + 1
  | .next => flushAllW r.k r.cmd buf space + 2
  | _ => 1

/-- The work of a call: its rounds of the loop and of handing bytes out. -/
def callDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (final : Bool) (D : Dec) (h : DInv stop D) (buf : ByteArray)
    (space : Nat) : Nat :=
  runDW a stop hs (withCap D space) (h.withCap space) + 1 +
    if hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput then
      flushAllW (runD a stop hs (withCap D space) (h.withCap space)).k (runD a stop hs (withCap D space) (h.withCap space)).cmd buf space +
        if (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0 then
          if _hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space then
            callDW a stop hs final (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
              (flushD_inv (runD_full hO) buf space) (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf
              (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space
          else 1
        else 1
    else afterRunW (runD a stop hs (withCap D space) (h.withCap space)) buf space
termination_by space
decreasing_by exact _hlt

end Brotli.Decoder
