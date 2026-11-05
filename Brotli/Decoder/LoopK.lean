import Brotli.Decoder.Loop

/-!
# The compiled command loop

`runCmdE` is `runCmd` as the compiler runs it: one loop with the whole command state in local variables, so that no
step rebuilds a record. It does exactly what `runCmd` does, step for step: the same refills, reads and writes, in the
same order (AGENTS.md, design rule 1). `runCmd_csimp` proves the two equal, and every proof is about `runCmd`.

`kstep` is one step, ending in a continuation: `cont` takes the state's fields and goes on, `exit` takes the state as
a record and stops. It is inlined into `runCmdK`, whose `cont` is its own recursive call, so every step ends in a jump.
`kstep_eq` proves a step equal to `stepCmd` on the record built from the fields (`mkCmd`).
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The command state from its fields. -/
def mkCmd (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) (status : StepStatus) : Cmd :=
  ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, pos, status⟩

/-- A step's continuation: the state's fields and the position. -/
abbrev KCont (α : Type) : Type :=
  UInt64 → UInt64 → ByteArray → USize → USize → USize → USize → UInt8 → UInt8 → UInt64 → UInt64 → UInt64 → UInt64 →
    Flags → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 →
    UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → ByteArray → USize → Tag → UInt64 → USize → α

/-- How a step's result goes on: with the record's fields if it moved on, otherwise with the record. -/
def kcase {α : Type} (cont : KCont α) (exit : Cmd → α) (r : Cmd) : α :=
  if r.status = .next then
    cont r.word r.count r.ring r.wpos r.pend r.cap r.written r.p1 r.p2 r.remaining r.iCount r.lCount r.dCount r.flags
      r.ext.iCur r.ext.iPrev r.ext.lCur r.ext.lPrev r.ext.dCur r.ext.dPrev r.ext.d0 r.ext.d1 r.ext.d2 r.ext.d3
      r.ext.code r.ext.ilen r.ext.clen r.ext.copyBits r.ext.copyBase r.ext.dist r.ext.wordBuf r.ext.wordPos r.tag r.left
      r.pos
  else exit r

/-- What a run holds while the loop is inside it: the facts its iterations need, by the kind of run. A literal run needs
the buffer, the window and the context map's bounds; a copy run, the window and the distance; a word run, the window
and the word's bounds. -/
def RunInv (H : Hdr) (k stop : USize) (tag : Tag) (m mb mo cd ri : USize) (word count : UInt64) (pos wpos : USize)
    (ring wordBuf : ByteArray) : Prop :=
  match tag with
  | .literals => pos.toNat ≤ stop.toNat ∧ (BitBuffer.mk word count).Wf ∧ k.toNat ≤ 24 ∧ ring.size = 2 ^ k.toNat ∧
      wpos.toNat < 2 ^ k.toNat ∧ mb.toNat + 64 ≤ H.lMap.size ∧ mo.toNat + 512 ≤ 2048 ∧ mo.toNat % 512 = 0
  | .copy => k.toNat ≤ 24 ∧ ring.size = 2 ^ k.toNat ∧ wpos.toNat < 2 ^ k.toNat ∧ 1 ≤ cd.toNat ∧ cd.toNat ≤ 2 ^ k.toNat
  | .word => k.toNat ≤ 24 ∧ ring.size = 2 ^ k.toNat ∧ wpos.toNat < 2 ^ k.toNat ∧ ri.toNat + m.toNat ≤ wordBuf.size ∧
      ri.toNat + m.toNat ≤ 2 ^ 32 - 1
  | _ => True

/-- A literal run's entry: its length, the context map's base and the context mode's offset, the buffer and position. -/
abbrev KRunL (α : Type) (H : Hdr) (k stop wpos : USize) (ring wordBuf : ByteArray) : Type :=
  (run mb mo : USize) → (w c : UInt64) → (p : USize) → RunInv H k stop .literals run mb mo 0 0 w c p wpos ring wordBuf → α

/-- A copy run's entry: its length and distance, the buffer and position. -/
abbrev KRunC (α : Type) (H : Hdr) (k stop wpos : USize) (ring wordBuf : ByteArray) : Type :=
  (run cd : USize) → (w c : UInt64) → (p : USize) → RunInv H k stop .copy run 0 0 cd 0 w c p wpos ring wordBuf → α

/-- A word run's entry: its length, the buffer and position. -/
abbrev KRunW (α : Type) (H : Hdr) (k stop wpos : USize) (ring wordBuf : ByteArray) (wordPos : USize) : Type :=
  (run : USize) → (w c : UInt64) → (p : USize) → RunInv H k stop .word run 0 0 0 wordPos w c p wpos ring wordBuf → α

/-- `applyDistance` on the fields. -/
@[inline] def kapply {α : Type} (cont : KCont α) (exit : Cmd → α)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) (dcode d : UInt64) : α :=
  if written.toUInt64 < d then
    if h : dictValid clen (d - (written.toUInt64 + 1)) then
      let wb := dictBuild clen (d - (written.toUInt64 + 1)) h
      if remaining < wb.usize.toUInt64 then
        exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
      else
        cont word count ring wpos pend cap written p1 p2 (remaining - wb.usize.toUInt64) iCount lCount dCount flags iCur
          iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wb 0 .word left pos
    else
      exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
        dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
  else if remaining < clen then
    exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)
  else if dcode = 0 then
    cont word count ring wpos pend cap written p1 p2 (remaining - clen) iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase d wordBuf wordPos .copy clen pos
  else
    cont word count ring wpos pend cap written p1 p2 (remaining - clen) iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d d0 d1 d2 code ilen clen copyBits copyBase d wordBuf wordPos .copy clen pos

/-- One step of the command loop on the fields: `stepCmd`, ending in a continuation. A literal, copy or word step
ends in its run's entry (`runL`, `runC`, `runW`) rather than running the run. -/
@[inline] def kstep {α : Type} (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (cont : KCont α) (exit : Cmd → α)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize)
    (runL : KRunL α H k stop wpos ring wordBuf) (runC : KRunC α H k stop wpos ring wordBuf)
    (runW : KRunW α H k stop wpos ring wordBuf wordPos) : α :=
  if hp : pos ≤ stop then
    let rf := refill word count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let w := rf.word
    let c := rf.count
    let p := rf.pos
    match tag with
    | .command =>
      if remaining = 0 then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .done)
      else if iCount = 0 then
        if hn : 2 ≤ H.nI then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI (H.swI hn').1 (H.swI hn').2 H.nI iCur iPrev w c
          match r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining (r.blockCount - 1) lCount dCount
              { flags with
                fI0 := markWord flags.fI0 r.cur 0, fI1 := markWord flags.fI1 r.cur 1, fI2 := markWord flags.fI2 r.cur 2
                fI3 := markWord flags.fI3 r.cur 3 }
              r.cur iCur lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .insertCopy left p
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p .bad)
      else
        cont w c ring wpos pend cap written p1 p2 remaining (iCount - 1) lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p
    | .insertCopy =>
      if ht : iCur < H.nI then
        have ht' := UInt64.lt_iff_toNat_lt.mp ht
        have hb : 4 * iCur.toNat + 4 ≤ H.icBase.size := by
          rw [H.icSize]
          omega
        let v := lookup H.arena (tableBase H.icBase iCur hb H.ic32) w
          (by rw [tableBase_toNat]; exact H.icFits _ ht') H.lit.arena32
        if wordBits v ≤ c then
          if hc : wordSym v < 704 then
            let b1 := (BitBuffer.mk w c).drop (wordBits v)
            let row := insertRow (wordSym v) (lt704 hc)
            if rowBits row ≤ b1.count then
              let b2 := b1.drop (rowBits row)
              let cr := copyRow (wordSym v) (lt704 hc)
              cont b2.word b2.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
                lPrev dCur dPrev d0 d1 d2 d3 (wordSym v) (rowBase row + b1.peek (rowBits row)) clen (rowBits cr)
                (rowBase cr) dist wordBuf wordPos .copyLength left p
            else
              exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
                dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p
                .needsInput)
          else
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p .needsInput)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .insertCopy left p .bad)
    | .copyLength =>
      if remaining < ilen then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copyLength left p .bad)
      else if copyBits ≤ c then
        let b := BitBuffer.mk w c
        let b1 := b.drop copyBits
        cont b1.word b1.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen (copyBase + b.peek copyBits) copyBits copyBase dist wordBuf wordPos .literals
          ilen p
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copyLength left p .needsInput)
    | .literals =>
      if left = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p
      else if lCount = 0 then
        if hn : 2 ≤ H.nL then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL (H.swL hn').1 (H.swL hn').2 H.nL lCur lPrev w c
          match r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining iCount r.blockCount dCount
              { flags with
                fL0 := markWord flags.fL0 r.cur 0, fL1 := markWord flags.fL1 r.cur 1, fL2 := markWord flags.fL2 r.cur 2
                fL3 := markWord flags.fL3 r.cur 3 }
              iCur iPrev r.cur lCur dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .literals left p
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
      else if room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .needsOutput)
      else if ht : lCur < H.nL then
        have ht' := UInt64.lt_iff_toNat_lt.mp ht
        have hm : lCur.toUSize.toNat < H.modes.size := by
          rw [cur_usize ht', H.modesSize]
          exact ht'
        have hmLt := H.modesLt _ hm
        if h : winCheck k wpos ring = true ∧ p ≤ stop ∧ wfCheck w c = true then
          runL (umin left (umin lCount (room k cap - pend).toUInt64)).toUSize (lCur <<< 6).toUSize
            ((H.modes.uget lCur.toUSize hm).toUInt64 <<< 9).toUSize w c p
            ⟨USize.le_iff_toNat_le.mp h.2.1, wfCheck_wf h.2.2, winCheck_k h.1, winCheck_size h.1, winCheck_pos h.1,
              by rw [mapBase_toNat ht', H.lMapSize]; omega, by rw [modeOff_toNat hmLt]; omega,
              by rw [modeOff_toNat hmLt]; omega⟩
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left p .bad)
    | .distance =>
      if remaining = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p
      else if code < 128 then
        if d0 = 0 then
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
        else
          kapply cont exit w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p 0 d0
      else if dCount = 0 then
        if hn : 2 ≤ H.nD then
          let hn' := UInt64.le_iff_toNat_le.mp hn
          let r := blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD (H.swD hn').1 (H.swD hn').2 H.nD dCur dPrev w c
          match r.status with
          | .ok =>
            cont r.word r.count ring wpos pend cap written p1 p2 remaining iCount lCount (r.blockCount - 1)
              { flags with
                fD0 := markWord flags.fD0 r.cur 0, fD1 := markWord flags.fD1 r.cur 1, fD2 := markWord flags.fD2 r.cur 2
                fD3 := markWord flags.fD3 r.cur 3 }
              iCur iPrev lCur lPrev r.cur dCur d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
              .distanceSymbol left p
          | .short =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .needsInput)
          | .bad =>
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distance left p .bad)
      else
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount (dCount - 1) flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
    | .distanceSymbol =>
      if ht : dCur < H.nD then
        have ht' := UInt64.lt_iff_toNat_lt.mp ht
        have hi : (dMapIndex dCur clen).toNat < H.dMap.size := by
          have h1 := H.dMap32
          have h2 := H.dMapSize
          have hcid := distanceContextId_lt clen.toNat
          rw [dMapIndex_toNat (by omega)]
          omega
        let tree := H.dMap.uget (dMapIndex dCur clen) hi
        have htree : tree.toNat < H.treesD.toNat := H.dMapLt _ hi
        have hb : 4 * tree.toUInt64.toNat + 4 ≤ H.dBase.size := by
          rw [H.dSize, UInt8.toNat_toUInt64]
          omega
        have hfit : TableFits H.arena (tableBase H.dBase tree.toUInt64 hb H.d32).toNat := by
          rw [tableBase_toNat, UInt8.toNat_toUInt64]
          exact H.dFits _ htree
        let v := lookup H.arena (tableBase H.dBase tree.toUInt64 hb H.d32) w hfit H.lit.arena32
        if wordBits v ≤ c then
          let nbits := extraBitsFast H.npostfix H.ndirect (wordSym v)
          let b1 := (BitBuffer.mk w c).drop (wordBits v)
          if nbits ≤ 24 then
            if nbits ≤ b1.count then
              let b2 := b1.drop nbits
              let d := distFast H.npostfix H.ndirect d0 d1 d2 d3 (wordSym v) (b1.peek nbits)
              if d = 0 then
                exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
                  lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left
                  p .bad)
              else
                kapply cont exit b2.word b2.count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
                  iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
                  .distanceSymbol left p (wordSym v) d
            else
              exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
                dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
                .needsInput)
          else
            exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p .bad)
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p
            .needsInput)
      else
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .distanceSymbol left p .bad)
    | .copy =>
      if left = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p
      else if room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left p .needsOutput)
      else
        let run := (umin left (room k cap - pend).toUInt64).toUSize
        let d := dist.toUSize
        if h : winCheck k wpos ring = true ∧ USize.ofNat 1 ≤ d ∧ d ≤ ringSize k then
          runC run d w c p
            ⟨winCheck_k h.1, winCheck_size h.1, winCheck_pos h.1,
              by
                have := USize.le_iff_toNat_le.mp h.2.1
                rwa [usize_ofNat' (by decide)] at this,
              by
                have := USize.le_iff_toNat_le.mp h.2.2
                rwa [ringSize_toNat (winCheck_k h.1)] at this⟩
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left p .bad)
    | .word =>
      if wordBuf.usize - wordPos = 0 then
        cont w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
          d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .command left p
      else if room k cap ≤ pend then
        exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
          dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left p .needsOutput)
      else
        let run := usmin (wordBuf.usize - wordPos) (room k cap - pend)
        if h : winCheck k wpos ring = true ∧ wordPos.toNat + run.toNat ≤ wordBuf.size ∧
            wordPos.toNat + run.toNat ≤ 2 ^ 32 - 1 then
          runW run w c p ⟨winCheck_k h.1, winCheck_size h.1, winCheck_pos h.1, h.2.1, h.2.2⟩
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left p .bad)
  else
    exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)

-- Lean's own clean-up of the termination goals, before `decreasing_by`, needs more than the default budget here.
set_option maxHeartbeats 1000000 in
/-- `runCmd` on the fields: up to `n` steps, each ending in a jump to the next. With `inRun`, the loop is inside a
literal, copy or word run (by `tag`), `m` of its `run` iterations left; `mb` and `mo` are a literal run's context map
base and mode offset, `cd` a copy's distance, `ri` a word's index, and `hinv` what the run's iterations need. A run's
iterations are the loop's own, so no run returns a result; when it ends, the loop finishes the step as the step's
finish would, and goes on. -/
def runCmdK (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (inRun : Bool)
    (m run mb mo cd ri : USize)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize)
    (hinv : inRun = true → RunInv H k stop tag m mb mo cd ri word count pos wpos ring wordBuf) : Cmd :=
  match inRun, hinv with
  | true, hinv =>
    match tag, hinv with
    | .literals, hinv =>
        have hp : pos.toNat ≤ stop.toNat := (hinv rfl).1
        have hw : (BitBuffer.mk word count).Wf := (hinv rfl).2.1
        have hk : k.toNat ≤ 24 := (hinv rfl).2.2.1
        have hsize : ring.size = 2 ^ k.toNat := (hinv rfl).2.2.2.1
        have hwp : wpos.toNat < 2 ^ k.toNat := (hinv rfl).2.2.2.2.1
        have hmb : mb.toNat + 64 ≤ H.lMap.size := (hinv rfl).2.2.2.2.2.1
        have hm : mo.toNat + 512 ≤ 2048 := (hinv rfl).2.2.2.2.2.2.1
        have hd : mo.toNat % 512 = 0 := (hinv rfl).2.2.2.2.2.2.2
        if _hm0 : m = 0 then
          -- the run is done: the literal step's finish, with nothing left of the run
          runCmdK H k a stop hs n false 0 0 0 0 0 0 word count ring wpos (pend + (run - 0)) cap
            (usmin (ringSize k - USize.ofNat 16) (written + (run - 0))) p1 p2 (remaining - (run - 0).toUInt64) iCount
            (lCount - (run - 0).toUInt64) dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
            copyBase dist wordBuf wordPos .literals (left - (run - 0).toUInt64) pos (fun h => nomatch h)
        else
          let r := refill word count a pos stop hs hp
          let rw := r.word
          let rc := r.count
          let rp := r.pos
          have hspec := refill_spec hs hp hw
          let cid := cidFast mo p1 p2 hm
          have hcid : cid.toNat < 64 := cid_lt hm hd
          have hi : (mapIndex mb cid).toNat < H.lMap.size := by
            rw [mapIndex_toNat (by have := H.lit.map32; omega)]
            omega
          let tree := H.lMap.uget (mapIndex mb cid) hi
          have htree : tree.toNat < H.treesL.toNat := H.lit.treeLt _ hi
          have hb : 4 * tree.toNat + 4 ≤ H.litBase.size := by
            rw [H.lit.baseSize]
            omega
          let base := treeBase H.litBase tree hb H.lit.base32
          have hfit : TableFits H.arena base.toNat := by
            rw [treeBase_toNat]
            exact H.lit.fits _ htree
          let v := lookup H.arena base rw hfit H.lit.arena32
          let l := v &&& 15
          if hl : l ≤ rc then
            let byte := (v >>> 4).toUInt8
            have hl63 : l.toNat < 64 := by
              have : (v &&& 15).toNat = v.toNat % 16 := by
                rw [UInt64.toNat_and]
                exact Nat.and_two_pow_sub_one_eq_mod v.toNat 4
              show (v &&& 15).toNat < 64
              omega
            have hr : wpos.toNat < ring.size := by omega
            let ring' := ringWrite ring wpos byte hr
            have hsize' : ring'.size = 2 ^ k.toNat := (size_ringWrite ring wpos byte hr).trans hsize
            have hnext : (ringNext wpos (ringMask k)).toNat < 2 ^ k.toNat := by
              unfold ringNext
              rw [USize.toNat_and, ringMask_toNat hk, Nat.and_two_pow_sub_one_eq_mod]
              exact Nat.mod_lt _ (Nat.two_pow_pos _)
            let b := (BitBuffer.mk rw rc).drop l
            have := usize_pred _hm0
            have : (m - 1).toNat = m.toNat - 1 := usize_pred _hm0
            have := usize_ne _hm0
            runCmdK H k a stop hs n true (m - USize.ofNat 1) run mb mo cd ri b.word b.count ring' (ringNext wpos (ringMask k))
              pend cap written byte p1 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code
              ilen clen copyBits copyBase dist wordBuf wordPos .literals left rp
              (fun _ => ⟨hspec.2.2.1, BitBuffer.drop_wf hspec.1 hl63 (UInt64.le_iff_toNat_le.mp hl), hk, hsize', hnext, hmb,
                hm, hd⟩)
          else
            -- the bits held can't finish a literal: the step's finish, with `m` left, waiting for input
            mkCmd rw rc ring wpos (pend + (run - m)) cap (usmin (ringSize k - USize.ofNat 16) (written + (run - m))) p1 p2
              (remaining - (run - m).toUInt64) iCount (lCount - (run - m).toUInt64) dCount flags iCur iPrev lCur lPrev dCur
              dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals (left - (run - m).toUInt64)
              rp .needsInput
    | .copy, hinv =>
        have hk : k.toNat ≤ 24 := (hinv rfl).1
        have hsize : ring.size = 2 ^ k.toNat := (hinv rfl).2.1
        have hwp : wpos.toNat < 2 ^ k.toNat := (hinv rfl).2.2.1
        have hd1 : 1 ≤ cd.toNat := (hinv rfl).2.2.2.1
        have hd2 : cd.toNat ≤ 2 ^ k.toNat := (hinv rfl).2.2.2.2
        if _hm0 : m = 0 then
          -- the copy is done: the copy step's finish
          runCmdK H k a stop hs n false 0 0 0 0 0 0 word count ring wpos (pend + run) cap
            (usmin (ringSize k - USize.ofNat 16) (written + run)) p1 p2 remaining iCount lCount dCount flags iCur iPrev
            lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy
            (left - run.toUInt64) pos (fun h => nomatch h)
        else
          have hb : (ringBack wpos cd (ringMask k) (ringSize k)).toNat < ring.size := by
            rw [ringBack_toNat hk (ringMask_toNat hk) (ringSize_toNat hk) hwp hd1 hd2, hsize]
            exact ringIdx_lt hwp (by omega)
          let byte := ring.uget (ringBack wpos cd (ringMask k) (ringSize k)) hb
          have hr : wpos.toNat < ring.size := by omega
          have hnext : (ringNext wpos (ringMask k)).toNat < 2 ^ k.toNat := by
            unfold ringNext
            rw [USize.toNat_and, ringMask_toNat hk, Nat.and_two_pow_sub_one_eq_mod]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          have := usize_pred _hm0
          have : (m - 1).toNat = m.toNat - 1 := usize_pred _hm0
          have := usize_ne _hm0
          runCmdK H k a stop hs n true (m - USize.ofNat 1) run mb mo cd ri word count (ringWrite ring wpos byte hr)
            (ringNext wpos (ringMask k)) pend cap written byte p1 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left pos
            (fun _ => ⟨hk, (size_ringWrite ring wpos byte hr).trans hsize, hnext, hd1, hd2⟩)
    | .word, hinv =>
        have hk : k.toNat ≤ 24 := (hinv rfl).1
        have hsize : ring.size = 2 ^ k.toNat := (hinv rfl).2.1
        have hwp : wpos.toNat < 2 ^ k.toNat := (hinv rfl).2.2.1
        have hb : ri.toNat + m.toNat ≤ wordBuf.size := (hinv rfl).2.2.2.1
        have hb32 : ri.toNat + m.toNat ≤ 2 ^ 32 - 1 := (hinv rfl).2.2.2.2
        if _hm0 : m = 0 then
          -- the word's run is done: the word step's finish
          runCmdK H k a stop hs n false 0 0 0 0 0 0 word count ring wpos (pend + run) cap
            (usmin (ringSize k - USize.ofNat 16) (written + run)) p1 p2 remaining iCount lCount dCount flags iCur iPrev
            lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf (wordPos + run) .word left pos
            (fun h => nomatch h)
        else
          have hnz := usize_ne _hm0
          have hpred := usize_pred _hm0
          have : (m - 1).toNat = m.toNat - 1 := usize_pred _hm0
          let byte := wordBuf.uget ri (by omega)
          have hr : wpos.toNat < ring.size := by omega
          have hnext : (ringNext wpos (ringMask k)).toNat < 2 ^ k.toNat := by
            unfold ringNext
            rw [USize.toNat_and, ringMask_toNat hk, Nat.and_two_pow_sub_one_eq_mod]
            exact Nat.mod_lt _ (Nat.two_pow_pos _)
          have hi : (ri + USize.ofNat 1).toNat = ri.toNat + 1 := usize_succ (by omega)
          runCmdK H k a stop hs n true (m - USize.ofNat 1) run mb mo cd (ri + USize.ofNat 1) word count
            (ringWrite ring wpos byte hr) (ringNext wpos (ringMask k)) pend cap written byte p1 remaining iCount lCount dCount
            flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word
            left pos
            (fun _ => ⟨hk, (size_ringWrite ring wpos byte hr).trans hsize, hnext, by rw [hi]; omega, by rw [hi]; omega⟩)
    | _, _ =>
      -- no run has another tag
      mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad
  | false, _ =>
    if _hn : n = 0 then
      mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next
    else
      have := usize_pred _hn
      have : (n - 1).toNat = n.toNat - 1 := usize_pred _hn
      have := usize_ne _hn
      kstep H k a stop hs
        (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
            dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
          runCmdK H k a stop hs (n - USize.ofNat 1) false 0 0 0 0 0 0 word count ring wpos pend cap written p1 p2 remaining
            iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
            wordBuf wordPos tag left pos (fun h => nomatch h))
        (fun c => c)
        word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
        d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
        (fun run mb mo w c p inv =>
          have := USize.toNat_lt_size run
          runCmdK H k a stop hs (n - USize.ofNat 1) true run run mb mo 0 0 w c ring wpos pend cap written p1 p2 remaining
            iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
            wordBuf wordPos .literals left p (fun _ => inv))
        (fun run cd w c p inv =>
          have := USize.toNat_lt_size run
          runCmdK H k a stop hs (n - USize.ofNat 1) true run run 0 0 cd 0 w c ring wpos pend cap written p1 p2 remaining
            iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist
            wordBuf wordPos .copy left p (fun _ => inv))
        (fun run w c p inv =>
          have := USize.toNat_lt_size run
          runCmdK H k a stop hs (n - USize.ofNat 1) true run run 0 0 0 wordPos w c ring wpos pend cap written p1 p2
            remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase
            dist wordBuf wordPos .word left p (fun _ => inv))
termination_by (n.toNat, if inRun then m.toNat + 1 else 0)
decreasing_by
  all_goals
    first
      | exact Prod.Lex.left _ _ (by omega)
      | exact Prod.Lex.right _ (by simp only [ite_true, ite_false]; omega)

/-- `runCmd` as the compiler runs it: the state taken apart once, then the loop on its fields. -/
def runCmdE (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) : Cmd :=
  match st with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
      ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
      tag, left, _, _⟩ =>
    runCmdK H k a stop hs n false 0 0 0 0 0 0 word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
      flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
      (fun h => nomatch h)

/-! ### The compiled loop is `runCmd` -/

/-- Takes both sides of an equation through the same tests: `split` reduces one side's test, and the hypothesis it
gives reduces the other side's copy. -/
macro "ksplit" : tactic =>
  `(tactic| repeat' (first
    | (split <;> rename_i h <;> (try simp only [h, ↓reduceIte, ↓reduceDIte, and_self, and_true, true_and]))
    | rfl
    | contradiction))

section
variable {α : Type} (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
  (cont : KCont α) (exit : Cmd → α)
  (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
  (remaining iCount lCount dCount : UInt64) (flags : Flags)
  (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
  (wordBuf : ByteArray) (wordPos : USize) (left : UInt64) (pos sp : USize) (ss : StepStatus)
  (runL : KRunL α H k stop wpos ring wordBuf) (runC : KRunC α H k stop wpos ring wordBuf)
  (runW : KRunW α H k stop wpos ring wordBuf wordPos)

/-- What a step on the fields must equal, for a tag. -/
abbrev KStepIs (tag : Tag) : Prop :=
  kstep H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos runL runC
      runW =
    kcase cont exit (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount
      dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
      tag left sp ss) pos)

/-- A literal run's entry does what the literal step's run and finish do. -/
abbrev HypL : Prop :=
  ∀ (run mb mo : USize) (w c : UInt64) (p : USize) (inv : RunInv H k stop .literals run mb mo 0 0 w c p wpos ring wordBuf),
    runL run mb mo w c p inv = kcase cont exit (finishLiterals
      (mkCmd w c ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left sp ss)
      (literalRun H.lit a stop hs mb mo (ringMask k) k.toNat inv.2.2.2.2.2.1 inv.2.2.2.2.2.2.1 inv.2.2.2.2.2.2.2
        (ringMask_toNat inv.2.2.1) inv.2.2.1 run w c p wpos ring p1 p2 inv.1 inv.2.1 inv.2.2.2.1 inv.2.2.2.2.1)
      run (ringSize k))

/-- A copy run's entry does what the copy step's run and finish do. -/
abbrev HypC : Prop :=
  ∀ (run cd : USize) (w c : UInt64) (p : USize) (inv : RunInv H k stop .copy run 0 0 cd 0 w c p wpos ring wordBuf),
    runC run cd w c p inv = kcase cont exit (finishCopy
      (mkCmd w c ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left sp ss)
      (copyRun cd (ringMask k) (ringSize k) k.toNat inv.1 (ringMask_toNat inv.1) (ringSize_toNat inv.1) inv.2.2.2.1
        inv.2.2.2.2 run ring wpos p1 p2 inv.2.1 inv.2.2.1)
      run (ringSize k) p)

/-- A word run's entry does what the word step's run and finish do. -/
abbrev HypW : Prop :=
  ∀ (run : USize) (w c : UInt64) (p : USize) (inv : RunInv H k stop .word run 0 0 0 wordPos w c p wpos ring wordBuf),
    runW run w c p inv = kcase cont exit (finishWord
      (mkCmd w c ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
        dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left sp ss)
      (wordRun wordBuf (ringMask k) k.toNat inv.1 (ringMask_toNat inv.1) run wordPos ring wpos p1 p2 inv.2.2.2.1
        inv.2.2.2.2 inv.2.1 inv.2.2.1)
      run (ringSize k) p)

-- The simp sets below unfold every step and accessor a tag may reach; which accessors a tag's proof uses isn't worth
-- tracking by hand, so the linter for unused simp arguments is off for these eight lemmas.
set_option linter.unusedSimpArgs false

theorem kstep_command (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .command := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCommand, markStep, Cmd.iCur, Cmd.iPrev]
  ksplit

theorem kstep_insertCopy (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .insertCopy := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepInsertCopy, insertStep, markStep, Cmd.iCur]
  ksplit

theorem kstep_copyLength (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .copyLength := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCopyLength, markStep, Cmd.ilen, Cmd.copyBits, Cmd.copyBase]
  ksplit

theorem kstep_literals (hp : pos ≤ stop)
    (hL : HypL H k a stop hs cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runL) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .literals := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  -- the run and its finish stay folded, to meet `hL`
  simp only [mkCmd, stepAt, stepLiterals, literalsRun, markStep, Cmd.lCur, Cmd.lPrev]
  ksplit
  all_goals exact hL _ _ _ _ _ _ _

theorem kstep_distance (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .distance := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepDistance, applyDistance, applyWord, applyBuilt, kapply, markStep, Cmd.code, Cmd.d0,
    Cmd.d1, Cmd.d2, Cmd.clen, Cmd.dCur, Cmd.dPrev]
  ksplit

theorem kstep_distanceSymbol (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .distanceSymbol := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepDistanceSymbol, distanceThrough, distanceStep, setBits, applyDistance, applyWord,
    applyBuilt, kapply, markStep, Cmd.dCur, Cmd.clen, Cmd.d0, Cmd.d1, Cmd.d2, Cmd.d3]
  -- `split` doesn't take this outer test apart, so both sides are rewritten by its case; the two tests are the same
  -- term, so one rewrite takes both
  by_cases ht : dCur < H.nD
  · rw [dite_eq_left ht]
    ksplit
  · simp only [ht, ↓reduceDIte]
    rfl

theorem kstep_copy (hp : pos ≤ stop)
    (hC : HypC H k stop cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runC) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .copy := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCopy, markStep, Cmd.dist]
  ksplit
  all_goals exact hC _ _ _ _ _ _

theorem kstep_word (hp : pos ≤ stop)
    (hW : HypW H k stop cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runW) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC runW
      .word := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepWord, markStep, Cmd.wordBuf, Cmd.wordPos]
  ksplit
  all_goals exact hW _ _ _ _ _

set_option linter.unusedSimpArgs true

/-- A step on the fields is `stepCmd` on the record they make, gone on with, given that the runs' entries do what the
runs and their finishes do. -/
theorem kstep_eq (tag : Tag)
    (hL : HypL H k a stop hs cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runL)
    (hC : HypC H k stop cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runC)
    (hW : HypW H k stop cont exit ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left sp ss runW) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss runL runC
      runW tag := by
  by_cases hp : pos ≤ stop
  · cases tag
    · exact kstep_command H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp
    · exact kstep_insertCopy H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp
    · exact kstep_copyLength H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp
    · exact kstep_literals H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp hL
    · exact kstep_distance H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp
    · exact kstep_distanceSymbol H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount
        lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
        wordPos left pos sp ss runL runC runW hp
    · exact kstep_copy H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp hC
    · exact kstep_word H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss runL runC runW hp hW
  · unfold KStepIs kstep stepCmd
    rw [dite_eq_right hp, dite_eq_right hp]
    rfl

end

/-- The loop's step continuation: on to the next step, with `n` steps left. -/
abbrev kc (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) : KCont Cmd :=
  fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
    runCmdK H k a stop hs n false 0 0 0 0 0 0 word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
      flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
      (fun h => nomatch h)

section
variable (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n run mb mo cd : USize)
  (pend cap written : USize) (remaining iCount lCount dCount : UInt64) (flags : Flags)
  (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
  (wordBuf : ByteArray) (wordPos : USize) (left : UInt64) (sp : USize) (ss : StepStatus)

/-- A literal run in the loop is `literalRun` and the step's finish, then the loop's next step. -/
theorem runK_literals (ri : USize) :
    ∀ (M : Nat) (m : USize) (word count : UInt64) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (pos : USize)
      (hinv : true = true → RunInv H k stop .literals m mb mo cd ri word count pos wpos ring wordBuf), m.toNat = M →
      runCmdK H k a stop hs n true m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          .literals left pos hinv =
        kcase (kc H k a stop hs n) id (finishLiterals
          (mkCmd word count ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
            lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals left sp ss)
          (literalRun H.lit a stop hs mb mo (ringMask k) k.toNat (hinv rfl).2.2.2.2.2.1 (hinv rfl).2.2.2.2.2.2.1
            (hinv rfl).2.2.2.2.2.2.2 (ringMask_toNat (hinv rfl).2.2.1) (hinv rfl).2.2.1 m word count pos wpos ring p1 p2
            (hinv rfl).1 (hinv rfl).2.1 (hinv rfl).2.2.2.1 (hinv rfl).2.2.2.2.1)
          run (ringSize k)) := by
  intro M
  induction M with
  | zero =>
    intro m word count ring wpos p1 p2 pos hinv hM
    have hm : m = 0 := usize_zero hM
    subst hm
    rw [runCmdK, literalRun]
    simp only [↓reduceDIte, finishLiterals, kcase, ↓reduceIte]
    rfl
  | succ M ih =>
    intro m word count ring wpos p1 p2 pos hinv hM
    have hm : m ≠ 0 := fun e => by rw [e] at hM; exact Nat.succ_ne_zero _ hM.symm
    rw [runCmdK, literalRun]
    simp only [hm, ↓reduceDIte]
    split
    · exact ih _ _ _ _ _ _ _ _ _ (by rw [usize_pred hm]; omega)
    · simp only [finishLiterals, kcase, hm, ↓reduceIte]
      rfl

/-- A copy run in the loop is `copyRun` and the step's finish, then the loop's next step. -/
theorem runK_copy (ri : USize) :
    ∀ (M : Nat) (m : USize) (word count : UInt64) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (pos : USize)
      (hinv : true = true → RunInv H k stop .copy m mb mo cd ri word count pos wpos ring wordBuf), m.toNat = M →
      runCmdK H k a stop hs n true m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          .copy left pos hinv =
        kcase (kc H k a stop hs n) id (finishCopy
          (mkCmd word count ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
            lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .copy left sp ss)
          (copyRun cd (ringMask k) (ringSize k) k.toNat (hinv rfl).1 (ringMask_toNat (hinv rfl).1)
            (ringSize_toNat (hinv rfl).1) (hinv rfl).2.2.2.1 (hinv rfl).2.2.2.2 m ring wpos p1 p2 (hinv rfl).2.1
            (hinv rfl).2.2.1)
          run (ringSize k) pos) := by
  intro M
  induction M with
  | zero =>
    intro m word count ring wpos p1 p2 pos hinv hM
    have hm : m = 0 := usize_zero hM
    subst hm
    rw [runCmdK, copyRun]
    simp only [↓reduceDIte, finishCopy, kcase, ↓reduceIte]
    rfl
  | succ M ih =>
    intro m word count ring wpos p1 p2 pos hinv hM
    have hm : m ≠ 0 := fun e => by rw [e] at hM; exact Nat.succ_ne_zero _ hM.symm
    rw [runCmdK, copyRun]
    simp only [hm, ↓reduceDIte]
    exact ih _ _ _ _ _ _ _ _ _ (by rw [usize_pred hm]; omega)

/-- A word run in the loop is `wordRun` and the step's finish, then the loop's next step. -/
theorem runK_word :
    ∀ (M : Nat) (m ri : USize) (word count : UInt64) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (pos : USize)
      (hinv : true = true → RunInv H k stop .word m mb mo cd ri word count pos wpos ring wordBuf), m.toNat = M →
      runCmdK H k a stop hs n true m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          .word left pos hinv =
        kcase (kc H k a stop hs n) id (finishWord
          (mkCmd word count ByteArray.empty wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur
            lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left sp ss)
          (wordRun wordBuf (ringMask k) k.toNat (hinv rfl).1 (ringMask_toNat (hinv rfl).1) m ri ring wpos p1 p2
            (hinv rfl).2.2.2.1 (hinv rfl).2.2.2.2 (hinv rfl).2.1 (hinv rfl).2.2.1)
          run (ringSize k) pos) := by
  intro M
  induction M with
  | zero =>
    intro m ri word count ring wpos p1 p2 pos hinv hM
    have hm : m = 0 := usize_zero hM
    subst hm
    rw [runCmdK, wordRun]
    simp only [↓reduceDIte, finishWord, kcase, ↓reduceIte]
    rfl
  | succ M ih =>
    intro m ri word count ring wpos p1 p2 pos hinv hM
    have hm : m ≠ 0 := fun e => by rw [e] at hM; exact Nat.succ_ne_zero _ hM.symm
    rw [runCmdK, wordRun]
    simp only [hm, ↓reduceDIte]
    exact ih _ _ _ _ _ _ _ _ _ _ (by rw [usize_pred hm]; omega)

end

/-- The loop on the fields, between steps, is `runCmd` on the record they make. -/
theorem runCmdK_eq (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (N : Nat) (n m run mb mo cd ri : USize) (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize)
      (p1 p2 : UInt8) (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos sp : USize) (ss : StepStatus)
      (hinv : false = true → RunInv H k stop tag m mb mo cd ri word count pos wpos ring wordBuf),
      n.toNat = N →
      runCmdK H k a stop hs n false m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          tag left pos hinv =
        runCmd H k a stop hs n (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left sp ss)
          pos := by
  intro N
  induction N with
  | zero =>
    intro n m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hinv hN
    have hn : n = 0 := usize_zero hN
    rw [runCmdK, runCmd]
    dsimp only
    rw [dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n m run mb mo cd ri word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hinv hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [runCmdK, runCmd]
    try dsimp only
    rw [dite_eq_right hn, dite_eq_right hn]
    rw [kstep_eq (sp := sp) (ss := ss)]
    · try dsimp only
      generalize stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
        flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left
        sp ss) pos = r
      obtain ⟨w, c, rg, wp, pe, cp, wr, q1, q2, rm, ic, lc, dc, fl,
        ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩, tg, lf, ps, st⟩ := r
      unfold kcase
      cases st
      · simp only [↓reduceIte]
        apply ih
        rw [usize_pred hn]
        omega
      all_goals rfl
    · intro run' mb' mo' w c p inv
      apply runK_literals
      rfl
    · intro run' cd' w c p inv
      apply runK_copy
      rfl
    · intro run' w c p inv
      apply runK_word
      rfl

/-- The compiler runs the loop on the fields in place of `runCmd`. -/
@[csimp] theorem runCmd_csimp : @runCmd = @runCmdE := by
  funext H k a stop hs n st pos
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, sp, ss⟩ := st
  exact (runCmdK_eq H k a stop hs _ n 0 0 0 0 0 0 word count ring wpos pend cap written p1 p2 remaining iCount lCount
    dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left
    pos sp ss (fun h => nomatch h) rfl).symm

end Brotli.Decoder
