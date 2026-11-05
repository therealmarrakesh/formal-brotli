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

/-- One step of the command loop on the fields: `stepCmd`, ending in a continuation. -/
@[inline] def kstep {α : Type} (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size)
    (cont : KCont α) (exit : Cmd → α)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) : α :=
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
          let run := (umin left (umin lCount (room k cap - pend).toUInt64)).toUSize
          let r := literalRun H.lit a stop hs (lCur <<< 6).toUSize ((H.modes.uget lCur.toUSize hm).toUInt64 <<< 9).toUSize
            (ringMask k) k.toNat
            (by
              rw [mapBase_toNat ht', H.lMapSize]
              omega)
            (by
              rw [modeOff_toNat hmLt]
              omega)
            (by
              rw [modeOff_toNat hmLt]
              omega)
            (ringMask_toNat (winCheck_k h.1)) (winCheck_k h.1) run w c p wpos ring p1 p2
            (USize.le_iff_toNat_le.mp h.2.1) (wfCheck_wf h.2.2) (winCheck_size h.1) (winCheck_pos h.1)
          let used := run - r.left
          if r.left = 0 then
            cont r.word r.count r.ring r.wpos (pend + used) cap (usmin (ringSize k - USize.ofNat 16) (written + used))
              r.p1 r.p2 (remaining - used.toUInt64) iCount (lCount - used.toUInt64) dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals
              (left - used.toUInt64) r.pos
          else
            exit (mkCmd r.word r.count r.ring r.wpos (pend + used) cap (usmin (ringSize k - USize.ofNat 16) (written + used))
              r.p1 r.p2 (remaining - used.toUInt64) iCount (lCount - used.toUInt64) dCount flags iCur iPrev lCur lPrev
              dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .literals
              (left - used.toUInt64) r.pos .needsInput)
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
          let r := copyRun d (ringMask k) (ringSize k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1))
            (ringSize_toNat (winCheck_k h.1))
            (by
              have := USize.le_iff_toNat_le.mp h.2.1
              rwa [usize_ofNat' (by decide)] at this)
            (by
              have := USize.le_iff_toNat_le.mp h.2.2
              rwa [ringSize_toNat (winCheck_k h.1)] at this)
            run ring wpos p1 p2 (winCheck_size h.1) (winCheck_pos h.1)
          cont w c r.ring r.wpos (pend + run) cap (usmin (ringSize k - USize.ofNat 16) (written + run)) r.p1 r.p2
            remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
            copyBase dist wordBuf wordPos .copy (left - run.toUInt64) p
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
          let r := wordRun wordBuf (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) run wordPos
            ring wpos p1 p2 h.2.1 h.2.2 (winCheck_size h.1) (winCheck_pos h.1)
          cont w c r.ring r.wpos (pend + run) cap (usmin (ringSize k - USize.ofNat 16) (written + run)) r.p1 r.p2
            remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits
            copyBase dist wordBuf (wordPos + run) .word left p
        else
          exit (mkCmd w c ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
            dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos .word left p .bad)
  else
    exit (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev
      dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .bad)

/-- `runCmd` on the fields: up to `n` steps, each ending in a jump to the next. -/
def runCmdK (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize)
    (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
    (remaining iCount lCount dCount : UInt64) (flags : Flags)
    (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
    (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos : USize) : Cmd :=
  if _hn : n = 0 then
    mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos .next
  else
    kstep H k a stop hs
      (fun word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
          dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =>
        runCmdK H k a stop hs (n - USize.ofNat 1) word count ring wpos pend cap written p1 p2 remaining iCount lCount
          dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
          tag left pos)
      (fun c => c)
      word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur dPrev
      d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos
termination_by n.toNat
decreasing_by
  have := usize_pred _hn
  have := usize_ne _hn
  omega

/-- `runCmd` as the compiler runs it: the state taken apart once, then the loop on its fields. -/
def runCmdE (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (n : USize) (st : Cmd)
    (pos : USize) : Cmd :=
  match st with
  | ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
      ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
      tag, left, _, _⟩ =>
    runCmdK H k a stop hs n word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
      lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos

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

/-- What a step on the fields must equal, for a tag. -/
abbrev KStepIs (tag : Tag) : Prop :=
  kstep H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =
    kcase cont exit (stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount
      dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
      tag left sp ss) pos)

-- The simp sets below unfold every step and accessor a tag may reach; which accessors a tag's proof uses isn't worth
-- tracking by hand, so the linter for unused simp arguments is off for these eight lemmas.
set_option linter.unusedSimpArgs false

theorem kstep_command (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .command := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCommand, markStep, Cmd.iCur, Cmd.iPrev]
  ksplit

theorem kstep_insertCopy (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .insertCopy := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepInsertCopy, insertStep, markStep, Cmd.iCur]
  ksplit

theorem kstep_copyLength (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .copyLength := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCopyLength, markStep, Cmd.ilen, Cmd.copyBits, Cmd.copyBase]
  ksplit

theorem kstep_literals (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .literals := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepLiterals, literalsRun, finishLiterals, clearRing, markStep, Cmd.lCur, Cmd.lPrev]
  ksplit

theorem kstep_distance (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .distance := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepDistance, applyDistance, applyWord, applyBuilt, kapply, markStep, Cmd.code, Cmd.d0,
    Cmd.d1, Cmd.d2, Cmd.clen, Cmd.dCur, Cmd.dPrev]
  ksplit

theorem kstep_distanceSymbol (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
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

theorem kstep_copy (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .copy := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepCopy, finishCopy, clearRing, markStep, Cmd.dist]
  ksplit

theorem kstep_word (hp : pos ≤ stop) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss
      .word := by
  unfold KStepIs kstep stepCmd
  rw [dite_eq_left hp, dite_eq_left hp]
  simp only [mkCmd, stepAt, stepWord, finishWord, clearRing, markStep, Cmd.wordBuf, Cmd.wordPos]
  ksplit

set_option linter.unusedSimpArgs true

/-- A step on the fields is `stepCmd` on the record they make, gone on with. -/
theorem kstep_eq (tag : Tag) :
    KStepIs H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur
      iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos left pos sp ss tag := by
  by_cases hp : pos ≤ stop
  · cases tag
    · exact kstep_command H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_insertCopy H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_copyLength H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_literals H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_distance H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_distanceSymbol H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount
        lCount dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf
        wordPos left pos sp ss hp
    · exact kstep_copy H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
    · exact kstep_word H k a stop hs cont exit word count ring wpos pend cap written p1 p2 remaining iCount lCount
        dCount flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos
        left pos sp ss hp
  · unfold KStepIs kstep stepCmd
    rw [dite_eq_right hp, dite_eq_right hp]
    rfl

end

/-- The loop on the fields is `runCmd` on the record they make. -/
theorem runCmdK_eq (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (ring : ByteArray) (wpos pend cap written : USize) (p1 p2 : UInt8)
      (remaining iCount lCount dCount : UInt64) (flags : Flags)
      (iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist : UInt64)
      (wordBuf : ByteArray) (wordPos : USize) (tag : Tag) (left : UInt64) (pos sp : USize) (ss : StepStatus),
      n.toNat = N →
      runCmdK H k a stop hs n word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev
          lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos =
        runCmd H k a stop hs n (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
          iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left sp ss)
          pos := by
  intro N
  induction N with
  | zero =>
    intro n word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
      dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hN
    have hn : n = 0 := usize_zero hN
    rw [runCmdK, runCmd, dite_eq_left hn, dite_eq_left hn]
    rfl
  | succ N ih =>
    intro n word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags iCur iPrev lCur lPrev dCur
      dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [runCmdK, runCmd, dite_eq_right hn, dite_eq_right hn, kstep_eq (sp := sp) (ss := ss)]
    dsimp only
    generalize stepCmd H k a stop hs (mkCmd word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount
      flags iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left sp
      ss) pos = r
    obtain ⟨w, c, rg, wp, pe, cp, wr, q1, q2, rm, ic, lc, dc, fl,
      ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩, tg, lf, ps, st⟩ := r
    unfold kcase
    cases st
    · simp only [↓reduceIte]
      apply ih
      rw [usize_pred hn]
      omega
    all_goals rfl

/-- The compiler runs the loop on the fields in place of `runCmd`. -/
@[csimp] theorem runCmd_csimp : @runCmd = @runCmdE := by
  funext H k a stop hs n st pos
  obtain ⟨word, count, ring, wpos, pend, cap, written, p1, p2, remaining, iCount, lCount, dCount, flags,
    ⟨iCur, iPrev, lCur, lPrev, dCur, dPrev, d0, d1, d2, d3, code, ilen, clen, copyBits, copyBase, dist, wordBuf, wordPos⟩,
    tag, left, sp, ss⟩ := st
  exact (runCmdK_eq H k a stop hs _ n word count ring wpos pend cap written p1 p2 remaining iCount lCount dCount flags
    iCur iPrev lCur lPrev dCur dPrev d0 d1 d2 d3 code ilen clen copyBits copyBase dist wordBuf wordPos tag left pos sp ss
    rfl).symm

end Brotli.Decoder
