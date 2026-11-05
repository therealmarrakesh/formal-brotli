import Brotli.Decoder.Loop

/-!
# What the compiled command loop carries

`KInv` is what the compiled loop (`LoopK.lean`) knows of its fields at every step, so that it tests none of it at run
time: the window's size and the write position in it, the bit buffer well formed, the position within the chunk, the
block types within their counts, the copy length's extra bits when that is next, and that the header's tables match
some spec header. `runCmd` is called only from a state the stream's relation holds of, which gives all of it
(`KInv.of_rel`), and every step keeps it from the fields alone: the lemmas below are what the steps need.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The tags that aren't the copy length's -/

theorem Tag.command_ne : Tag.command ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.insertCopy_ne : Tag.insertCopy ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.literals_ne : Tag.literals ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.distance_ne : Tag.distance ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.distanceSymbol_ne : Tag.distanceSymbol ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.copy_ne : Tag.copy ≠ .copyLength := fun e => Tag.noConfusion e
theorem Tag.word_ne : Tag.word ≠ .copyLength := fun e => Tag.noConfusion e

/-- A tag that isn't the copy length's asks nothing of the extra bits. -/
theorem noCL {t : Tag} (ht : t ≠ .copyLength) {cb : UInt64} : t = .copyLength → cb.toNat ≤ 24 :=
  fun e => absurd e ht

/-- An insert-and-copy code's insert extra bits are few. -/
theorem insertRow_bits {c : UInt64} (hc : c.toNat < 704) : (rowBits (insertRow c hc)).toNat < 64 := by
  have h1 := (insertRow_fields hc).1
  have h2 := (cmdRow_small hc).1
  omega

/-- An insert-and-copy code's copy extra bits are at most 24. -/
theorem copyRow_bits {c : UInt64} (hc : c.toNat < 704) : (rowBits (copyRow c hc)).toNat ≤ 24 := by
  have h1 := (copyRow_fields hc).1
  have h2 := (cmdRow_small hc).2.2.1
  omega

/-- What the compiled loop knows of its fields. -/
structure KInv (H : Hdr) (k stop : USize) (word count : UInt64) (ring : ByteArray) (wpos : USize)
    (iCur iPrev lCur lPrev dCur dPrev copyBits : UInt64) (tag : Tag) (pos : USize) : Prop where
  hdr : ∃ m, HdrRel H m
  k24 : k.toNat ≤ 24
  k16 : 16 ≤ 2 ^ k.toNat
  size : ring.size = 2 ^ k.toNat
  wpos : wpos.toNat < 2 ^ k.toNat
  wf : (BitBuffer.mk word count).Wf
  pos : pos.toNat ≤ stop.toNat
  iCur : iCur.toNat < H.nI.toNat
  iPrev : 2 ≤ H.nI.toNat → iPrev.toNat < H.nI.toNat
  lCur : lCur.toNat < H.nL.toNat
  lPrev : 2 ≤ H.nL.toNat → lPrev.toNat < H.nL.toNat
  dCur : dCur.toNat < H.nD.toNat
  dPrev : 2 ≤ H.nD.toNat → dPrev.toNat < H.nD.toNat
  copyBits : tag = .copyLength → copyBits.toNat ≤ 24

section
variable {H : Hdr} {k stop : USize} {word count : UInt64} {ring : ByteArray} {wpos : USize}
  {iCur iPrev lCur lPrev dCur dPrev copyBits : UInt64} {tag : Tag} {pos : USize}

/-- The window passes the run loops' check. -/
theorem KInv.win (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos) :
    winCheck k wpos ring = true :=
  winCheck_of h.k24 h.size h.wpos

/-- New bits, window, element fields and position, with the block types kept. -/
theorem KInv.set (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {word' count' : UInt64} {ring' : ByteArray} {wpos' : USize} {copyBits' : UInt64} {tag' : Tag} {pos' : USize}
    (hs : ring'.size = 2 ^ k.toNat) (hwp : wpos'.toNat < 2 ^ k.toNat) (hw : (BitBuffer.mk word' count').Wf)
    (hp : pos'.toNat ≤ stop.toNat) (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop word' count' ring' wpos' iCur iPrev lCur lPrev dCur dPrev copyBits' tag' pos' :=
  ⟨h.hdr, h.k24, h.k16, hs, hwp, hw, hp, h.iCur, h.iPrev, h.lCur, h.lPrev, h.dCur, h.dPrev, hc⟩

/-- New bits, element fields and position. -/
theorem KInv.bits (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {word' count' : UInt64} {copyBits' : UInt64} {tag' : Tag} {pos' : USize} (hw : (BitBuffer.mk word' count').Wf)
    (hp : pos'.toNat ≤ stop.toNat) (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop word' count' ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits' tag' pos' :=
  h.set h.size h.wpos hw hp hc

/-- A new tag that isn't the copy length's. -/
theorem KInv.retag (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {copyBits' : UInt64} {tag' : Tag} (ht : tag' ≠ .copyLength) :
    KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits' tag' pos :=
  h.bits h.wf h.pos (fun e => absurd e ht)

/-- The bits refilled. -/
theorem KInv.refill (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {a : ByteArray} (hs : stop.toNat ≤ a.size) (hp : pos.toNat ≤ stop.toNat) :
    KInv H k stop (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count ring wpos iCur
      iPrev lCur lPrev dCur dPrev copyBits tag (refill word count a pos stop hs hp).pos :=
  have hr := refill_spec hs hp h.wf
  h.bits hr.1 hr.2.2.1 h.copyBits

/-- Bits taken from the buffer. -/
theorem KInv.drop (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {l : UInt64} (hl : l.toNat < 64) (hle : l ≤ count) {copyBits' : UInt64} {tag' : Tag}
    (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop ((BitBuffer.mk word count).drop l).word ((BitBuffer.mk word count).drop l).count ring wpos iCur iPrev
      lCur lPrev dCur dPrev copyBits' tag' pos :=
  h.bits (BitBuffer.drop_wf h.wf hl (UInt64.le_iff_toNat_le.mp hle)) h.pos hc

/-- The window written. -/
theorem KInv.wrote (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    {ring' : ByteArray} {wpos' : USize} {tag' : Tag} (hs : ring'.size = 2 ^ k.toNat)
    (hwp : wpos'.toNat < 2 ^ k.toNat) (ht : tag' ≠ .copyLength) :
    KInv H k stop word count ring' wpos' iCur iPrev lCur lPrev dCur dPrev copyBits tag' pos :=
  h.set hs hwp h.wf h.pos (fun e => absurd e ht)

end

/-! ### Block switches -/

/-- A block switch that finishes leaves the bits well formed and the new type within the count. -/
theorem switch_ok {arena : ByteArray} {h32 : arena.size < 2 ^ 32} {tBase cBase : USize}
    {hT : TableFits arena tBase.toNat} {hC : TableFits arena cBase.toNat} {c : BlockCategory} {n cur prev word count : UInt64}
    (hrel : CatRel arena tBase cBase c) (hwf : c.Wf) (hcnt : 2 ≤ c.n → c.countCode.Symbols blockCountAlphabetSize)
    (hnn : n.toNat = c.n) (hw : (BitBuffer.mk word count).Wf) (hn2 : 2 ≤ n.toNat) (hcur : cur.toNat < n.toNat)
    (hprev : 2 ≤ n.toNat → prev.toNat < n.toNat)
    (hr : (blockSwitch arena h32 tBase cBase hT hC n cur prev word count).status = .ok) :
    (BitBuffer.mk (blockSwitch arena h32 tBase cBase hT hC n cur prev word count).word
        (blockSwitch arena h32 tBase cBase hT hC n cur prev word count).count).Wf ∧
      (blockSwitch arena h32 tBase cBase hT hC n cur prev word count).cur.toNat < n.toNat := by
  have h2 : 2 ≤ c.n := by omega
  obtain ⟨okT, cT, sT⟩ := hrel.type h2
  obtain ⟨okC, cC, _⟩ := hrel.count h2
  have hspec := blockSwitch_spec (h32 := h32) (hT := hT) (hC := hC) (cur := cur) (prev := prev) (word := word)
    (count := count) hnn okT okC cT cC hw h2 (by have := hwf.2.1; omega) sT (hcnt h2) (by omega) (by have := hprev hn2; omega)
    []
  obtain ⟨e1, e2, _⟩ := hspec.1 hr
  exact ⟨e1, by omega⟩

section
variable {H : Hdr} {k stop : USize} {word count : UInt64} {ring : ByteArray} {wpos : USize}
  {iCur iPrev lCur lPrev dCur dPrev copyBits : UInt64} {tag : Tag} {pos : USize}

/-- An insert-and-copy block switch that finishes. -/
theorem KInv.swI (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    (hn : 2 ≤ H.nI) {hT : TableFits H.arena H.baseTI.toNat} {hC : TableFits H.arena H.baseCI.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).status = .ok)
    {copyBits' : UInt64} {tag' : Tag} (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).count ring wpos
      (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).cur iCur lCur lPrev dCur
      dPrev copyBits' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catI hH.ok.insertCopy hH.ok.insertCopyCount hH.nI h.wf hn' h.iCur h.iPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, e1, h.pos, e2, fun _ => h.iCur, h.lCur, h.lPrev, h.dCur, h.dPrev, hc⟩

/-- A literal block switch that finishes. -/
theorem KInv.swL (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    (hn : 2 ≤ H.nL) {hT : TableFits H.arena H.baseTL.toNat} {hC : TableFits H.arena H.baseCL.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).status = .ok)
    {copyBits' : UInt64} {tag' : Tag} (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).count ring wpos iCur iPrev
      (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).cur lCur dCur dPrev
      copyBits' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catL hH.ok.literal hH.ok.literalCount hH.nL h.wf hn' h.lCur h.lPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, e1, h.pos, h.iCur, h.iPrev, e2, fun _ => h.lCur, h.dCur, h.dPrev, hc⟩

/-- A distance block switch that finishes. -/
theorem KInv.swD (h : KInv H k stop word count ring wpos iCur iPrev lCur lPrev dCur dPrev copyBits tag pos)
    (hn : 2 ≤ H.nD) {hT : TableFits H.arena H.baseTD.toNat} {hC : TableFits H.arena H.baseCD.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).status = .ok)
    {copyBits' : UInt64} {tag' : Tag} (hc : tag' = .copyLength → copyBits'.toNat ≤ 24) :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).count ring wpos iCur iPrev
      lCur lPrev (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).cur dCur
      copyBits' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catD hH.ok.distance hH.ok.distanceCount hH.nD h.wf hn' h.dCur h.dPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, e1, h.pos, h.iCur, h.iPrev, h.lCur, h.lPrev, e2, fun _ => h.dCur, hc⟩

end

/-! ### The runs keep the window and the bits -/

/-- What a literal run leaves: the window's size, the write position in it, the bits well formed and the position
within the chunk. -/
def LitInv (k : Nat) (stop : USize) (r : LitRun) : Prop :=
  r.ring.size = 2 ^ k ∧ r.wpos.toNat < 2 ^ k ∧ (BitBuffer.mk r.word r.count).Wf ∧ r.pos.toNat ≤ stop.toNat

theorem literalRun_inv' {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      LitInv k stop (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp
        hw hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    rw [literalRun, dite_eq_left (usize_zero hN)]
    exact ⟨hsize, hwp, hw, hp⟩
  | succ N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [literalRun, dite_eq_right hn]
    dsimp only
    split
    · apply ih
      rw [usize_pred hn]
      omega
    · have hr := refill_spec hs hp hw
      exact ⟨hsize, hwp, hr.1, hr.2.2.1⟩

theorem literalRun_inv {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64) (pos wpos : USize)
    (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    LitInv k stop (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw
      hsize hwp) :=
  literalRun_inv' C a stop hs mapBase modeOff mask k hmb hm hd hmask hk _ n word count pos wpos ring p1 p2 hp hw hsize
    hwp rfl

/-- What a copy or word run leaves: the window's size and the write position in it. -/
def RingInv (k : Nat) (r : CopyRun) : Prop := r.ring.size = 2 ^ k ∧ r.wpos.toNat < 2 ^ k

theorem copyRun_inv' {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      RingInv k (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n ring wpos p1 p2 hsize hwp hN
    rw [copyRun, dite_eq_left (usize_zero hN)]
    exact ⟨hsize, hwp⟩
  | succ N ih =>
    intro n ring wpos p1 p2 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyRun, dite_eq_right hn]
    apply ih
    rw [usize_pred hn]
    omega

theorem copyRun_inv {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (n : USize) (ring : ByteArray) (wpos : USize)
    (p1 p2 : UInt8) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    RingInv k (copyRun d mask size k hk hmask hsz hd1 hd2 n ring wpos p1 p2 hsize hwp) :=
  copyRun_inv' hk hmask hsz hd1 hd2 _ n ring wpos p1 p2 hsize hwp rfl

theorem wordRun_inv' {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
      (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k), n.toNat = N →
      RingInv k (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    rw [wordRun, dite_eq_left (usize_zero hN)]
    exact ⟨hsize, hwp⟩
  | succ N ih =>
    intro n idx ring wpos p1 p2 hb hb32 hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [wordRun, dite_eq_right hn]
    apply ih
    rw [usize_pred hn]
    omega

theorem wordRun_inv {buf : ByteArray} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (n idx : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8) (hb : idx.toNat + n.toNat ≤ buf.size)
    (hb32 : idx.toNat + n.toNat ≤ 2 ^ 32 - 1) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    RingInv k (wordRun buf mask k hk hmask n idx ring wpos p1 p2 hb hb32 hsize hwp) :=
  wordRun_inv' hk hmask _ n idx ring wpos p1 p2 hb hb32 hsize hwp rfl

/-! ### Where the loop starts -/

/-- The stream's relation for a meta-block's commands gives what the compiled loop carries. -/
theorem KInv.of_rel {w : Nat} {m : MetaBlockHeader} {H : Hdr} {k stop pos : USize} {st : Cmd} {p : Phase}
    (hH : HdrRel H m) (hrel : Rel w k.toNat m st p) (hp : pos.toNat ≤ stop.toNat) :
    KInv H k stop st.word st.count st.ring st.wpos st.iCur st.iPrev st.lCur st.lPrev st.dCur st.dPrev st.copyBits
      st.tag pos := by
  have core : ∃ out rem ds ic lit dist, Core w k.toNat m st out rem ds ic lit dist := by
    cases p with
    | literalSymbol => exact hrel.elim
    | command s => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | insertCopy s ic => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | copyLength s ic c ilen cb cbase => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | literals s ic c ilen clen n lit out => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | distance s c clen => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | distanceSymbol s clen dist => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | copy s d n => exact ⟨_, _, _, _, _, _, hrel.1⟩
    | word s pending => exact ⟨_, _, _, _, _, _, hrel.1⟩
  obtain ⟨out, rem, ds, ic, lit, dist, hC⟩ := core
  have hcb : st.tag = .copyLength → st.copyBits.toNat ≤ 24 := by
    intro ht
    cases p with
    | copyLength s ic c ilen cb cbase =>
      obtain ⟨_, _, _, _, _, e, _, h24, _⟩ := hrel
      rw [e]
      exact h24
    | literalSymbol => exact hrel.elim
    | command s => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | insertCopy s ic => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | literals s ic c ilen clen n lit out => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | distance s c clen => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | distanceSymbol s clen dist => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | copy s d n => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
    | word s pending => exact absurd (hrel.2.1.symm.trans ht) (fun e => Tag.noConfusion e)
  have hk16 : 16 ≤ 2 ^ k.toNat := by have := hC.win; omega
  obtain ⟨iw1, iw2, _⟩ := hC.iRel.wf
  obtain ⟨lw1, lw2, _⟩ := hC.lRel.wf
  obtain ⟨dw1, dw2, _⟩ := hC.dRel.wf
  refine ⟨⟨m, hH⟩, hC.k24, hk16, hC.ring.size, hC.ring.pos_lt, hC.wf, hp, ?_, ?_, ?_, ?_, ?_, ?_, hcb⟩
  · rw [hH.nI, ← hC.iRel.cur]
    exact iw2
  · rw [hH.nI, ← hC.iRel.prev]
    exact iw1
  · rw [hH.nL, ← hC.lRel.cur]
    exact lw2
  · rw [hH.nL, ← hC.lRel.prev]
    exact lw1
  · rw [hH.nD, ← hC.dRel.cur]
    exact dw2
  · rw [hH.nD, ← hC.dRel.prev]
    exact dw1

end Brotli.Decoder
