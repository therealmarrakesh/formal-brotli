import Brotli.Decoder.Loop

/-!
# What the compiled command loop carries

`KInv` is what the compiled loop (`LoopK.lean`) knows of its fields at every step, so that it tests none of it at run
time: the window's size and the write position in it, how much of the window is written, the bit buffer well formed,
the position within the chunk, the block types within their counts, what the next step needs of the element's fields
(`TagInv`: the copy length's extra bits, the copy's distance, the word's position in its buffer), and that the header's
tables match some spec header. `runCmd` is called only from a state the stream's relation holds of, which gives all of it
(`KInv.of_rel`), and every step keeps it from the fields alone: the lemmas below are what the steps need.
-/

namespace Brotli.Decoder

open Brotli.Spec

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

/-- A built dictionary word is at most 38 bytes. -/
theorem dictBuild_le {clen w : UInt64} (h : dictValid clen w) : (dictBuild clen w h).size ≤ 38 := by
  have hs := dictBuild_spec (clen := clen) (wordId := w) (distance := w.toNat + 1) (maxDistance := 0) (by omega)
  rw [dite_eq_left h] at hs
  have hl := dictionaryWord_length hs
  simp only [List.length_map, Array.length_toList] at hl
  have : (dictBuild clen w h).size = (dictBuild clen w h).data.size := rfl
  omega

/-- A small fixed-width value as a position. -/
theorem toUSize_small {x : UInt64} (h : x.toNat < 2 ^ 32) : x.toUSize.toNat = x.toNat := by
  rw [UInt64.toNat_toUSize]
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rw [← USize.size_eq_two_pow]
    exact USize.le_size
  exact Nat.mod_eq_of_lt (by omega)

/-- The window's written count after more is written stays below the window less 16. -/
theorem written_usmin {k : USize} (hk : k.toNat ≤ 24) (h16 : 16 ≤ 2 ^ k.toNat) (x : USize) :
    (usmin (ringSize k - USize.ofNat 16) x).toNat + 16 ≤ 2 ^ k.toNat := by
  have h1 : (USize.ofNat 16).toNat = 16 := usize_ofNat' (by decide)
  rw [usmin_toNat, USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [h1, ringSize_toNat hk]; exact h16)), h1,
    ringSize_toNat hk]
  omega

/-- A distance that isn't 0 and reaches no further than what is written is within the window. -/
theorem copy_dist_ok {d : UInt64} {written : USize} {k : Nat} (hd : d ≠ 0) (hwd : ¬ written.toUInt64 < d)
    (hw : written.toNat + 16 ≤ 2 ^ k) : 1 ≤ d.toNat ∧ d.toNat ≤ 2 ^ k := by
  have h1 : d.toNat ≠ 0 := fun e => hd (UInt64.toNat_inj.mp (by rw [e]; rfl))
  have h2 : ¬ written.toUInt64.toNat < d.toNat := fun e => hwd (UInt64.lt_iff_toNat_lt.mpr e)
  rw [USize.toNat_toUInt64] at h2
  omega

/-- What the next step needs of the element's fields, by the tag. -/
def TagInv (k : Nat) (copyBits dist : UInt64) (wordBuf : ByteArray) (wordPos : USize) : Tag → Prop
  | .copyLength => copyBits.toNat ≤ 24
  | .copy => 1 ≤ dist.toNat ∧ dist.toNat ≤ 2 ^ k
  | .word => wordPos.toNat ≤ wordBuf.size ∧ wordBuf.size ≤ 38
  | _ => True

/-- What the compiled loop knows of its fields. -/
structure KInv (H : Hdr) (k stop : USize) (word count : UInt64) (ring : ByteArray) (wpos written : USize)
    (iCur iPrev lCur lPrev dCur dPrev copyBits dist : UInt64) (wordBuf : ByteArray) (wordPos : USize) (tag : Tag)
    (pos : USize) : Prop where
  hdr : ∃ m, HdrRel H m
  k24 : k.toNat ≤ 24
  k16 : 16 ≤ 2 ^ k.toNat
  size : ring.size = 2 ^ k.toNat
  wpos : wpos.toNat < 2 ^ k.toNat
  written : written.toNat + 16 ≤ 2 ^ k.toNat
  wf : (BitBuffer.mk word count).Wf
  pos : pos.toNat ≤ stop.toNat
  iCur : iCur.toNat < H.nI.toNat
  iPrev : 2 ≤ H.nI.toNat → iPrev.toNat < H.nI.toNat
  lCur : lCur.toNat < H.nL.toNat
  lPrev : 2 ≤ H.nL.toNat → lPrev.toNat < H.nL.toNat
  dCur : dCur.toNat < H.nD.toNat
  dPrev : 2 ≤ H.nD.toNat → dPrev.toNat < H.nD.toNat
  tagged : TagInv k.toNat copyBits dist wordBuf wordPos tag

section
variable {H : Hdr} {k stop : USize} {word count : UInt64} {ring : ByteArray} {wpos written : USize}
  {iCur iPrev lCur lPrev dCur dPrev copyBits dist : UInt64} {wordBuf : ByteArray} {wordPos : USize} {tag : Tag}
  {pos : USize}

/-- The window passes the run loops' check. -/
theorem KInv.win (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) : winCheck k wpos ring = true :=
  winCheck_of h.k24 h.size h.wpos

/-- New bits, window, element fields and position, with the block types kept. -/
theorem KInv.set (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) {word' count' : UInt64} {ring' : ByteArray} {wpos' written' : USize} {copyBits' dist' : UInt64}
    {wordBuf' : ByteArray} {wordPos' : USize} {tag' : Tag} {pos' : USize}
    (hs : ring'.size = 2 ^ k.toNat) (hwp : wpos'.toNat < 2 ^ k.toNat) (hwr : written'.toNat + 16 ≤ 2 ^ k.toNat)
    (hw : (BitBuffer.mk word' count').Wf) (hp : pos'.toNat ≤ stop.toNat)
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop word' count' ring' wpos' written' iCur iPrev lCur lPrev dCur dPrev copyBits' dist' wordBuf' wordPos'
      tag' pos' :=
  ⟨h.hdr, h.k24, h.k16, hs, hwp, hwr, hw, hp, h.iCur, h.iPrev, h.lCur, h.lPrev, h.dCur, h.dPrev, ht⟩

/-- New bits, element fields and position. -/
theorem KInv.bits (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) {word' count' : UInt64} {copyBits' dist' : UInt64} {wordBuf' : ByteArray} {wordPos' : USize}
    {tag' : Tag} {pos' : USize} (hw : (BitBuffer.mk word' count').Wf) (hp : pos'.toNat ≤ stop.toNat)
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop word' count' ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits' dist' wordBuf' wordPos' tag'
      pos' :=
  h.set h.size h.wpos h.written hw hp ht

/-- New element fields. -/
theorem KInv.retag (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) {copyBits' dist' : UInt64} {wordBuf' : ByteArray} {wordPos' : USize} {tag' : Tag}
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits' dist' wordBuf' wordPos' tag'
      pos :=
  h.bits h.wf h.pos ht

/-- The bits refilled. -/
theorem KInv.refill (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist
    wordBuf wordPos tag pos) {a : ByteArray} (hs : stop.toNat ≤ a.size) (hp : pos.toNat ≤ stop.toNat) :
    KInv H k stop (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count ring wpos written
      iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf wordPos tag (refill word count a pos stop hs hp).pos :=
  have hr := refill_spec hs hp h.wf
  h.bits hr.1 hr.2.2.1 h.tagged

/-- Bits taken from the buffer. -/
theorem KInv.drop (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) {l : UInt64} (hl : l.toNat < 64) (hle : l ≤ count) {copyBits' dist' : UInt64}
    {wordBuf' : ByteArray} {wordPos' : USize} {tag' : Tag} (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop ((BitBuffer.mk word count).drop l).word ((BitBuffer.mk word count).drop l).count ring wpos written iCur
      iPrev lCur lPrev dCur dPrev copyBits' dist' wordBuf' wordPos' tag' pos :=
  h.bits (BitBuffer.drop_wf h.wf hl (UInt64.le_iff_toNat_le.mp hle)) h.pos ht

/-- The window written. -/
theorem KInv.wrote (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) {ring' : ByteArray} {wpos' written' : USize} {copyBits' dist' : UInt64} {wordBuf' : ByteArray}
    {wordPos' : USize} {tag' : Tag} (hs : ring'.size = 2 ^ k.toNat) (hwp : wpos'.toNat < 2 ^ k.toNat)
    (hwr : written'.toNat + 16 ≤ 2 ^ k.toNat) (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop word count ring' wpos' written' iCur iPrev lCur lPrev dCur dPrev copyBits' dist' wordBuf' wordPos' tag'
      pos :=
  h.set hs hwp hwr h.wf h.pos ht

end

/-! ### What a copy and a word need -/

/-- A copy's distance as a position: what the copy step tests, and its bounds. -/
theorem copy_dist {k : USize} {dist : UInt64} (hk : k.toNat ≤ 24) (h : 1 ≤ dist.toNat ∧ dist.toNat ≤ 2 ^ k.toNat) :
    USize.ofNat 1 ≤ dist.toUSize ∧ dist.toUSize ≤ ringSize k ∧ 1 ≤ dist.toUSize.toNat ∧
      dist.toUSize.toNat ≤ 2 ^ k.toNat := by
  have hR : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hd := toUSize_small (x := dist) (by omega)
  have h1 : (USize.ofNat 1).toNat = 1 := usize_ofNat' (by decide)
  refine ⟨USize.le_iff_toNat_le.mpr ?_, USize.le_iff_toNat_le.mpr ?_, ?_, ?_⟩
  · rw [h1, hd]
    exact h.1
  · rw [hd, ringSize_toNat hk]
    exact h.2
  · rw [hd]
    exact h.1
  · rw [hd]
    exact h.2

private theorem usize_small {n : Nat} (h : n ≤ 38) : (USize.ofNat n).toNat = n := usize_ofNat' (by omega)

/-- A word's next run fits its buffer: what the word step tests. -/
theorem word_bounds {wordBuf : ByteArray} {wordPos : USize} (h : wordPos.toNat ≤ wordBuf.size ∧ wordBuf.size ≤ 38)
    (x : USize) :
    wordPos.toNat + (usmin (wordBuf.usize - wordPos) x).toNat ≤ wordBuf.size ∧
      wordPos.toNat + (usmin (wordBuf.usize - wordPos) x).toNat ≤ 2 ^ 32 - 1 := by
  have hu : wordBuf.usize.toNat = wordBuf.size := usize_small h.2
  have hs : (wordBuf.usize - wordPos).toNat = wordBuf.size - wordPos.toNat := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [hu]; exact h.1)), hu]
  rw [usmin_toNat, hs]
  omega

/-- A word's position after its next run is still within its buffer. -/
theorem word_next {wordBuf : ByteArray} {wordPos : USize} (h : wordPos.toNat ≤ wordBuf.size ∧ wordBuf.size ≤ 38)
    (x : USize) :
    (wordPos + usmin (wordBuf.usize - wordPos) x).toNat ≤ wordBuf.size ∧ wordBuf.size ≤ 38 := by
  have hb := (word_bounds h x).1
  have hU : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rw [← USize.size_eq_two_pow]
    exact USize.le_size
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact ⟨hb, h.2⟩

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
variable {H : Hdr} {k stop : USize} {word count : UInt64} {ring : ByteArray} {wpos written : USize}
  {iCur iPrev lCur lPrev dCur dPrev copyBits dist : UInt64} {wordBuf : ByteArray} {wordPos : USize} {tag : Tag}
  {pos : USize} {copyBits' dist' : UInt64} {wordBuf' : ByteArray} {wordPos' : USize} {tag' : Tag}

/-- An insert-and-copy block switch that finishes. -/
theorem KInv.swI (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) (hn : 2 ≤ H.nI) {hT : TableFits H.arena H.baseTI.toNat} {hC : TableFits H.arena H.baseCI.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).status = .ok)
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).count ring wpos written
      (blockSwitch H.arena H.lit.arena32 H.baseTI H.baseCI hT hC H.nI iCur iPrev word count).cur iCur lCur lPrev dCur
      dPrev copyBits' dist' wordBuf' wordPos' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catI hH.ok.insertCopy hH.ok.insertCopyCount hH.nI h.wf hn' h.iCur h.iPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, h.written, e1, h.pos, e2, fun _ => h.iCur, h.lCur, h.lPrev, h.dCur,
    h.dPrev, ht⟩

/-- A literal block switch that finishes. -/
theorem KInv.swL (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) (hn : 2 ≤ H.nL) {hT : TableFits H.arena H.baseTL.toNat} {hC : TableFits H.arena H.baseCL.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).status = .ok)
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).count ring wpos written
      iCur iPrev (blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL hT hC H.nL lCur lPrev word count).cur lCur dCur
      dPrev copyBits' dist' wordBuf' wordPos' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catL hH.ok.literal hH.ok.literalCount hH.nL h.wf hn' h.lCur h.lPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, h.written, e1, h.pos, h.iCur, h.iPrev, e2, fun _ => h.lCur, h.dCur,
    h.dPrev, ht⟩

/-- A distance block switch that finishes. -/
theorem KInv.swD (h : KInv H k stop word count ring wpos written iCur iPrev lCur lPrev dCur dPrev copyBits dist wordBuf
    wordPos tag pos) (hn : 2 ≤ H.nD) {hT : TableFits H.arena H.baseTD.toNat} {hC : TableFits H.arena H.baseCD.toNat}
    (hr : (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).status = .ok)
    (ht : TagInv k.toNat copyBits' dist' wordBuf' wordPos' tag') :
    KInv H k stop (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).word
      (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).count ring wpos written
      iCur iPrev lCur lPrev (blockSwitch H.arena H.lit.arena32 H.baseTD H.baseCD hT hC H.nD dCur dPrev word count).cur
      dCur copyBits' dist' wordBuf' wordPos' tag' pos := by
  obtain ⟨m, hH⟩ := h.hdr
  have hn' := UInt64.le_iff_toNat_le.mp hn
  obtain ⟨e1, e2⟩ := switch_ok hH.catD hH.ok.distance hH.ok.distanceCount hH.nD h.wf hn' h.dCur h.dPrev hr
  exact ⟨h.hdr, h.k24, h.k16, h.size, h.wpos, h.written, e1, h.pos, h.iCur, h.iPrev, h.lCur, h.lPrev, e2,
    fun _ => h.dCur, ht⟩

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
    KInv H k stop st.word st.count st.ring st.wpos st.written st.iCur st.iPrev st.lCur st.lPrev st.dCur st.dPrev
      st.copyBits st.dist st.wordBuf st.wordPos st.tag pos := by
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
  have hwin := hC.win
  have ht : TagInv k.toNat st.copyBits st.dist st.wordBuf st.wordPos st.tag := by
    cases p with
    | literalSymbol => exact hrel.elim
    | command s => rw [hrel.2.1]; trivial
    | insertCopy s ic => rw [hrel.2.1]; trivial
    | copyLength s ic c ilen cb cbase =>
      obtain ⟨_, e0, _, _, _, e, _, h24, _⟩ := hrel
      rw [e0]
      show st.copyBits.toNat ≤ 24
      rw [e]
      exact h24
    | literals s ic c ilen clen n lit out => rw [hrel.2.1]; trivial
    | distance s c clen => rw [hrel.2.1]; trivial
    | distanceSymbol s clen dist => rw [hrel.2.1]; trivial
    | copy s d n =>
      obtain ⟨_, e0, _, e, _, h1, h2, _⟩ := hrel
      rw [e0]
      show 1 ≤ st.dist.toNat ∧ st.dist.toNat ≤ 2 ^ k.toNat
      rw [e]
      omega
    | word s pending =>
      obtain ⟨_, e0, _, _, h38, hle⟩ := hrel
      rw [e0]
      exact ⟨hle, h38⟩
  have hk16 : 16 ≤ 2 ^ k.toNat := by omega
  have hwr : st.written.toNat + 16 ≤ 2 ^ k.toNat := by
    have := hC.written
    omega
  obtain ⟨iw1, iw2, _⟩ := hC.iRel.wf
  obtain ⟨lw1, lw2, _⟩ := hC.lRel.wf
  obtain ⟨dw1, dw2, _⟩ := hC.dRel.wf
  refine ⟨⟨m, hH⟩, hC.k24, hk16, hC.ring.size, hC.ring.pos_lt, hwr, hC.wf, hp, ?_, ?_, ?_, ?_, ?_, ?_, ht⟩
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
