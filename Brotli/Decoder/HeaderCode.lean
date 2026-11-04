import Brotli.Decoder.HeaderBuild

/-!
# A prefix code's first bits

The place at a prefix code's first two bits, a simple prefix code, and the code lengths of the code length alphabet.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Code lengths in an array -/

/-- An array holds the code lengths `lengthsOf` gives. -/
structure LensIs (t : ByteArray) (size : Nat) (P : List (Nat × Nat)) : Prop where
  sz : t.size = size
  at_ : ∀ i, i < size → (t.data[i]?.getD 0).toNat = ((P.find? (·.1 == i)).map (·.2)).getD 0

theorem LensIs.eq {t : ByteArray} {size : Nat} {P : List (Nat × Nat)} (h : LensIs t size P) : lensOf t size = lengthsOf size P := by
  have hl : (lensOf t size).length = size := length_lensOf (by rw [h.sz]; exact Nat.le_refl _)
  have hl' : (lengthsOf size P).length = size := by simp [lengthsOf]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < size
  · rw [lensOf_get hi (by rw [h.sz]; exact Nat.le_refl _), h.at_ i hi]
    simp [lengthsOf, hi]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem LensIs.zero {size : Nat} (h : size < 2 ^ 32) : LensIs (zeroBytes size) size [] :=
  ⟨zeroBytes_size h, fun i _ => by rw [zeroBytes_get h]; rfl⟩

/-- A length set in front of the others wins. -/
theorem LensIs.set {t : ByteArray} {size : Nat} {P : List (Nat × Nat)} (h : LensIs t size P) (s l : UInt64) (hs : s.toNat < 2 ^ 32)
    (hl : l.toNat < 256) : LensIs (setU t s.toUSize l.toUInt8) size ((s.toNat, l.toNat) :: P) := by
  have hus : s.toUSize.toNat = s.toNat := word_toUSize hs
  refine ⟨by rw [size_setU]; exact h.sz, fun i hi => ?_⟩
  by_cases he : i = s.toNat
  · subst he
    have := setU_get_same (t := t) (i := s.toUSize) (v := l.toUInt8) (by rw [hus, h.sz]; exact hi)
    rw [hus] at this
    rw [this, UInt64.toNat_toUInt8]
    simp
    omega
  · rw [setU_get_ne (by rw [hus]; exact he), h.at_ i hi]
    simp [Ne.symm he]

/-- A length added at the back of pairs that don't have its symbol. -/
theorem LensIs.push {t : ByteArray} {size : Nat} {P : List (Nat × Nat)} (h : LensIs t size P) (s l : UInt64) (hs : s.toNat < size)
    (h32 : size < 2 ^ 32) (hl : l.toNat < 256) (hnew : ∀ p ∈ P, p.1 ≠ s.toNat) :
    LensIs (setU t s.toUSize l.toUInt8) size (P ++ [(s.toNat, l.toNat)]) := by
  have hus : s.toUSize.toNat = s.toNat := word_toUSize (by omega)
  refine ⟨by rw [size_setU]; exact h.sz, fun i hi => ?_⟩
  by_cases he : i = s.toNat
  · subst he
    have := setU_get_same (t := t) (i := s.toUSize) (v := l.toUInt8) (by rw [hus, h.sz]; exact hi)
    rw [hus] at this
    rw [this, UInt64.toNat_toUInt8]
    have hf : P.find? (·.1 == s.toNat) = none := by
      rw [List.find?_eq_none]
      intro p hp
      simpa using hnew p hp
    rw [List.find?_append, hf]
    simp
    omega
  · rw [setU_get_ne (by rw [hus]; exact he), h.at_ i hi, List.find?_append]
    have hf : ([(s.toNat, l.toNat)] : List (Nat × Nat)).find? (·.1 == i) = none := by
      simp [Ne.symm he]
    rw [hf]
    cases P.find? (·.1 == i) <;> rfl

/-- A zero length added at the back, whose byte is zero already. -/
theorem LensIs.pushZero {t : ByteArray} {size : Nat} {P : List (Nat × Nat)} (h : LensIs t size P) (s : Nat) :
    LensIs t size (P ++ [(s, 0)]) := by
  refine ⟨h.sz, fun i hi => ?_⟩
  rw [h.at_ i hi, List.find?_append]
  cases hf : P.find? (·.1 == i) with
  | some p => rfl
  | none =>
    by_cases he : s = i
    · subst he
      simp
    · simp [he]

/-! ### Writing a simple code's lengths -/

/-- Sets one code length. -/
@[inline] def setLen (t : ByteArray) (s l : UInt64) : ByteArray := setU t s.toUSize l.toUInt8

/-- A simple code's lengths, in an array of zeros. -/
def writeSimple (t : ByteArray) (r : Rd) : ByteArray :=
  if r.e = 1 then setLen (setLen t r.b 1) r.a 1
  else if r.e = 2 then setLen (setLen (setLen t r.c 2) r.b 2) r.a 1
  else if r.e = 3 then setLen (setLen (setLen (setLen t r.d 2) r.c 2) r.b 2) r.a 2
  else setLen (setLen (setLen (setLen t r.d 3) r.c 3) r.b 2) r.a 1

private theorem writeSimple_lens {size : Nat} (hs : size < 2 ^ 32) (r : Rd) (he : r.e.toNat ≠ 0) (h1 : r.a.toNat < 2 ^ 32)
    (h2 : r.b.toNat < 2 ^ 32) (h3 : r.c.toNat < 2 ^ 32) (h4 : r.d.toNat < 2 ^ 32) :
    simpleCode size r.a.toNat r.b.toNat r.c.toNat r.d.toNat r.e.toNat = .canonical (lensOf (writeSimple (zeroBytes size) r) size) := by
  have z := LensIs.zero hs
  unfold simpleCode writeSimple
  rw [ite_eq_right he]
  by_cases e1 : r.e = 1
  · have e1' : r.e.toNat = 1 := by rw [e1]; rfl
    rw [ite_eq_left e1', ite_eq_left e1]
    exact congrArg _ ((z.set r.b 1 h2 (by decide)).set r.a 1 h1 (by decide)).eq.symm
  have e1' : ¬ r.e.toNat = 1 := fun h => e1 (UInt64.toNat_inj.mp h)
  rw [ite_eq_right e1', ite_eq_right e1]
  by_cases e2 : r.e = 2
  · have e2' : r.e.toNat = 2 := by rw [e2]; rfl
    rw [ite_eq_left e2', ite_eq_left e2]
    exact congrArg _ (((z.set r.c 2 h3 (by decide)).set r.b 2 h2 (by decide)).set r.a 1 h1 (by decide)).eq.symm
  have e2' : ¬ r.e.toNat = 2 := fun h => e2 (UInt64.toNat_inj.mp h)
  rw [ite_eq_right e2', ite_eq_right e2]
  by_cases e3 : r.e = 3
  · have e3' : r.e.toNat = 3 := by rw [e3]; rfl
    rw [ite_eq_left e3', ite_eq_left e3]
    exact congrArg _ (((((z.set r.d 2 h4 (by decide)).set r.c 2 h3 (by decide))).set r.b 2 h2 (by decide)).set r.a 2 h1 (by decide)).eq.symm
  have e3' : ¬ r.e.toNat = 3 := fun h => e3 (UInt64.toNat_inj.mp h)
  rw [ite_eq_right e3', ite_eq_right e3]
  exact congrArg _ (((((z.set r.d 3 h4 (by decide)).set r.c 3 h3 (by decide))).set r.b 2 h2 (by decide)).set r.a 1 h1 (by decide)).eq.symm

theorem writeSimple_size (t : ByteArray) (r : Rd) : (writeSimple t r).size = t.size := by
  unfold writeSimple setLen
  split
  · rw [size_setU, size_setU]
  · split
    · rw [size_setU, size_setU, size_setU]
    · split
      · rw [size_setU, size_setU, size_setU, size_setU]
      · rw [size_setU, size_setU, size_setU, size_setU]

/-- A simple code that reads: what it leaves holds the rest of the bits, the code is the spec's reading, and its values are
small. -/
theorem simple_wit {st : Hd} (hw : (BitBuffer.mk st.word st.count).Wf) (hs : st.size.toNat ≤ 704) (h2 : 2 ≤ st.count)
    (h1 : (BitBuffer.mk st.word st.count).peek 2 = 1)
    (hok : (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).status = .ok) :
    (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).buf.Wf ∧
    readPrefixCode st.size.toNat (BitBuffer.mk st.word st.count).held =
      some (simpleValue st.size (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)),
        (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).buf.held) ∧
    SmallVals (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)) := by
  have hread := read_int (b := ⟨st.word, st.count⟩) (k := 2) [] (by decide) h2
  have hw1 := drop_wf' hw (k := 2) (by decide) h2
  rw [h1] at hread
  generalize (BitBuffer.mk st.word st.count).drop 2 = b1 at hread hw1 hok ⊢
  obtain ⟨hbits, hbitsLe⟩ := alphabetBitsFast_toNat (size := st.size) (by omega)
  have R := simpleFast_ok (size := st.size) (bits := alphabetBitsFast st.size) hw1 hbitsLe
  rw [hbits] at R
  have hsmall := simpleFast_small st.size (alphabetBitsFast st.size) b1 hbitsLe
  have hR := R.ok hok
  generalize simpleFast st.size (alphabetBitsFast st.size) b1 = r at hR hok hsmall ⊢
  have hN2 := hR.2 []
  simp only [List.append_nil] at hN2 hread
  have e2 : (2 : UInt64).toNat = 2 := rfl
  have e1 : (1 : UInt64).toNat = 1 := rfl
  rw [e2, e1] at hread
  refine ⟨hR.1, ?_, hsmall⟩
  unfold readPrefixCode
  rw [hread]
  show (if 1 = 1 then readSimple st.size.toNat b1.held else readComplex st.size.toNat 1 b1.held) = _
  rw [ite_eq_left rfl, simpleChain_eq]
  exact hN2

/-- A simple code with two symbols or more has complete lengths, as they are written into the state's array. -/
theorem simple_complete {st : Hd} (hw : (BitBuffer.mk st.word st.count).Wf) (hs : st.size.toNat ≤ 704) (h2 : 2 ≤ st.count)
    (h1 : (BitBuffer.mk st.word st.count).peek 2 = 1)
    (hok : (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).status = .ok)
    (he : (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).e.toNat ≠ 0) :
    Complete (.canonical (lensOf (writeSimple (zeroBytes st.size.toNat)
      (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2))) st.size.toNat)) := by
  obtain ⟨-, hwit, hsmall⟩ := simple_wit hw hs h2 h1 hok
  generalize simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) = r at hwit hsmall he ⊢
  have hC := readPrefixCode_complete hwit
  have hl := writeSimple_lens (size := st.size.toNat) (by omega) r he hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2
  unfold simpleValue at hC
  rwa [hl] at hC

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

/-- A finished table is a step, given that what the state stands for before it is the code's owner. -/
theorem TableDone.toStep {g : Gh} {o : Owner} {c : PrefixCode} {p : HPhase} {st st0 r : Hd} {pos : USize}
    (h : TableDone K g o c st0 r) (h2 : st0.pos = pos) (hp : pos.toNat ≤ stop.toNat) (hd : st0.d = st.d) (hsz : HSize st → HSize st0)
    (heq : ∀ F, hrest K g p (availBits st.word st.count a pos stop F) = ownerK K g o c (availBits st0.word st0.count a pos stop F))
    (hj : ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) = .next (g, ownerPlace g o c) (availBits st0.word st0.count a pos stop F))
    (hrank : (rankH p).1 = rankO o := by rfl) (hcap : budH g p = budO g o := by rfl) (hs0 : st0.status = .next := by rfl) :
    HStepOk K a stop g p st pos r := by
  obtain ⟨⟨b1, b2, b3⟩, hnext, hst⟩ := h
  have hne : ∀ s : HStatus, s ≠ .next → r.status = s → False := fun s h1 e => h1 (e.symm.trans (hst.trans hs0))
  refine ⟨fun e => ?_, fun e => ?_, fun e F => ?_, fun e => ?_, fun e => ?_⟩
  · obtain ⟨g', p', oc, h4, h5, h6, h7, h8⟩ := hnext e
    have hmv := h7 p hcap
    refine ⟨g', p', oc, h4, by rw [b3, h2]; exact Nat.le_refl _, by rw [b3, h2]; exact hp, (fun F => ?_), Or.inl (by rw [hrank]; exact h6),
      ⟨by rw [hmv.max, hd], by rw [hmv.grow, hd], fun hs => hmv.size (hsz hs), hmv.cap.same hd⟩, fun F => ?_⟩
    · rw [heq F, avail_mk, h5, avail_mk, b1, b2, b3, h2]
    · rw [h8, hj F, avail_mk, avail_mk, b1, b2, b3, h2]
  · exact (hne _ (fun e => HStatus.noConfusion e) e).elim
  · exact (hne _ (fun e => HStatus.noConfusion e) e).elim
  · exact (hne _ (fun e => HStatus.noConfusion e) e).elim
  · exact (hne _ (fun e => HStatus.noConfusion e) e).elim

/-- What a simple code's table leaves, once the code is read. -/
theorem simple_done {o : Owner} {size : Nat} {st : Hd} {g : Gh} (pos : USize) {r : Rd} (hrel : HRel st g (.code o size))
    (hw2 : r.buf.Wf) (hwit : readPrefixCode st.size.toNat (BitBuffer.mk st.word st.count).held = some (simpleValue st.size r, r.buf.held))
    (hsmall : SmallVals r) (hb : st.d.arena.size + budO g o ≤ st.d.arenaCap.toNat)
    {ha : TableArgs st.size (writeSimple (zeroBytes st.size.toNat) r) (r.e == 0) r.a} {hi : InstallOk st.role st.idx st.fill} :
    TableDone K g o (simpleValue st.size r) { st with
        word := r.word, count := r.count, pos := pos, status := .next, lens := writeSimple (zeroBytes st.size.toNat) r }
      (tableDone { st with
        word := r.word, count := r.count, pos := pos, status := .next, lens := writeSimple (zeroBytes st.size.toNat) r }
        (r.e == 0) r.a ha hi) := by
  obtain ⟨_, hu, _, hs, ho⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hCc := readPrefixCode_complete hwit
  have hsy := readPrefixCode_symbols hwit
  rw [hs1] at hsy
  have hsn : st.size.toNat < 2 ^ 32 := by omega
  have hlensEq : (writeSimple (zeroBytes st.size.toNat) r).size = size := by
    rw [writeSimple_size, zeroBytes_size hsn, hs1]
  have hsg : (r.e == 0) = true → simpleValue st.size r = .single r.a.toNat := by
    intro he
    have he' : r.e = 0 := by simpa using he
    unfold simpleValue simpleCode
    rw [he']
    rfl
  have hcn : (r.e == 0) = false → simpleValue st.size r = .canonical (lensOf (writeSimple (zeroBytes st.size.toNat) r) size) := by
    intro he
    have he' : r.e.toNat ≠ 0 := fun e => by
      have : r.e = 0 := UInt64.toNat_inj.mp e
      simp [this] at he
    have := writeSimple_lens (size := st.size.toNat) hsn r he' hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2
    rw [hs1] at this
    unfold simpleValue
    rw [hs1, this]
  apply tableDone_ok K (size := size)
  · exact hw2
  · exact hu
  · exact ⟨hs1, hs2, hs3⟩
  · exact ho
  · exact hsg
  · exact hcn
  · exact hlensEq
  · exact hCc
  · exact hsy
  · exact hb

/-! ### The place at a prefix code's first bits -/

/-- A state at a prefix code's first bits stands for a place there. -/
theorem code_ex {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .code) : ∃ g o size, HRel st g (.code o size) := by
  obtain ⟨g, p, hr⟩ := h
  cases p with
  | code o size => exact ⟨g, o, size, hr⟩
  | np => exact absurd (hr.2.2.symm.trans ht) (fun e => HTag.noConfusion e)
  | _ => exact absurd (hr.2.2.1.symm.trans ht) (fun e => HTag.noConfusion e)

/-- A state at a prefix code's first bits has what `installTable` needs. -/
theorem code_install {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .code) : InstallOk st.role st.idx st.fill := by
  obtain ⟨g, o, size, hrel⟩ := code_ex h ht
  exact hrel.2.2.2.2.install

private theorem readInt_one (bs : List Bool) : readInt 2 (true :: false :: bs) = some (1, bs) := by
  simp [readInt]

/-- A simple code read after the first two bits is a code that was read. -/
theorem simple_args {st : Hd} (h : ∃ g p, HRel st g p) (ht : st.tag = .code) (h2 : 2 ≤ st.count)
    (hok : (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).status = .ok) :
    TableArgs st.size (writeSimple (zeroBytes st.size.toNat) (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)))
      ((simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).e == 0)
      (simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2)).a := by
  obtain ⟨g, o, size, hrel⟩ := code_ex h ht
  obtain ⟨hw, _, _, hs, _⟩ := hrel
  obtain ⟨hs1, _, hs3⟩ := hs
  have hw1 := drop_wf' hw (k := 2) (by decide) h2
  obtain ⟨hbits, hbitsLe⟩ := alphabetBitsFast_toNat (size := st.size) (by omega)
  have R := simpleFast_ok (size := st.size) (bits := alphabetBitsFast st.size) hw1 hbitsLe
  rw [hbits, hs1] at R
  have hsmall := simpleFast_small st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) hbitsLe
  generalize simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) = r at R hsmall hok ⊢
  have hN2 := (R.ok hok).2 []
  simp only [List.append_nil] at hN2
  have hwit : readPrefixCode st.size.toNat (true :: false :: ((BitBuffer.mk st.word st.count).drop 2).held) =
      some (simpleValue st.size r, r.buf.held) := by
    unfold readPrefixCode
    rw [readInt_one]
    show (if 1 = 1 then readSimple st.size.toNat ((BitBuffer.mk st.word st.count).drop 2).held
      else readComplex st.size.toNat 1 ((BitBuffer.mk st.word st.count).drop 2).held) = _
    rw [ite_eq_left rfl, simpleChain_eq, hs1]
    exact hN2
  have hCc := readPrefixCode_complete hwit
  have hsy := readPrefixCode_symbols hwit
  rw [hs1] at hsy
  have hsn : st.size.toNat < 2 ^ 32 := by omega
  have hlensEq : (writeSimple (zeroBytes st.size.toNat) r).size = size := by
    rw [writeSimple_size, zeroBytes_size hsn, hs1]
  refine ⟨simpleValue st.size r, size, hs1, hs3, fun he => ?_, fun he => ?_, hlensEq, hCc, hsy⟩
  · have he' : r.e = 0 := by simpa using he
    unfold simpleValue simpleCode
    rw [he']
    rfl
  · have he' : r.e.toNat ≠ 0 := fun e => by
      have : r.e = 0 := UInt64.toNat_inj.mp e
      simp [this] at he
    have := writeSimple_lens (size := st.size.toNat) hsn r he' hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2
    rw [hs1] at this
    unfold simpleValue
    rw [hs1, this]

/-- A simple code's read, with what a successful one gives. -/
@[inline] def simpleFastT (st : Hd) (h : ∃ g p, HRel st g p) (ht : st.tag = .code) (h2 : 2 ≤ st.count) :
    { r : Rd // r.status = .ok → TableArgs st.size (writeSimple (zeroBytes st.size.toNat) r) (r.e == 0) r.a } :=
  ⟨simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2), simple_args h ht h2⟩

theorem simpleFastT_val {st : Hd} {h : ∃ g p, HRel st g p} {ht : st.tag = .code} {h2 : 2 ≤ st.count} :
    (simpleFastT st h ht h2).1 = simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) := rfl

/-- The place at a prefix code's first two bits. -/
def stepHCode (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) (ht : st.tag = .code) : Hd :=
  let b0 : BitBuffer := ⟨st.word, st.count⟩
  if h2 : 2 ≤ st.count then
    let hskip := b0.peek 2
    let b1 := b0.drop 2
    if hskip = 1 then
      match simpleFastT st h ht h2 with
      | ⟨r, hr⟩ =>
      match hs : r.status with
      | .short => markH st pos .needsInput
      | .bad => markH st pos .bad
      | .ok =>
        tableDone { st with
            word := r.word, count := r.count, pos := pos, status := .next
            lens := writeSimple (zeroBytes st.size.toNat) r }
          (r.e == 0) r.a (hr hs) (code_install (st := st) h ht)
    else
      { st with
        word := b1.word, count := b1.count, pos := pos, status := .next, tag := .clens, clIdx := hskip, clSum := 0, clNz := 0, clSym := 0
        clLens := zeroBytes 18 }
  else markH st pos .needsInput

private theorem not_le_lt'' {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

private theorem codeOrder_ok : codeLengthOrder.Nodup ∧ ∀ x ∈ codeLengthOrder, x < 18 := by
  decide +kernel

/-- The state at the start of the code length alphabet's lengths. -/
theorem clStart_rel {hskip : UInt64} (hh : hskip.toNat < 4) {st : Hd} (h1 : st.clIdx = hskip) (h2 : st.clSum = 0) (h3 : st.clNz = 0)
    (h4 : st.clSym = 0) (h5 : st.clLens = zeroBytes 18) : ClRel st (codeLengthOrder.drop hskip.toNat) [] 0 where
  orderOk := by rw [h1]
  le := by rw [h1]; omega
  sumOk := by rw [h2]; rfl
  sumLt := by decide
  sumEq := by simp [lengthSum]
  size := by rw [h5]; exact zeroBytes_size (by decide)
  lens := fun i _ => by
    rw [h5, zeroBytes_get (by decide)]
    rfl
  keys := by simp
  apart := by simp
  nz := by rw [h3]; rfl
  nzLe := by rw [h3]; exact Nat.zero_le _
  nzOne := by simp
  symLt := by rw [h4]; decide

theorem stepHCode_ok {o : Owner} {size : Nat} {st : Hd} {g : Gh} {pos : USize} {hH : ∃ g p, HRel st g p} {hT : st.tag = .code}
    (hrel : HRel st g (.code o size)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop)
    (hb : st.d.arena.size + budH g (.code o size) ≤ st.d.arenaCap.toNat) :
    HStepOk K a stop g (.code o size) st pos (stepHCode st pos hH hT) := by
  obtain ⟨hw, hu, ht, hs, ho⟩ := hrel
  have hrel : HRel st g (.code o size) := ⟨hw, hu, ht, hs, ho⟩
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hs : SizeOk st size := ⟨hs1, hs2, hs3⟩
  unfold stepHCode
  dsimp only
  by_cases h2 : 2 ≤ st.count
  · rw [dite_eq_left h2]
    generalize hT' : simpleFastT st hH hT h2 = rr
    obtain ⟨r, hr⟩ := rr
    have e : r = simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) := by
      rw [← simpleFastT_val (h := hH) (ht := hT) (h2 := h2), hT']
    subst e
    dsimp only
    have hread := fun f => read_int (b := ⟨st.word, st.count⟩) (k := 2) f (by decide) h2
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    have hcount1 : ((BitBuffer.mk st.word st.count).drop 2).count.toNat = st.count.toNat - 2 :=
      drop_count (UInt64.le_iff_toNat_le.mp h2)
    have h2' : 2 ≤ st.count.toNat := UInt64.le_iff_toNat_le.mp h2
    have hhlt : ((BitBuffer.mk st.word st.count).peek 2).toNat < 4 := peek_lt _ (k := 2) (by decide)
    generalize (BitBuffer.mk st.word st.count).drop 2 = b1 at hread hw1 hcount1 hr
    generalize (BitBuffer.mk st.word st.count).peek 2 = hskip at hread hhlt
    have hspec : ∀ f, hrest K g (.code o size) ((BitBuffer.mk st.word st.count).held ++ f) =
        if hskip.toNat = 1 then (simpleChain size (alphabetBits size) (b1.held ++ f) >>= fun p => ownerK K g o p.1 p.2)
        else hrest K g (.clens o size (codeLengthOrder.drop hskip.toNat) [] 0) (b1.held ++ f) := by
      intro f
      rw [hrest_code, show readInt 2 ((BitBuffer.mk st.word st.count).held ++ f) = _ from hread f]
      rfl
    have hnil := hspec []
    rw [List.append_nil, List.append_nil] at hnil
    have hr0 : readInt 2 (BitBuffer.mk st.word st.count).held = some (hskip.toNat, b1.held) := by simpa using hread []
    by_cases h1 : hskip = 1
    · rw [ite_eq_left h1]
      have h1' : hskip.toNat = 1 := by rw [h1]; rfl
      rw [ite_eq_left h1'] at hnil
      simp only [h1', ↓reduceIte] at hspec
      obtain ⟨hbits, hbitsLe⟩ := alphabetBitsFast_toNat (size := st.size) (by omega)
      have R := simpleFast_ok (size := st.size) (bits := alphabetBitsFast st.size) hw1 hbitsLe
      rw [hbits, hs1] at R
      obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := fun bs => simpleChain size (alphabetBits size) bs >>= fun p => ownerK K g o p.1 p.2)
        (N := ownerK K g o) (fun bs => rfl)
      have hval := R.ok
      have hsh0 := R.short
      have hsmall := simpleFast_small st.size (alphabetBitsFast st.size) b1 hbitsLe
      generalize simpleFast st.size (alphabetBitsFast st.size) b1 = r at Rok Rshort Rbad hval hsmall hsh0 hr ⊢
      split
      · rename_i hsr
        obtain ⟨_, _, h3, h4⟩ := Rshort hsr
        obtain ⟨_, _, _, h5⟩ := hsh0 hsr
        refine HStepOk.ofShortRead (X := 45) hrel hfull (by omega) (by omega) (by rw [hnil]; exact h4) ?_
        show readIn 2 (readInt 2) _ _ = _
        rw [readIn_some hr0]
        show (if hskip.toNat = 1 then _ else _) = _
        rw [ite_eq_left h1']
        exact readIn_short h5 (by rw [held_len]; exact h3)
      · rename_i hsr
        exact HStepOk.ofBad rfl (fun F => by rw [avail_mk, hspec]; exact Rbad hsr _)
      · rename_i hsr
        obtain ⟨hw2, hN⟩ := Rok hsr
        have hN2 := (hval hsr).2 []
        simp only [List.append_nil] at hN2
        have hwit : readPrefixCode st.size.toNat (BitBuffer.mk st.word st.count).held = some (simpleValue st.size r, r.buf.held) := by
          have e : readInt 2 ((BitBuffer.mk st.word st.count).held ++ []) = some (1, b1.held ++ []) := by
            have := hread []
            rw [h1'] at this
            exact this
          simp only [List.append_nil] at e
          unfold readPrefixCode
          rw [e]
          show (if 1 = 1 then readSimple st.size.toNat b1.held else readComplex st.size.toNat 1 b1.held) = _
          rw [ite_eq_left rfl, simpleChain_eq, hs1]
          exact hN2
        have hdone := simple_done (K := K) pos hrel hw2 hwit hsmall hb (ha := hr hsr) (hi := code_install hH hT)
        generalize hc : simpleValue st.size r = c at hN hdone
        exact hdone.toStep rfl hp rfl (fun h => ⟨h.fill, by
            show (writeSimple (zeroBytes st.size.toNat) r).size ≤ _
            rw [writeSimple_size, zeroBytes_size (by omega), hs1]
            exact hs3,
            h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩) (fun F => by
          rw [avail_mk, hspec]
          exact hN _) (fun F => by
          rw [avail_mk]
          show readIn 2 (readInt 2) _ _ = _
          rw [readIn_some (show readInt 2 _ = _ from hread _)]
          show (if hskip.toNat = 1 then _ else _) = _
          rw [ite_eq_left h1']
          show readIn 43 (simpleChain size (alphabetBits size)) _ _ = _
          rw [readIn_some ((hval hsr).2 _), hc]
          rfl)
    · rw [ite_eq_right h1]
      have h1' : ¬ hskip.toNat = 1 := fun h => h1 (UInt64.toNat_inj.mp h)
      simp only [h1', ↓reduceIte] at hspec
      refine HStepOk.ofNext (g' := g) (p' := .clens o size (codeLengthOrder.drop hskip.toNat) [] 0) rfl
        (hm := ⟨rfl, rfl, fun h => ⟨h.fill, h.lens, by show (zeroBytes 18).size ≤ _; rw [zeroBytes_size (by decide)]; exact Nat.le_refl _,
          h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, h.dBase, h.work⟩,
          ⟨rfl, by simp [budH, tableOf]⟩⟩)
        ⟨hw1, hu, rfl, hs, ho, clStart_rel hhlt rfl rfl rfl rfl rfl⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
      · rw [avail_mk, hspec]
        rfl
      · rw [avail_mk]
        show readIn 2 (readInt 2) _ _ = _
        rw [readIn_some (show readInt 2 _ = _ from hread _)]
        show (if hskip.toNat = 1 then _ else _) = _
        rw [ite_eq_right h1']
        rfl
  · rw [dite_eq_right h2]
    have hc : st.count.toNat < 2 := not_le_lt'' h2
    have hnone : hrest K g (.code o size) (BitBuffer.mk st.word st.count).held = none := by
      rw [hrest_code, readInt_short (b := ⟨st.word, st.count⟩) hc]
      rfl
    exact HStepOk.ofShortRead (X := 2) hrel hfull (by omega) hc hnone
      (by show readIn 2 (readInt 2) _ _ = _; exact readIn_short (readInt_short (b := ⟨st.word, st.count⟩) hc) (by rw [held_len]; exact hc))

end

end Brotli.Decoder
