import Brotli.Decoder.HeaderMap

/-!
# The header machine, and the header it leaves

`stepH` is one step of the header machine, proved by `stepH_ok`. When it is ready, `mkHdr` makes the command loop's `Hdr`
from the header that was read: what that loop's proofs rest on holds of every header read (`hdr_facts`), so nothing is
checked.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The machine -/

/-- A step, once the buffer is refilled. Each place's step is handed what its place gives. -/
def stepAtH (st : Hd) (pos : USize) (h : ∃ g p, HRel st g p) : Hd :=
  match ht : st.tag with
  | .cat => stepHCat st pos
  | .code => stepHCode st pos h ht
  | .clens => stepHClens st pos h ht
  | .syms => stepHSyms st pos h ht
  | .first => stepHFirst st pos (first_fits h ht)
  | .np => stepHNp st pos
  | .modes => stepHModes st pos
  | .trees => stepHTrees st pos
  | .rlemax => stepHRlemax st pos
  | .vals => stepHVals st pos
  | .imtf => stepHImtf st pos
  | .codes => stepHCodes st pos
  | .ready => markH st pos .ready

section
variable {st : Hd} {pos : USize} {h : ∃ g p, HRel st g p}

/-- Settles `stepAtH`'s tag, given its equation. -/
macro "stepAtH_tag" ht:ident : tactic =>
  `(tactic| (unfold stepAtH; split <;> rename_i e <;> first | rfl | exact absurd (e.symm.trans $ht) (fun x => HTag.noConfusion x)))

theorem stepAtH_cat (ht : st.tag = .cat) : stepAtH st pos h = stepHCat st pos := by stepAtH_tag ht
theorem stepAtH_code (ht : st.tag = .code) : stepAtH st pos h = stepHCode st pos h ht := by stepAtH_tag ht
theorem stepAtH_clens (ht : st.tag = .clens) : stepAtH st pos h = stepHClens st pos h ht := by stepAtH_tag ht
theorem stepAtH_syms (ht : st.tag = .syms) : stepAtH st pos h = stepHSyms st pos h ht := by stepAtH_tag ht
theorem stepAtH_first (ht : st.tag = .first) : stepAtH st pos h = stepHFirst st pos (first_fits h ht) := by stepAtH_tag ht
theorem stepAtH_np (ht : st.tag = .np) : stepAtH st pos h = stepHNp st pos := by stepAtH_tag ht
theorem stepAtH_modes (ht : st.tag = .modes) : stepAtH st pos h = stepHModes st pos := by stepAtH_tag ht
theorem stepAtH_trees (ht : st.tag = .trees) : stepAtH st pos h = stepHTrees st pos := by stepAtH_tag ht
theorem stepAtH_rlemax (ht : st.tag = .rlemax) : stepAtH st pos h = stepHRlemax st pos := by stepAtH_tag ht
theorem stepAtH_vals (ht : st.tag = .vals) : stepAtH st pos h = stepHVals st pos := by stepAtH_tag ht
theorem stepAtH_imtf (ht : st.tag = .imtf) : stepAtH st pos h = stepHImtf st pos := by stepAtH_tag ht
theorem stepAtH_codes (ht : st.tag = .codes) : stepAtH st pos h = stepHCodes st pos := by stepAtH_tag ht
theorem stepAtH_ready (ht : st.tag = .ready) : stepAtH st pos h = markH st pos .ready := by stepAtH_tag ht

end

/-- A state's buffer is well formed. -/
theorem hrel_wf {st : Hd} (h : ∃ g p, HRel st g p) : (BitBuffer.mk st.word st.count).Wf := by
  obtain ⟨_, _, hr⟩ := h
  exact hr.wf

/-- New bits keep a state's place. -/
theorem hrel_bits {st : Hd} (h : ∃ g p, HRel st g p) {word count : UInt64} (hw : (BitBuffer.mk word count).Wf) :
    ∃ g p, HRel { st with word := word, count := count } g p := by
  obtain ⟨g, p, hr⟩ := h
  exact ⟨g, p, hr.withBits hw⟩

/-- A state's position is not part of its place. -/
theorem hrel_pos0 {st : Hd} (h : ∃ g p, HRel st g p) : ∃ g p, HRel { st with pos := 0 } g p := by
  obtain ⟨g, p, hr⟩ := h
  exact ⟨g, p, hr.mark 0 st.status⟩

/-- A state stands for a place, with room in the arena's reservation for the tables still to come. -/
def HIn (st : Hd) : Prop := ∃ g p, HRel st g p ∧ st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat

theorem HIn.rel {st : Hd} (h : HIn st) : ∃ g p, HRel st g p := by
  obtain ⟨g, p, hr, _⟩ := h
  exact ⟨g, p, hr⟩

/-- A refill, with the buffer it leaves well formed. -/
@[inline] def refillH (word count : UInt64) (a : ByteArray) (pos stop : USize) (hs : stop.toNat ≤ a.size) (hp : pos.toNat ≤ stop.toNat)
    (hw : (BitBuffer.mk word count).Wf) : { r : Refilled // r.buf.Wf } :=
  ⟨refill word count a pos stop hs hp, (refill_spec hs hp hw).1⟩

theorem refillH_val {word count : UInt64} {a : ByteArray} {pos stop : USize} {hs : stop.toNat ≤ a.size} {hp : pos.toNat ≤ stop.toNat}
    {hw : (BitBuffer.mk word count).Wf} : (refillH word count a pos stop hs hp hw).1 = refill word count a pos stop hs hp := rfl

/-- One step of the header machine. -/
def stepH (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Hd) (pos : USize) (h : HIn st)
    (hp : pos.toNat ≤ stop.toNat) : Hd :=
  match refillH st.word st.count a pos stop hs hp (hrel_wf h.rel) with
  | ⟨r, hr⟩ =>
    let rw := r.word
    let rc := r.count
    let rp := r.pos
    stepAtH { st with word := rw, count := rc } rp (hrel_bits h.rel hr)

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

theorem stepAtH_ok {g : Gh} {p : HPhase} {st : Hd} {pos : USize} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) {h : ∃ g p, HRel st g p} :
    HStepOk K a stop g p st pos (stepAtH st pos h) := by
  cases p with
  | cat i =>
    rw [stepAtH_cat hrel.2.2.1]
    exact stepHCat_ok hrel hp hfull
  | code o size =>
    rw [stepAtH_code hrel.2.2.1]
    exact stepHCode_ok hrel hp hfull hb
  | clens o size order acc sum =>
    rw [stepAtH_clens hrel.2.2.1]
    exact stepHClens_ok hrel hp hfull
  | syms o size clc ls =>
    rw [stepAtH_syms hrel.2.2.1]
    exact stepHSyms_ok hrel hp hfull hb
  | first i n tc cc =>
    rw [stepAtH_first hrel.2.2.1]
    exact stepHFirst_ok hrel hp hfull
  | np =>
    rw [stepAtH_np hrel.2.2]
    exact stepHNp_ok hrel hp hfull
  | modes done left =>
    rw [stepAtH_modes hrel.2.2.1]
    exact stepHModes_ok hrel hp hfull
  | trees isL =>
    rw [stepAtH_trees hrel.2.2.1]
    exact stepHTrees_ok hrel hp hfull
  | rlemax isL ntrees =>
    rw [stepAtH_rlemax hrel.2.2.1]
    exact stepHRlemax_ok hrel hp hfull
  | vals isL ntrees rlemax code done left =>
    rw [stepAtH_vals hrel.2.2.1]
    exact stepHVals_ok hrel hp hfull
  | imtf isL ntrees vals =>
    rw [stepAtH_imtf hrel.2.2.1]
    exact stepHImtf_ok hrel hp hfull
  | codes k done left =>
    rw [stepAtH_codes hrel.2.2.1]
    exact stepHCodes_ok hrel hp

/-- What a step of the header machine does in the spec's terms, for every future. -/
theorem stepH_ok {g : Gh} {p : HPhase} {st : Hd} {pos : USize} {hs : stop.toNat ≤ a.size} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) {h : HIn st} :
    HStepOk K a stop g p st pos (stepH a stop hs st pos h hp) := by
  unfold stepH refillH
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  dsimp only
  refine (stepAtH_ok (hrel.withBits h1) h3 h5 hb).refilled (fun F => ?_) h2 h3 ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩
  show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
    (refill st.word st.count a pos stop hs hp).buf.held ++
      (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ F)
  rw [← List.append_assoc, ← List.append_assoc, h4]

end

/-- A header step that leaves a header ready leaves one that was read. -/
theorem stepH_upto {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize}
    (h : HIn st) (hp : pos.toNat ≤ stop.toNat) (hst : (stepH a stop hs st pos h hp).status = .ready) :
    ∃ g, Upto (stepH a stop hs st pos h hp).d g 10 := by
  obtain ⟨g, p, hrel, hb⟩ := id h
  obtain ⟨g', hu, _⟩ := (stepH_ok (K := (⟨fun _ _ => none, fun _ x => x⟩ : HK Unit)) (hs := hs) hrel hp hb).ready hst
  exact ⟨g', hu⟩

/-- A header step, with what a ready header gives. -/
@[inline] def stepHR (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Hd) (pos : USize) (h : HIn st)
    (hp : pos.toNat ≤ stop.toNat) : { r : Hd // r.status = .ready → ∃ g, Upto r.d g 10 } :=
  ⟨stepH a stop hs st pos h hp, stepH_upto h hp⟩

theorem stepHR_val {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} {h : HIn st}
    {hp : pos.toNat ≤ stop.toNat} : (stepHR a stop hs st pos h hp).1 = stepH a stop hs st pos h hp := rfl

/-! ### The command loop's header -/

/-- The sizes and small values a command loop's header needs. -/
def HdrSizes (d : Done) : Prop :=
  d.arena.size < 4294967296 ∧ d.litBase.size < 4294967296 ∧ d.lMap.size < 4294967296 ∧ d.litBase.size = 4 * d.treesL.toNat ∧
    d.npostfix.toNat ≤ 3 ∧ d.ndirect.toNat ≤ 120 ∧ d.lMap.size = 64 * d.nL.toNat ∧ d.modes.size = d.nL.toNat ∧
    d.icBase.size = 4 * d.nI.toNat ∧ d.icBase.size < 4294967296 ∧ d.dBase.size = 4 * d.treesD.toNat ∧ d.dBase.size < 4294967296 ∧
    d.dMap.size = 4 * d.nD.toNat ∧ d.dMap.size < 4294967296 ∧ d.treesL.toNat ≤ 256 ∧ d.treesD.toNat ≤ 256 ∧ d.nI.toNat ≤ 256

/-- The bounds on the maps and modes, and the tables that fit, as `Hdr` states them. -/
structure HdrProps (d : Done) : Prop where
  treeLt : ∀ p : USize, ∀ h : p.toNat < d.lMap.size, (d.lMap.uget p h).toNat < d.treesL.toNat
  fits : ∀ tree, tree < d.treesL.toNat → TableFits d.arena (u32At d.litBase tree)
  modesLt : ∀ p : USize, ∀ h : p.toNat < d.modes.size, (d.modes.uget p h).toNat < 4
  icFits : ∀ t, t < d.nI.toNat → TableFits d.arena (u32At d.icBase t)
  dMapLt : ∀ p : USize, ∀ h : p.toNat < d.dMap.size, (d.dMap.uget p h).toNat < d.treesD.toNat
  dFits : ∀ tree, tree < d.treesD.toNat → TableFits d.arena (u32At d.dBase tree)
  swL : 2 ≤ d.nL.toNat → TableFits d.arena d.baseTL.toNat ∧ TableFits d.arena d.baseCL.toNat
  swI : 2 ≤ d.nI.toNat → TableFits d.arena d.baseTI.toNat ∧ TableFits d.arena d.baseCI.toNat
  swD : 2 ≤ d.nD.toNat → TableFits d.arena d.baseTD.toNat ∧ TableFits d.arena d.baseCD.toNat

/-- A map's bytes are its values. -/
private theorem mapOk_lt {b : ByteArray} {l : List Nat} {size n : Nat} (hm : MapOk b l size n) :
    ∀ p : USize, ∀ h : p.toNat < b.size, (b.uget p h).toNat < n := by
  intro p h
  rw [uget_toNat]
  have hps : p.toNat < size := by rw [← hm.sz]; exact h
  exact hm.lt _ (List.mem_of_getElem? (hm.at_ _ hps))

/-- Every header read has what the command loop's header needs. -/
theorem hdr_facts {d : Done} {g : Gh} (hu : Upto d g 10) : HdrSizes d ∧ HdrProps d := by
  have hL := hu.cat .L (by decide)
  have hI := hu.cat .I (by decide)
  have hD := hu.cat .D (by decide)
  have hLn : d.nL.toNat = g.m.literal.n := hL.n
  have hIn : d.nI.toNat = g.m.insertCopy.n := hI.n
  have hDn : d.nD.toNat = g.m.distance.n := hD.n
  have hLw : g.m.literal.n ≤ 256 := hL.wf.2.1
  have hIw : g.m.insertCopy.n ≤ 256 := hI.wf.2.1
  have hDw : g.m.distance.n ≤ 256 := hD.wf.2.1
  obtain ⟨_, _, np3, np4⟩ := hu.np (by decide)
  have hm := hu.modes (by decide)
  obtain ⟨tl1, _, tl3, ml⟩ := hu.lmap (by decide)
  obtain ⟨td1, _, td3, md⟩ := hu.dmap (by decide)
  obtain ⟨cl1, cl⟩ := hu.codes .L (by decide)
  obtain ⟨ci1, ci⟩ := hu.codes .I (by decide)
  obtain ⟨cd1, cd⟩ := hu.codes .D (by decide)
  have ha32 : d.arena.size < 4294967296 := by
    have := hu.le
    have := hu.max
    omega
  have clB : d.litBase.size = 4 * g.treesL := cl.basesSize
  have ciB : d.icBase.size = 4 * g.m.insertCopy.n := ci.basesSize
  have cdB : d.dBase.size = 4 * g.treesD := cd.basesSize
  have hmL : d.lMap.size = 64 * d.nL.toNat := by rw [ml.sz, hLn]; rfl
  have hmD : d.dMap.size = 4 * d.nD.toNat := by rw [md.sz, hDn]; rfl
  have hsizes : HdrSizes d := by
    refine ⟨ha32, by rw [clB]; omega, by rw [hmL]; omega, by rw [clB, tl1], by omega, by omega, hmL, ?_, by rw [ciB, hIn], by rw [ciB]; omega,
      by rw [cdB, td1], by rw [cdB]; omega, hmD, by rw [hmD]; omega, by omega, by omega, by omega⟩
    rw [hm.sz, hLn]
  have tablesFrom : ∀ {cs : List PrefixCode} {bases : ByteArray} {total size : Nat}, CodesPart d.arena bases cs total size → cs.length = total →
      ∀ t, t < total → TableFits d.arena (u32At bases t) := by
    intro cs bases total size hp hl t ht
    obtain ⟨c, _, h2, _⟩ := hp.code t (by omega)
    exact h2.toTableFits
  have catOf : ∀ {i : Cat} {c : BlockCategory}, CatOk d i c → 2 ≤ (d.nOf i).toNat →
      TableFits d.arena (d.baseTOf i).toNat ∧ TableFits d.arena (d.baseCOf i).toNat := by
    intro i c h hn
    have h2 : 2 ≤ c.n := by rw [← h.n]; exact hn
    exact ⟨(h.rel.type h2).1.toTableFits, (h.rel.count h2).1.toTableFits⟩
  exact ⟨hsizes, ⟨by rw [tl1]; exact mapOk_lt ml, by rw [tl1]; exact tablesFrom cl cl1.symm, mapOk_lt hm,
    by rw [hIn]; exact tablesFrom ci ci1.symm, by rw [td1]; exact mapOk_lt md, by rw [td1]; exact tablesFrom cd cd1.symm,
    catOf hL, catOf hI, catOf hD⟩⟩

/-- Makes the command loop's header from a header that was read. -/
def mkHdr (d : Done) (h : ∃ g, Upto d g 10) : Hdr :=
  have hf : HdrSizes d ∧ HdrProps d := by
    obtain ⟨g, hu⟩ := h
    exact hdr_facts hu
  { arena := d.arena, arenaCap := d.arenaCap, litBase := d.litBase, lMap := d.lMap, icBase := d.icBase, dBase := d.dBase
    dMap := d.dMap, modes := d.modes
    nL := d.nL, nI := d.nI, nD := d.nD, treesL := d.treesL, treesD := d.treesD
    baseTL := d.baseTL, baseCL := d.baseCL, baseTI := d.baseTI, baseCI := d.baseCI, baseTD := d.baseTD, baseCD := d.baseCD
    npostfix := d.npostfix, ndirect := d.ndirect
    npLe := hf.1.2.2.2.2.1, ndLe := hf.1.2.2.2.2.2.1
    lit := ⟨hf.1.1, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2.1, hf.2.treeLt, hf.2.fits⟩
    lMapSize := hf.1.2.2.2.2.2.2.1
    modesSize := hf.1.2.2.2.2.2.2.2.1
    modesLt := hf.2.modesLt
    icSize := hf.1.2.2.2.2.2.2.2.2.1
    ic32 := hf.1.2.2.2.2.2.2.2.2.2.1
    icFits := hf.2.icFits
    dSize := hf.1.2.2.2.2.2.2.2.2.2.2.1
    d32 := hf.1.2.2.2.2.2.2.2.2.2.2.2.1
    dMapSize := hf.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    dMap32 := hf.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    dMapLt := hf.2.dMapLt
    dFits := hf.2.dFits
    swL := hf.2.swL
    swI := hf.2.swI
    swD := hf.2.swD }

/-- The header made from a header that was read matches the spec's. -/
theorem mkHdr_ok {d : Done} {g : Gh} (hu : Upto d g 10) (h : ∃ g, Upto d g 10) : HdrRel (mkHdr d h) g.m := by
  have hL := hu.cat .L (by decide)
  have hI := hu.cat .I (by decide)
  have hD := hu.cat .D (by decide)
  have hLn : d.nL.toNat = g.m.literal.n := hL.n
  have hIn : d.nI.toNat = g.m.insertCopy.n := hI.n
  have hDn : d.nD.toNat = g.m.distance.n := hD.n
  obtain ⟨np1, np2, _, _⟩ := hu.np (by decide)
  have hm := hu.modes (by decide)
  obtain ⟨tl1, _, _, ml⟩ := hu.lmap (by decide)
  obtain ⟨td1, _, _, md⟩ := hu.dmap (by decide)
  obtain ⟨cl1, cl⟩ := hu.codes .L (by decide)
  obtain ⟨ci1, ci⟩ := hu.codes .I (by decide)
  obtain ⟨cd1, cd⟩ := hu.codes .D (by decide)
  have codesMem : ∀ {cs : List PrefixCode} {bases : ByteArray} {total size : Nat}, CodesPart d.arena bases cs total size →
      ∀ c ∈ cs, c.Symbols size ∧ Complete c := by
    intro cs bases total size hp c hc
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨c1, h1, _, h3, h4⟩ := hp.code i hi
    rw [List.getElem?_eq_getElem hi, e] at h1
    have := Option.some.inj h1
    subst this
    exact ⟨h4, h3⟩
  unfold mkHdr
  exact {
    ok := {
      literal := hL.wf
      insertCopy := hI.wf
      distance := hD.wf
      literalCount := fun h => (hL.rel.count h).2.2
      insertCopyCount := fun h => (hI.rel.count h).2.2
      distanceCount := fun h => (hD.rel.count h).2.2
      modes_length := hm.length
      literalMap_length := ml.length
      literalMap_lt := fun v hv => by
        have := ml.lt v hv
        rw [← show g.treesL = g.m.literalCodes.length from cl1]
        exact this
      literalCodes := codesMem cl
      insertCopyCodes_length := ci1.symm
      insertCopyCodes := codesMem ci
      distanceMap_length := md.length
      distanceMap_lt := fun v hv => by
        have := md.lt v hv
        rw [← show g.treesD = g.m.distanceCodes.length from cd1]
        exact this
      distanceCodes := codesMem cd
      literalSwitch := ⟨hL.tc, hL.cc⟩
      insertCopySwitch := ⟨hI.tc, hI.cc⟩
      distanceSwitch := ⟨hD.tc, hD.cc⟩ }
    nL := hLn
    nI := hIn
    nD := hDn
    npostfix := np1
    ndirect := np2
    lit := {
      map := fun p h => by
        rw [uget_toNat]
        exact ml.at_ _ (by rw [← ml.sz]; exact h)
      code := fun t ht => by
        obtain ⟨c, h1, h2, h3, h4⟩ := cl.code t (by rw [← cl1]; rw [tl1] at ht; exact ht)
        exact ⟨c, h1, h2, h3, h4⟩ }
    modes := fun p h => by
      rw [uget_toNat]
      exact hm.at_ _ (by rw [← hm.sz]; exact h)
    ic := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := ci.code t (by rw [← ci1]; rw [hIn] at ht; exact ht)
      exact ⟨c, h1, h2, h3, h4⟩
    dMap := fun p h => by
      rw [uget_toNat]
      exact md.at_ _ (by rw [← md.sz]; exact h)
    d := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := cd.code t (by rw [← cd1]; rw [td1] at ht; exact ht)
      exact ⟨c, h1, h2, h3, h4⟩
    catL := hL.rel
    catI := hI.rel
    catD := hD.rel }

end Brotli.Decoder
