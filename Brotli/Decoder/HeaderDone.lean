module

public import Brotli.Decoder.HeaderMap
public import Brotli.Decoder.HeaderLens
public import Brotli.Decoder.HeaderStep2
public import Brotli.Decoder.LitTriv

@[expose] public section

/-!
# The header machine, and the header it leaves

`stepH` is one step of the header machine, proved by `stepH_ok`. When it is ready, `mkHdr` makes the command loop's `Hdr`
from the header that was read: what that loop's proofs rest on holds of every header read (`hdr_facts`), so nothing is
checked.
-/

namespace Brotli.Decoder

open Brotli.Spec

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
  | .modes => stepHModes st pos h ht
  | .trees => stepHTrees st pos
  | .rlemax => stepHRlemax st pos
  | .vals => stepHVals st pos h ht
  | .imtf => stepHImtf st pos h ht
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
theorem stepAtH_modes (ht : st.tag = .modes) : stepAtH st pos h = stepHModes st pos h ht := by stepAtH_tag ht
theorem stepAtH_trees (ht : st.tag = .trees) : stepAtH st pos h = stepHTrees st pos := by stepAtH_tag ht
theorem stepAtH_rlemax (ht : st.tag = .rlemax) : stepAtH st pos h = stepHRlemax st pos := by stepAtH_tag ht
theorem stepAtH_vals (ht : st.tag = .vals) : stepAtH st pos h = stepHVals st pos h ht := by stepAtH_tag ht
theorem stepAtH_imtf (ht : st.tag = .imtf) : stepAtH st pos h = stepHImtf st pos h ht := by stepAtH_tag ht
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
    exact stepHCodes_ok hrel hp hb

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

/-! ### The fast command loop's tables -/

/-- What the derived tables' builder needs, from a header that was read: its arena `A`, the rest of its record `d`, and
its literal types' shared tables `lTriv`. -/
theorem tabArgs_of {A : ByteArray} {d : Done} {g : Gh} (hu : Upto { d with arena := A } g 10) {lTriv : ByteArray}
    (ht : lTriv.size = 4 * d.nL.toNat) (hok : TrivInv d.lMap d.litBase lTriv d.nL.toNat) :
    TabArgs A d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
      d.treesD.toNat := by
  obtain ⟨hs, hp⟩ := hdr_facts hu
  unfold HdrSizes at hs
  dsimp only at hs
  obtain ⟨_, _, h3, h4, _, _, h7, _, h9, _, h11, _, h13, _, h15, h16, h17⟩ := hs
  have hL := hu.cat .L (by decide)
  have hD := hu.cat .D (by decide)
  have hLn : d.nL.toNat = g.m.literal.n := hL.n
  have hDn : d.nD.toNat = g.m.distance.n := hD.n
  have hIn : d.nI.toNat = g.m.insertCopy.n := (hu.cat .I (by decide)).n
  have hL2 : g.m.literal.n ≤ 256 := hL.wf.2.1
  have hD2 : g.m.distance.n ≤ 256 := hD.wf.2.1
  have hfin := hu.fin rfl
  have hmax := hu.max
  have hpre := hu.pre
  dsimp only at hfin hmax hpre
  unfold arenaPre at hpre
  have htm : tabMaxOf g = tabMax d.nL.toNat d.nI.toNat d.nD.toNat := by
    unfold tabMaxOf
    rw [hLn, hIn, hDn, Nat.min_eq_left hL2, Nat.min_eq_left (by omega), Nat.min_eq_left hD2]
  refine ⟨⟨by omega, h17, by omega, h4, h15, h7, hp.treeLt, h9, h11, h16, h13, hp.dMapLt, ht⟩, ?_, hpre, hu.masks,
    hp.fits, hp.icFits, hp.dFits, fun t hti hne => ?_⟩
  · have : A.size + tabMaxOf g ≤ d.arenaCap.toNat := hfin
    rw [htm] at this
    omega
  · have e0 := hok t hti hne 0 (by decide)
    rw [Nat.add_zero] at e0
    have hp64 : (USize.ofNat (64 * t)).toNat = 64 * t := fastLit (by omega)
    have hlt := hp.treeLt (USize.ofNat (64 * t)) (by rw [hp64, h7]; omega)
    rw [uget_toNat, hp64] at hlt
    rw [← e0]
    exact hp.fits _ hlt

/-- The arena with the fast command loop's derived tables appended, the literal types chosen for two-literal tables
by the policy. -/
def buildArena (A : ByteArray) (d : Done) (lTriv : ByteArray) (mlen : UInt64)
    (h : TabArgs A d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
      d.treesD.toNat) (hd : DshAt A d.npostfix d.ndirect 256) :
    { T : ByteArray // Extends A T ∧ TabOk T d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat
      d.nD.toNat d.treesL.toNat d.treesD.toNat d.npostfix d.ndirect (A.size + padOf A.size) ∧
      T.size ≤ A.size + tabMax d.nL.toNat d.nI.toNat d.nD.toNat } :=
  match tabPolicy A (by have := h.size; omega) d.icBase d.nI.toNat h.arrs.icSize
      (by have := h.arrs.icSize; have := h.arrs.nI256; omega) (fun ti hti => (h.icFits ti hti).root) lTriv d.nL.toNat
      h.arrs.trivSize h.arrs.nL256 h.trivFits mlen with
  | ⟨(fl, A1), hA⟩ =>
    ⟨buildTab A1 d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat d.nD.toNat d.treesL.toNat
        d.treesD.toNat (by rw [show A1 = A from hA]; exact h) fl.1 fl.2.1 fl.2.2.1 fl.2.2.2,
      by
        have e : A1 = A := hA
        subst e
        exact ⟨buildTab_extends _ _ _ _ _, buildTab_ok _ hd _ _ _ _, buildTab_size _ _ _ _ _⟩⟩

/-- A table keeps what it decodes in an arena that begins with the one it was built in. -/
theorem TableOk.extend {A T : ByteArray} {b : Nat} {c : PrefixCode} (h : TableOk A b c) (he : Extends A T)
    (h4 : A.size % 2 = 0) : TableOk T b c :=
  h.frame h4 he.1 (fun q hq => he.slotAt (by omega))

/-- An arena that begins with another keeps it, as the header's growth does. -/
theorem Extends.keep {A T : ByteArray} (he : Extends A T) (h4 : A.size % 2 = 0) : Keep A T :=
  ⟨h4, he.1, fun q hq => he.slotAt (by omega)⟩

/-- Takes a settled record's arena out of it, so that the arena is held once while the derived tables are appended. -/
@[noinline] def takeArena (d : Done) : ByteArray × Done := (d.arena, clearArena d)

theorem takeArena_back {d d0 : Done} {A : ByteArray} (h : takeArena d = (A, d0)) : { d0 with arena := A } = d := by
  unfold takeArena clearArena at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  rfl

theorem implSlots_idx {t : ByteArray} {base j : USize} (hr : 2 * (base.toNat + 256) ≤ t.size) (s : t.size < 2 ^ 32)
    (hj : j < USize.ofNat 64) : 2 * (base + j * USize.ofNat 4).toNat + 2 ≤ t.size := by
  have := fastLt (by decide) hj
  have e : (j * USize.ofNat 4).toNat = 4 * j.toNat := by
    have hU := USize.le_size
    rw [USize.size_eq_two_pow] at hU
    rw [USize.toNat_mul, fastLit (by decide), Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  rw [fastAdd (by omega), e]
  omega

/-- Of every fourth of an insert-and-copy tree's root slots, from the `j`-th, how many hold a code word of at most 8 bits
for a symbol below 128, whose distance is implicit: in 64ths, about the share of commands that reuse the last
distance. -/
def implSlots (t : ByteArray) (s : t.size < 2 ^ 32) (base : USize) (hr : 2 * (base.toNat + 256) ≤ t.size) (j : USize)
    (acc : UInt64) : UInt64 :=
  if hj : j < USize.ofNat 64 then
    implSlots t s base hr (j + USize.ofNat 1)
      (if slot16 t (base + j * USize.ofNat 4) (implSlots_idx hr s hj) s &&& 15 ≤ 8 ∧
          slot16 t (base + j * USize.ofNat 4) (implSlots_idx hr s hj) s >>> 4 < 128
        then acc + 1 else acc)
  else acc
termination_by 64 - j.toNat
decreasing_by
  have := fastLt (by decide) hj
  rw [fastIdx_succ hj]
  omega

/-- `implSlots` summed over the insert-and-copy trees from `ti`. -/
def implTypes (t : ByteArray) (s : t.size < 2 ^ 32) (icBase : ByteArray) (nI : Nat) (hic : icBase.size = 4 * nI)
    (hi32 : icBase.size < 2 ^ 32) (hI : ICReady icBase nI t) (ti : USize) (acc : UInt64) : UInt64 :=
  if hti : ti < USize.ofNat nI then
    have hn : ti.toNat < nI := fastLt (by omega) hti
    implTypes t s icBase nI hic hi32 hI (ti + USize.ofNat 1)
      (implSlots t s (slotWord icBase ti (by rw [hic]; omega) hi32).toUSize
        (by
          have hv := slotWord_toNat (i := ti) (by rw [hic]; omega) hi32
          rw [word_toUSize (by rw [hv]; exact u32At_lt _ _), hv]
          exact hI _ hn) 0 acc)
  else acc
termination_by nI - ti.toNat
decreasing_by
  have := fastLt (by omega) hti
  rw [fastIdx_succ hti]
  omega

/-- The command loop a header's commands run in: the one that decodes a distance only when it is explicit when a quarter
or more of the insert-and-copy trees' sampled root slots are for implicit distances. A policy: both loops give the same
result (`fastLoopS_eq`). -/
def implSel (t : ByteArray) (s : t.size < 2 ^ 32) (icBase : ByteArray) (nI : Nat) (hic : icBase.size = 4 * nI)
    (hi32 : icBase.size < 2 ^ 32) (hI : ICReady icBase nI t) : Bool :=
  decide (0 < nI) && 16 * UInt64.ofNat nI ≤ implTypes t s icBase nI hic hi32 hI 0 0

/-- The command loop's header, from a header that was read with its arena `A` taken out of the rest of its record `d`, and
its arena with the derived tables `R`. -/
def hdrOfArena (A : ByteArray) (d : Done) (hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A })
    (lTriv : ByteArray) (ht : lTriv.size = 4 * d.nL.toNat) (hok : TrivInv d.lMap d.litBase lTriv d.nL.toNat)
    (R : { T : ByteArray // Extends A T ∧ TabOk T d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat
      d.nD.toNat d.treesL.toNat d.treesD.toNat d.npostfix d.ndirect (A.size + padOf A.size) ∧
      T.size ≤ A.size + tabMax d.nL.toNat d.nI.toNat d.nD.toNat }) : Hdr :=
  match R with
  | ⟨T, hT⟩ =>
    { arena := T, arenaCap := d.arenaCap, litBase := d.litBase, lMap := d.lMap, icBase := d.icBase, dBase := d.dBase
      dMap := d.dMap, modes := d.modes
      nL := d.nL, nI := d.nI, nD := d.nD, treesL := d.treesL, treesD := d.treesD
      baseTL := d.baseTL, baseCL := d.baseCL, baseTI := d.baseTI, baseCI := d.baseCI, baseTD := d.baseTD, baseCD := d.baseCD
      npostfix := d.npostfix, ndirect := d.ndirect
      npLe := hf.1.2.2.2.2.1, ndLe := hf.1.2.2.2.2.2.1
      lit := ⟨hT.2.1.size32, hf.1.2.1, hf.1.2.2.1, hf.1.2.2.2.1, hf.2.treeLt,
        fun tree htr => (hT.2.1.lFit tree htr).fits (by have := hT.2.1.sizeOk; omega)⟩
      lMapSize := hf.1.2.2.2.2.2.2.1
      modesSize := hf.1.2.2.2.2.2.2.2.1
      modesLt := hf.2.modesLt
      icSize := hf.1.2.2.2.2.2.2.2.2.1
      ic32 := hf.1.2.2.2.2.2.2.2.2.2.1
      icFits := fun t hti => (hT.2.1.iFit t hti).fits (by have := hT.2.1.sizeOk; omega)
      dSize := hf.1.2.2.2.2.2.2.2.2.2.2.1
      d32 := hf.1.2.2.2.2.2.2.2.2.2.2.2.1
      dMapSize := hf.1.2.2.2.2.2.2.2.2.2.2.2.2.1
      dMap32 := hf.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dMapLt := hf.2.dMapLt
      dFits := fun tree htr => (hT.2.1.dFit tree htr).fits (by have := hT.2.1.sizeOk; omega)
      swL := fun h2 => ⟨(hf.2.swL h2).1.extend hT.1, (hf.2.swL h2).2.extend hT.1⟩
      swI := fun h2 => ⟨(hf.2.swI h2).1.extend hT.1, (hf.2.swI h2).2.extend hT.1⟩
      swD := fun h2 => ⟨(hf.2.swD h2).1.extend hT.1, (hf.2.swD h2).2.extend hT.1⟩
      lTriv := lTriv
      trivSize := ht
      trivOk := hok
      tabF0 := USize.ofNat (A.size + padOf A.size)
      dsel := implSel T hT.2.1.size32 d.icBase d.nI.toNat hf.1.2.2.2.2.2.2.2.2.1 hf.1.2.2.2.2.2.2.2.2.2.1
        (fun ti hti => ((hT.2.1.iFit ti hti).fits (by have := hT.2.1.sizeOk; omega)).root) }

/-- Makes the command loop's header from a header that was read, with its arena `A` taken out of the rest of its record
`d`: the literal types' shared tables, then the derived tables appended to the arena in place. -/
def mkHdrOf (A : ByteArray) (d : Done) (mlen : UInt64) (h : ∃ g, Upto { d with arena := A } g 10)
    (hd : DshAt A d.npostfix d.ndirect 256) : Hdr :=
  have hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A } := by
    obtain ⟨g, hu⟩ := h
    exact hdr_facts hu
  hdrOfArena A d hf
    (trivBuild d.lMap d.litBase d.treesL.toNat d.nL hf.1.2.2.2.2.2.2.1 hf.1.2.2.1 hf.1.2.2.2.1 hf.1.2.1 hf.2.treeLt)
    trivBuild_spec.1 trivBuild_spec.2
    (buildArena A d
      (trivBuild d.lMap d.litBase d.treesL.toNat d.nL hf.1.2.2.2.2.2.2.1 hf.1.2.2.1 hf.1.2.2.2.1 hf.1.2.1 hf.2.treeLt) mlen
      (by obtain ⟨g, hu⟩ := h; exact tabArgs_of hu trivBuild_spec.1 trivBuild_spec.2) hd)

theorem takeArena_upto {d d0 : Done} {A : ByteArray} (hT : takeArena d = (A, d0)) (h : ∃ g, Upto d g 10) :
    ∃ g, Upto { d0 with arena := A } g 10 := by
  rw [takeArena_back hT]
  exact h

/-- A header that was read has room for the shared distance table in its arena's prefix. -/
theorem upto_dshRoom {d : Done} (h : ∃ g, Upto d g 10) : 4416 ≤ d.arena.size ∧ d.arena.size < 2 ^ 32 := by
  obtain ⟨g, hu⟩ := h
  have := hu.pre
  have := hu.le
  have := hu.max
  unfold arenaPre at *
  omega

/-- Writing the shared distance table changes the arena only in its prefix, after the masks. -/
theorem keepAbove_dsh {A : ByteArray} {np nd : UInt64} {h1 : 4416 ≤ A.size} {h2 : A.size < 2 ^ 32} :
    KeepAbove A (writeDsh np nd A h1 h2) := by
  obtain ⟨s1, s2, s3, _⟩ := writeDsh_spec (np := np) (nd := nd) (t := A) (h := h1) (h32 := h2)
  exact ⟨s1, s2, fun q hq => s3 q hq⟩

theorem upto_dsh {d0 : Done} {A : ByteArray} {np nd : UInt64} {h1 : 4416 ≤ A.size} {h2 : A.size < 2 ^ 32}
    (h : ∃ g, Upto { d0 with arena := A } g 10) : ∃ g, Upto { d0 with arena := writeDsh np nd A h1 h2 } g 10 := by
  obtain ⟨g, hu⟩ := h
  exact ⟨g, hu.frameAbove keepAbove_dsh⟩

/-- Makes the command loop's header from a header that was read. The arena is taken out of the record first, so that it
is held once while the shared distance table is written into its prefix and the derived tables are appended. -/
def mkHdr (d : Done) (mlen : UInt64) (h : ∃ g, Upto d g 10) : Hdr :=
  match hT : takeArena d with
  | (A, d0) =>
    have hr := upto_dshRoom (takeArena_upto hT h)
    mkHdrOf (writeDsh d0.npostfix d0.ndirect A hr.1 hr.2) d0 mlen (upto_dsh (takeArena_upto hT h))
      writeDsh_spec.2.2.2

/-- The header made from a header that was read matches the spec's. -/
theorem hdrOfArena_ok {A : ByteArray} {d : Done} {g : Gh} (hu : Upto { d with arena := A } g 10)
    {hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A }} {lTriv : ByteArray}
    {ht : lTriv.size = 4 * d.nL.toNat} {hok : TrivInv d.lMap d.litBase lTriv d.nL.toNat}
    (R : { T : ByteArray // Extends A T ∧ TabOk T d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat
      d.nD.toNat d.treesL.toNat d.treesD.toNat d.npostfix d.ndirect (A.size + padOf A.size) ∧
      T.size ≤ A.size + tabMax d.nL.toNat d.nI.toNat d.nD.toNat }) :
    HdrRel (hdrOfArena A d hf lTriv ht hok R) g.m := by
  obtain ⟨T, hE, hTab, _⟩ := R
  have h4' : A.size % 2 = 0 := hu.four
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
  have codesMem : ∀ {cs : List PrefixCode} {bases : ByteArray} {total size : Nat}, CodesPart A bases cs total size →
      ∀ c ∈ cs, c.Symbols size ∧ Complete c := by
    intro cs bases total size hp c hc
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.mp hc
    obtain ⟨c1, h1, _, h3, h4⟩ := hp.code i hi
    rw [List.getElem?_eq_getElem hi, e] at h1
    have := Option.some.inj h1
    subst this
    exact ⟨h4, h3⟩
  have hf0 : (USize.ofNat (A.size + padOf A.size)).toNat = A.size + padOf A.size :=
    fastLit (by have := hTab.sizeOk; have := hTab.size32; omega)
  unfold hdrOfArena
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
        exact ⟨c, h1, h2.extend hE h4', h3, h4⟩ }
    modes := fun p h => by
      rw [uget_toNat]
      exact hm.at_ _ (by rw [← hm.sz]; exact h)
    ic := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := ci.code t (by rw [← ci1]; rw [hIn] at ht; exact ht)
      exact ⟨c, h1, h2.extend hE h4', h3, h4⟩
    dMap := fun p h => by
      rw [uget_toNat]
      exact md.at_ _ (by rw [← md.sz]; exact h)
    d := fun t ht => by
      obtain ⟨c, h1, h2, h3, h4⟩ := cd.code t (by rw [← cd1]; rw [td1] at ht; exact ht)
      exact ⟨c, h1, h2.extend hE h4', h3, h4⟩
    catL := hL.rel.frame (hE.keep h4')
    catI := hI.rel.frame (hE.keep h4')
    catD := hD.rel.frame (hE.keep h4')
    tab := by
      show TabOk T _ _ _ _ _ _ _ _ _ _ _ _ _ (USize.ofNat (A.size + padOf A.size)).toNat
      rw [hf0]
      exact hTab }

/-- The header made from a header that was read matches the spec's. -/
theorem mkHdr_ok {d : Done} {g : Gh} {mlen : UInt64} (hu : Upto d g 10) (h : ∃ g, Upto d g 10) :
    HdrRel (mkHdr d mlen h) g.m := by
  unfold mkHdr
  split
  rename_i A d0 hT
  have hb := takeArena_back hT
  subst hb
  unfold mkHdrOf
  exact hdrOfArena_ok (A := writeDsh d0.npostfix d0.ndirect A _ _) (d := d0) (hu.frameAbove keepAbove_dsh) _

theorem hdrOfArena_size {A : ByteArray} {d : Done} {hf : HdrSizes { d with arena := A } ∧ HdrProps { d with arena := A }}
    {lTriv : ByteArray} {ht : lTriv.size = 4 * d.nL.toNat} {hok : TrivInv d.lMap d.litBase lTriv d.nL.toNat}
    (R : { T : ByteArray // Extends A T ∧ TabOk T d.litBase d.lMap d.icBase d.dBase d.dMap lTriv d.nL.toNat d.nI.toNat
      d.nD.toNat d.treesL.toNat d.treesD.toNat d.npostfix d.ndirect (A.size + padOf A.size) ∧
      T.size ≤ A.size + tabMax d.nL.toNat d.nI.toNat d.nD.toNat }) :
    (hdrOfArena A d hf lTriv ht hok R).arena.size ≤ A.size + tabMax d.nL.toNat d.nI.toNat d.nD.toNat ∧
      (hdrOfArena A d hf lTriv ht hok R).arenaCap = d.arenaCap := by
  obtain ⟨T, _, _, hsz⟩ := R
  exact ⟨hsz, rfl⟩

/-- The header made from a header that was read keeps its arena within its reservation. -/
theorem mkHdr_size {d : Done} {g : Gh} {mlen : UInt64} (hu : Upto d g 10) (h : ∃ g, Upto d g 10) :
    (mkHdr d mlen h).arena.size ≤ (mkHdr d mlen h).arenaCap.toNat := by
  unfold mkHdr
  split
  rename_i A d0 hT
  have hb := takeArena_back hT
  subst hb
  unfold mkHdrOf
  dsimp only
  refine Nat.le_trans (hdrOfArena_size _).1 ?_
  rw [(hdrOfArena_size _).2]
  have hs : ∀ np nd h1 h2, (writeDsh np nd A h1 h2).size = A.size := fun _ _ _ _ => writeDsh_spec.1
  rw [hs]
  have hL := hu.cat .L (by decide)
  have hD := hu.cat .D (by decide)
  have hI := hu.cat .I (by decide)
  have hLn : d0.nL.toNat = g.m.literal.n := hL.n
  have hDn : d0.nD.toNat = g.m.distance.n := hD.n
  have hIn : d0.nI.toNat = g.m.insertCopy.n := hI.n
  have hfin := hu.fin rfl
  dsimp only at hfin
  have htm : tabMaxOf g = tabMax d0.nL.toNat d0.nI.toNat d0.nD.toNat := by
    unfold tabMaxOf
    rw [hLn, hIn, hDn, Nat.min_eq_left (show g.m.literal.n ≤ 256 from hL.wf.2.1),
      Nat.min_eq_left (show g.m.insertCopy.n ≤ 256 from hI.wf.2.1),
      Nat.min_eq_left (show g.m.distance.n ≤ 256 from hD.wf.2.1)]
  rw [htm] at hfin
  omega

end Brotli.Decoder
