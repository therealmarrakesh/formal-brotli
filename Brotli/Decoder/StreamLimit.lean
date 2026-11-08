module

public import Brotli.Decoder.StreamCall

@[expose] public section

/-!
# The limit changes nothing but whether the decoder stops

The decoder reads the memory limit only where it checks it: the room left for the window at WBITS, and the room left for a
header's tables when the groups' tables are reserved. Everywhere else a state's limit, and its header's table room, are
carried along unread.
So two states that differ only in those two fields step alike, until one of them reports the limit.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### A header's table room -/

/-- A header machine's state with another table room. -/
def hdSet (st : Hd) (a : UInt64) : Hd := { st with d := { st.d with arenaMax := a } }

theorem setN_am (d : Done) (a : UInt64) (i : Cat) (n : UInt64) :
    ({ d with arenaMax := a } : Done).setN i n = { d.setN i n with arenaMax := a } := by
  cases i <;> rfl

theorem setCount_am (d : Done) (a : UInt64) (i : Cat) (n : UInt64) :
    ({ d with arenaMax := a } : Done).setCount i n = { d.setCount i n with arenaMax := a } := by
  cases i <;> rfl

theorem setBaseT_am (d : Done) (a : UInt64) (i : Cat) (b : USize) :
    ({ d with arenaMax := a } : Done).setBaseT i b = { d.setBaseT i b with arenaMax := a } := by
  cases i <;> rfl

theorem setBaseC_am (d : Done) (a : UInt64) (i : Cat) (b : USize) :
    ({ d with arenaMax := a } : Done).setBaseC i b = { d.setBaseC i b with arenaMax := a } := by
  cases i <;> rfl

theorem setBases_am (d : Done) (a : UInt64) (k : CK) (b : ByteArray) :
    ({ d with arenaMax := a } : Done).setBases k b = { d.setBases k b with arenaMax := a } := by
  cases k <;> rfl

theorem nOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).nOf i = d.nOf i := by
  cases i <;> rfl

theorem countOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).countOf i = d.countOf i := by
  cases i <;> rfl

theorem baseTOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).baseTOf i = d.baseTOf i := by
  cases i <;> rfl

theorem baseCOf_am (d : Done) (a : UInt64) (i : Cat) : ({ d with arenaMax := a } : Done).baseCOf i = d.baseCOf i := by
  cases i <;> rfl

theorem basesOf_am (d : Done) (a : UInt64) (k : CK) : ({ d with arenaMax := a } : Done).basesOf k = d.basesOf k := by
  cases k <;> rfl

/-- Settles a step that neither reads nor sets the table room: split every branch, and match the two sides. -/
macro "lim_tac" : tactic =>
  `(tactic| ((repeat' split) <;> (try simp_all [hdSet, setN_am, setCount_am, setBaseT_am, setBaseC_am, setBases_am, nOf_am,
    countOf_am, baseTOf_am, baseCOf_am, basesOf_am]) <;> (try rfl)))

/-- What two header steps from states that differ only in their table room leave: one of them ran out of room, or they
again differ only in their table room. -/
def HLim (r1 r2 : Hd) : Prop := r1.status = .memory ∨ r2.status = .memory ∨ ∃ a, r1 = hdSet r2 a

theorem HLim.same {r1 r2 : Hd} {a : UInt64} (h : r1 = hdSet r2 a) : HLim r1 r2 := Or.inr (Or.inr ⟨a, h⟩)

/-- Both sides take the same branch of a dependent `if`. -/
theorem dite_hd (a : UInt64) {c : Prop} [Decidable c] {x x' : c → Hd} {y y' : ¬ c → Hd} (hx : ∀ h, x h = hdSet (x' h) a)
    (hy : ∀ h, y h = hdSet (y' h) a) : dite c x y = hdSet (dite c x' y') a := by
  by_cases h : c
  · rw [dite_eq_left h, dite_eq_left h]
    exact hx h
  · rw [dite_eq_right h, dite_eq_right h]
    exact hy h

theorem ite_hd (a : UInt64) {c : Prop} [Decidable c] {x x' y y' : Hd} (hx : c → x = hdSet x' a) (hy : ¬ c → y = hdSet y' a) :
    (if c then x else y) = hdSet (if c then x' else y') a := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
    exact hx h
  · rw [ite_eq_right h, ite_eq_right h]
    exact hy h

theorem dite_lim {c : Prop} [Decidable c] {x x' : c → Hd} {y y' : ¬ c → Hd} (hx : ∀ h, HLim (x h) (x' h))
    (hy : ∀ h, HLim (y h) (y' h)) : HLim (dite c x y) (dite c x' y') := by
  by_cases h : c
  · rw [dite_eq_left h, dite_eq_left h]
    exact hx h
  · rw [dite_eq_right h, dite_eq_right h]
    exact hy h
section
variable (st : Hd) (a : UInt64) (pos : USize)

theorem catMoveOn_lim : catMoveOn (hdSet st a) = hdSet (catMoveOn st) a := by
  simp only [catMoveOn]; lim_tac

theorem ckFinish_lim : ckFinish (hdSet st a) = hdSet (ckFinish st) a := by
  simp only [ckFinish]; lim_tac

theorem installTable_lim (base : UInt64) (hi : InstallOk st.role st.idx st.fill) :
    installTable (hdSet st a) base hi = hdSet (installTable st base hi) a := by
  have hr4 : st.role = .type ∨ st.role = .count ∨ st.role = .codes ∨ st.role = .map := by
    cases st.role <;> simp
  show installTable { st with d := { st.d with arenaMax := a } } base hi = _
  rcases hr4 with hr | hr | hr | hr
  · rw [installTable_type (st := { st with d := { st.d with arenaMax := a } }) hr, installTable_type hr]
    lim_tac
  · rw [installTable_count (st := { st with d := { st.d with arenaMax := a } }) hr, installTable_count hr]
    lim_tac
  · rw [installTable_codes (st := { st with d := { st.d with arenaMax := a } }) hr, installTable_codes hr]
    simp only [clearFill]
    lim_tac
  · rw [installTable_map (st := { st with d := { st.d with arenaMax := a } }) hr, installTable_map hr]
    rfl

theorem clFinish_lim (h1 : ∃ acc, ClDone (hdSet st a) acc) (h2 : ∃ acc, ClDone st acc) :
    clFinish (hdSet st a) h1 = hdSet (clFinish st h2) a := rfl

theorem mapTableDone_lim (t : ByteArray) (hf : t.size < 2 ^ 32 ∧ TableFits t (USize.ofNat 0).toNat) :
    mapTableDone (hdSet st a) t hf = hdSet (mapTableDone st t hf) a := by
  simp only [mapTableDone, mapSizeFast]; lim_tac

theorem growSingle_lim (sym : UInt64) (h1 : (hdSet st a).d.arena.size + 2672 < 2 ^ 32 ∧ (hdSet st a).d.arena.size % 2 = 0)
    (h2 : st.d.arena.size + 2672 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0) :
    growSingle (hdSet st a) sym h1 = hdSet (growSingle st sym h2) a := by
  simp only [growSingle, clearDone, clearArena, hdSet]

theorem growLens_lim (h1 : ∃ L, BuildArgs (hdSet st a).d.arena (hdSet st a).head (hdSet st a).next L)
    (h2 : ∃ L, BuildArgs st.d.arena st.head st.next L) : growLens (hdSet st a) h1 = hdSet (growLens st h2) a := by
  simp only [growLens, clearDone, clearArena, hdSet]

/-- Two checks of the room that may disagree: the states agree when both pass, and a failed one reports the limit. -/
private theorem check_lim {c1 c2 : Prop} [Decidable c1] [Decidable c2] {x1 x2 y1 y2 : Hd} (h : c1 → c2 → x1 = hdSet x2 a)
    (hy1 : y1.status = .memory) (hy2 : y2.status = .memory) : HLim (if c1 then x1 else y1) (if c2 then x2 else y2) := by
  by_cases h1 : c1 <;> by_cases h2 : c2 <;> simp only [h1, h2, ↓reduceIte]
  · exact HLim.same (h h1 h2)
  · exact Or.inr (Or.inl hy2)
  · exact Or.inl hy1
  · exact Or.inl hy1

theorem mapFinish_lim (n : UInt64) (map : ByteArray) : HLim (mapFinish (hdSet st a) n map) (mapFinish st n map) := by
  unfold mapFinish
  rw [show (hdSet st a).isL = st.isL from rfl]
  cases st.isL with
  | true => exact HLim.same (a := a) rfl
  | false =>
    dsimp only
    exact check_lim a (fun _ _ => rfl) rfl rfl

theorem mapFinish_lim' {L : Hd} (h : L = hdSet st a) (n : UInt64) (map map' : ByteArray) (hm : map = map') :
    HLim (mapFinish L n map) (mapFinish st n map') := h ▸ hm ▸ mapFinish_lim st a n map

theorem installTable_lim' {S S' : Hd} (h : S = hdSet S' a) (base : UInt64) (hi : InstallOk S.role S.idx S.fill)
    (hi' : InstallOk S'.role S'.idx S'.fill) : installTable S base hi = hdSet (installTable S' base hi') a := by
  subst h
  exact installTable_lim S' a base hi'

theorem tableDone_lim (single : Bool) (sym : UInt64) (ha1 : TableArgs (hdSet st a).size (hdSet st a).head (hdSet st a).next single sym)
    (ha2 : TableArgs st.size st.head st.next single sym) (hi : InstallOk st.role st.idx st.fill)
    (har1 : (hdSet st a).d.arena.size % 2 = 0 ∧ (hdSet st a).d.arena.size + 2672 < 2 ^ 32)
    (har2 : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32) :
    tableDone (hdSet st a) single sym ha1 hi har1 = hdSet (tableDone st single sym ha2 hi har2) a := by
  unfold tableDone
  have er : (hdSet st a).role = st.role := rfl
  have ea : (hdSet st a).d.arena = st.d.arena := rfl
  simp only [er, ea]
  cases hr : st.role with
  | map => dsimp only; exact mapTableDone_lim st a _ _
  | type | count | codes =>
    dsimp only
    by_cases hs : single = true
    · rw [dite_eq_left hs, dite_eq_left hs]
      exact installTable_lim' a (growSingle_lim st a sym _ _) _ _ _
    · rw [dite_eq_right hs, dite_eq_right hs]
      exact installTable_lim' a (growLens_lim st a _ _) _ _ _

theorem stepHCat_lim : stepHCat (hdSet st a) pos = hdSet (stepHCat st pos) a := by
  simp only [stepHCat, markH, catMoveOn]; lim_tac

theorem stepHFirst_lim (hf : st.d.arena.size < 2 ^ 32 ∧ TableFits st.d.arena (st.d.baseCOf st.cat).toNat) :
    stepHFirst (hdSet st a) pos hf = hdSet (stepHFirst st pos hf) a := by
  show stepHFirst { st with d := { st.d with arenaMax := a } } pos hf = _
  simp only [stepHFirst, markH, catMoveOn, baseCOf_am]; lim_tac

theorem stepHNp_lim : stepHNp (hdSet st a) pos = hdSet (stepHNp st pos) a := by
  simp only [stepHNp, markH]; lim_tac

theorem stepHModes_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .modes) :
    stepHModes (hdSet st a) pos h1 ht = hdSet (stepHModes st pos h2 ht) a := by
  show stepHModes { st with d := { st.d with arenaMax := a } } pos h1 ht = _
  simp only [stepHModes, markH, clearFill]; lim_tac

theorem stepHTrees_lim : HLim (stepHTrees (hdSet st a) pos) (stepHTrees st pos) := by
  show HLim (stepHTrees { st with d := { st.d with arenaMax := a } } pos) _
  simp only [stepHTrees, markH]
  (repeat' split) <;> first | exact mapFinish_lim' _ a (by rfl) _ _ _ (by rfl) | exact HLim.same (a := a) (by rfl) | contradiction | (simp_all [hdSet]; done)

theorem stepHRlemax_lim : stepHRlemax (hdSet st a) pos = hdSet (stepHRlemax st pos) a := by
  simp only [stepHRlemax, markH]; lim_tac

theorem stepHVals_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .vals) :
    stepHVals (hdSet st a) pos h1 ht = hdSet (stepHVals st pos h2 ht) a := by
  show stepHVals { st with d := { st.d with arenaMax := a } } pos h1 ht = _
  have e : mapSymFastT { st with d := { st.d with arenaMax := a } } h1 ht = mapSymFastT st h2 ht := rfl
  unfold stepHVals
  rw [e]
  simp only [imtfRunK_eq]
  generalize mapSymFastT st h2 ht = rr
  obtain ⟨⟨rs, rw, rc, ra, rb, rcc, rd, re⟩, hr⟩ := rr
  cases rs <;> (try simp only [markH, clearMap]) <;> lim_tac

theorem stepHImtf_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .imtf) :
    HLim (stepHImtf (hdSet st a) pos h1 ht) (stepHImtf st pos h2 ht) := by
  show HLim (stepHImtf { st with d := { st.d with arenaMax := a } } pos h1 ht) _
  simp only [stepHImtf, markH, clearMap]
  (repeat' split) <;> first | exact mapFinish_lim' _ a (by rfl) _ _ _ (by rfl) | exact HLim.same (a := a) (by rfl) | contradiction | (simp_all [hdSet]; done)

theorem stepHCodes_lim : stepHCodes (hdSet st a) pos = hdSet (stepHCodes st pos) a := by
  simp only [stepHCodes, ckFinish, ckSizeFast]; lim_tac

theorem clFinish_lim' {L : Hd} (h : L = hdSet st a) (h1 : ∃ acc, ClDone L acc) (h2 : ∃ acc, ClDone st acc) :
    clFinish L h1 = hdSet (clFinish st h2) a := by
  subst h
  exact clFinish_lim st a h1 h2

theorem tableDone_lim' {L : Hd} (h : L = hdSet st a) (single : Bool) (sym : UInt64) (ha1 : TableArgs L.size L.head L.next single sym)
    (ha2 : TableArgs st.size st.head st.next single sym) (hi1 : InstallOk L.role L.idx L.fill) (hi2 : InstallOk st.role st.idx st.fill)
    (har1 : L.d.arena.size % 2 = 0 ∧ L.d.arena.size + 2672 < 2 ^ 32)
    (har2 : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32) :
    tableDone L single sym ha1 hi1 har1 = hdSet (tableDone st single sym ha2 hi2 har2) a := by
  subst h
  exact tableDone_lim st a single sym ha1 ha2 hi2 har1 har2

theorem stepHClens_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .clens) :
    stepHClens (hdSet st a) pos h1 ht = hdSet (stepHClens st pos h2 ht) a := by
  show stepHClens { st with d := { st.d with arenaMax := a } } pos h1 ht = _
  simp only [stepHClens, markH, clearClLens]
  (repeat' split) <;> first | exact clFinish_lim' _ a (by rfl) _ _ | rfl | (simp_all [hdSet]; done)

theorem simpleTable_lim {r : Rd} (h1 : SimpleRead (hdSet st a).size r) (h2 : SimpleRead st.size r) (he : ¬ r.e = 0)
    (hi1 : InstallOk (hdSet st a).role (hdSet st a).idx (hdSet st a).fill) (hi2 : InstallOk st.role st.idx st.fill)
    (har1 : (hdSet st a).d.arena.size % 2 = 0 ∧ (hdSet st a).d.arena.size + 2672 < 2 ^ 32)
    (har2 : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32) :
    simpleTable (hdSet st a) r pos h1 he hi1 har1 = hdSet (simpleTable st r pos h2 he hi2 har2) a := by
  unfold simpleTable
  exact tableDone_lim' (simpleLists st r pos h2.fits) a rfl _ _ _ _ _ _ _ _

theorem stepHCode_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .code) :
    HLim (stepHCode (hdSet st a) pos h1 ht) (stepHCode st pos h2 ht) := by
  show HLim (stepHCode { st with d := { st.d with arenaMax := a } } pos h1 ht) _
  simp only [stepHCode, markH, simpleFastT]
  (repeat' (first | (refine dite_lim (fun _ => ?_) (fun _ => ?_)) | split)) <;> first
    | exact HLim.same (tableDone_lim' _ a (by rfl) _ _ _ _ _ _ _ _) | exact HLim.same (a := a) (by rfl)
    | (refine HLim.same (a := a) ?_; exact simpleTable_lim _ _ _ _ _ _ _ _ _ _) | (simp_all [hdSet]; done)

theorem symsRep_lim {r : Rd} (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .syms)
    (hl1 : ¬ (hdSet st a).ln = (hdSet st a).size) (hl2 : ¬ st.ln = st.size) (new old : UInt64) :
    symsRep (hdSet st a) pos h1 ht hl1 r new old = hdSet (symsRep st pos h2 ht hl2 r new old) a := by
  unfold symsRep
  refine dite_hd a (fun _ => rfl) (fun _ => ?_)
  exact ite_hd a (fun _ => rfl) (fun _ => ite_hd a (fun _ => rfl) (fun _ => rfl))

theorem symsOk_lim {r : Rd} (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .syms)
    (hl1 : ¬ (hdSet st a).ln = (hdSet st a).size) (hl2 : ¬ st.ln = st.size) :
    symsOk (hdSet st a) pos h1 ht hl1 r = hdSet (symsOk st pos h2 ht hl2 r) a := by
  unfold symsOk
  refine dite_hd a (fun _ => ?_) (fun _ => symsRep_lim st a pos h1 h2 ht hl1 hl2 _ _)
  exact ite_hd a (fun _ => rfl) (fun _ => ite_hd a (fun _ => rfl) (fun _ => rfl))

theorem stepHSyms_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) (ht : st.tag = .syms) :
    HLim (stepHSyms (hdSet st a) pos h1 ht) (stepHSyms st pos h2 ht) := by
  unfold stepHSyms
  refine dite_lim (fun _ => HLim.same (tableDone_lim' _ a (by rfl) _ _ _ _ _ _ _ _)) (fun _ => ?_)
  refine HLim.same (a := a) (dite_hd a (fun _ => rfl) (fun hl => ?_))
  have hr : lenSymFast (hdSet st a).clt.t (USize.ofNat 0) (hdSet st a).clt.fits (hdSet st a).clt.h32
      ⟨(hdSet st a).word, (hdSet st a).count⟩ = lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ := rfl
  dsimp only
  rw [hr]
  split <;> rename_i hs <;> simp only [hs] <;> first | rfl | exact symsOk_lim st a pos h1 h2 ht _ _

theorem stepAtH_lim (h1 : ∃ g p, HRel (hdSet st a) g p) (h2 : ∃ g p, HRel st g p) :
    HLim (stepAtH (hdSet st a) pos h1) (stepAtH st pos h2) := by
  cases ht : st.tag with
  | cat => rw [stepAtH_cat (st := hdSet st a) ht, stepAtH_cat ht]; exact HLim.same (stepHCat_lim st a pos)
  | code => rw [stepAtH_code (st := hdSet st a) ht, stepAtH_code ht]; exact stepHCode_lim st a pos h1 h2 ht
  | clens => rw [stepAtH_clens (st := hdSet st a) ht, stepAtH_clens ht]; exact HLim.same (stepHClens_lim st a pos _ _ ht)
  | syms => rw [stepAtH_syms (st := hdSet st a) ht, stepAtH_syms ht]; exact stepHSyms_lim st a pos h1 h2 ht
  | first => rw [stepAtH_first (st := hdSet st a) ht, stepAtH_first ht]; exact HLim.same (stepHFirst_lim st a pos _)
  | np => rw [stepAtH_np (st := hdSet st a) ht, stepAtH_np ht]; exact HLim.same (stepHNp_lim st a pos)
  | modes => rw [stepAtH_modes (st := hdSet st a) ht, stepAtH_modes ht]; exact HLim.same (stepHModes_lim st a pos h1 h2 ht)
  | trees => rw [stepAtH_trees (st := hdSet st a) ht, stepAtH_trees ht]; exact stepHTrees_lim st a pos
  | rlemax => rw [stepAtH_rlemax (st := hdSet st a) ht, stepAtH_rlemax ht]; exact HLim.same (stepHRlemax_lim st a pos)
  | vals => rw [stepAtH_vals (st := hdSet st a) ht, stepAtH_vals ht]; exact HLim.same (stepHVals_lim st a pos h1 h2 ht)
  | imtf => rw [stepAtH_imtf (st := hdSet st a) ht, stepAtH_imtf ht]; exact stepHImtf_lim st a pos h1 h2 ht
  | codes => rw [stepAtH_codes (st := hdSet st a) ht, stepAtH_codes ht]; exact HLim.same (stepHCodes_lim st a pos)
  | ready => rw [stepAtH_ready (st := hdSet st a) ht, stepAtH_ready ht]; exact HLim.same (a := a) rfl

theorem stepAtH_lim' {L : Hd} (h : L = hdSet st a) (h1 : ∃ g p, HRel L g p) (h2 : ∃ g p, HRel st g p) :
    HLim (stepAtH L pos h1) (stepAtH st pos h2) := by
  subst h
  exact stepAtH_lim st a pos h1 h2

theorem stepH_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) (h1 : HIn (hdSet st a))
    (h2 : HIn st) (hp : pos.toNat ≤ stop.toNat) :
    HLim (stepH ar stop hs (hdSet st a) pos h1 hp) (stepH ar stop hs st pos h2 hp) := by
  unfold stepH refillH
  dsimp only
  exact stepAtH_lim' _ a _ (by rfl) _ _

end

/-! ### A stream's limit -/

/-- A stream state with another limit and table room. -/
def decSet (D : Dec) (l a : UInt64) : Dec := { D with limit := l, hd := hdSet D.hd a }

/-- What two stream steps from states that differ only in their limit and table room leave: one of them reports the limit,
or they again differ only in those. -/
def DLim (r1 r2 : Dec) : Prop := r1.status = .memory ∨ r2.status = .memory ∨ ∃ l a, r1 = decSet r2 l a

theorem DLim.same {r1 r2 : Dec} {l a : UInt64} (h : r1 = decSet r2 l a) : DLim r1 r2 := Or.inr (Or.inr ⟨l, a, h⟩)

section
variable (D : Dec) (l a : UInt64) (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) (pos : USize)

theorem stepDSkip_lim : stepDSkip stop (decSet D l a) pos = decSet (stepDSkip stop D pos) l a := by
  show stepDSkip stop { D with limit := l, hd := hdSet D.hd a } pos = _
  simp only [stepDSkip, moveOn]
  (repeat' split) <;> first | rfl | contradiction | (simp_all [decSet, hdSet]; done)

theorem stepDCmds_lim (h : CmdInv D.H D.k stop D.cmd pos) :
    stepDCmds ar stop hs (decSet D l a) pos h = decSet (stepDCmds ar stop hs D pos h) l a := by
  show stepDCmds ar stop hs { D with limit := l, hd := hdSet D.hd a } pos h = _
  simp only [stepDCmds, takeCmd, clearCmd]
  cases (runCmdF D.H D.k ar stop hs cmdBudget D.cmd pos h).status <;>
    first | rfl | (by_cases hc : seenOk (runCmdF D.H D.k ar stop hs cmdBudget D.cmd pos h) D.H.nL D.H.nI D.H.nD = true <;>
      simp only [hc, ↓reduceIte] <;> rfl)

theorem stepDRaw_lim : stepDRaw ar stop hs (decSet D l a) pos = decSet (stepDRaw ar stop hs D pos) l a := by
  show stepDRaw ar stop hs { D with limit := l, hd := hdSet D.hd a } pos = _
  simp only [stepDRaw, takeRing, moveOn, clearCmd, rawFinish]
  (repeat' split) <;> first | rfl | contradiction | (simp_all [decSet, hdSet]; done)

theorem metaGo_lim (r : Rd) (p : USize) : DLim (metaGo (decSet D l a) D.cmd r p) (metaGo D D.cmd r p) := by
  show DLim (metaGo { D with limit := l, hd := hdSet D.hd a } D.cmd r p) _
  unfold metaGo
  dsimp only
  by_cases h0 : r.a = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    exact DLim.same (l := l) (a := a) (by rfl)
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h1 : r.a = 1
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases hz : r.buf.peek (r.count &&& 7) = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
      exact DLim.same (l := l) (a := a) (by rfl)
    · rw [ite_eq_right hz, ite_eq_right hz]
      exact DLim.same (l := l) (a := a) (by rfl)
  rw [ite_eq_right h1, ite_eq_right h1]
  by_cases hu : (r.d != 0) = true
  · rw [ite_eq_left hu, ite_eq_left hu]
    by_cases hz : r.buf.peek (r.count &&& 7) = 0
    · rw [ite_eq_left hz, ite_eq_left hz]
      by_cases hr : D.cmd.ring.size = 0
      · rw [ite_eq_left hr, ite_eq_left hr]
        by_cases c1 : (1 : UInt64) <<< D.k.toUInt64 ≤ l
        · rw [ite_eq_left c1]
          by_cases c2 : (1 : UInt64) <<< D.k.toUInt64 ≤ D.limit
          · rw [ite_eq_left c2]
            exact DLim.same (l := l - (1 : UInt64) <<< D.k.toUInt64) (a := a) (by rfl)
          · rw [ite_eq_right c2]
            exact Or.inr (Or.inl rfl)
        · rw [ite_eq_right c1]
          exact Or.inl rfl
      · rw [ite_eq_right hr, ite_eq_right hr]
        exact DLim.same (l := l) (a := a) (by rfl)
    · rw [ite_eq_right hz, ite_eq_right hz]
      exact DLim.same (l := l) (a := a) (by rfl)
  · rw [ite_eq_right hu, ite_eq_right hu]
    by_cases hr : D.cmd.ring.size = 0
    · rw [ite_eq_left hr, ite_eq_left hr]
      by_cases c1 : (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c ≤ l
      · rw [ite_eq_left c1]
        by_cases c2 : (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c ≤ D.limit
        · rw [ite_eq_left c2]
          exact DLim.same (l := l - (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c)
            (a := l - (1 : UInt64) <<< allocBits D.k (r.b != 0) r.c) (by rfl)
        · rw [ite_eq_right c2]
          exact Or.inr (Or.inl rfl)
      · rw [ite_eq_right c1]
        exact Or.inl rfl
    · rw [ite_eq_right hr, ite_eq_right hr]
      exact DLim.same (l := l) (a := l) (by rfl)

theorem stepDMeta_lim : DLim (stepDMeta ar stop hs (decSet D l a) pos) (stepDMeta ar stop hs D pos) := by
  show DLim (stepDMeta ar stop hs { D with limit := l, hd := hdSet D.hd a } pos) _
  unfold stepDMeta
  by_cases h0 : D.cmd.pend = 0
  · rw [ite_eq_left (show ({ D with limit := l, hd := hdSet D.hd a } : Dec).cmd.pend = 0 from h0), ite_eq_left h0]
    by_cases hp : pos ≤ stop
    · rw [dite_eq_left hp, dite_eq_left hp]
      dsimp only
      generalize refill D.cmd.word D.cmd.count ar pos stop hs _ = rf
      generalize metaStartFast ⟨rf.word, rf.count⟩ = r
      cases hr : r.status with
      | short => exact DLim.same (l := l) (a := a) (by rfl)
      | bad => exact DLim.same (l := l) (a := a) (by rfl)
      | ok => exact metaGo_lim D l a r rf.pos
    · rw [dite_eq_right hp, dite_eq_right hp]
      exact DLim.same (l := l) (a := a) (by rfl)
  · rw [ite_eq_right (show ¬ ({ D with limit := l, hd := hdSet D.hd a } : Dec).cmd.pend = 0 from h0), ite_eq_right h0]
    exact DLim.same (l := l) (a := a) (by rfl)

theorem stepDWbits_lim : DLim (stepDWbits ar stop hs (decSet D l a) pos) (stepDWbits ar stop hs D pos) := by
  show DLim (stepDWbits ar stop hs { D with limit := l, hd := hdSet D.hd a } pos) _
  unfold stepDWbits
  by_cases hp : pos ≤ stop
  · rw [dite_eq_left hp, dite_eq_left hp]
    dsimp only
    split <;> exact DLim.same (l := l) (a := a) (by rfl)
  · rw [dite_eq_right hp, dite_eq_right hp]
    exact DLim.same (l := l) (a := a) (by rfl)

theorem stepDHdr_lim (hH1 : HIn (decSet D l a).hd) (hH2 : HIn D.hd) (hp : pos.toNat ≤ stop.toNat) :
    DLim (stepDHdr ar stop hs (decSet D l a) pos hH1 hp) (stepDHdr ar stop hs D pos hH2 hp) := by
  unfold stepDHdr takeHd clearHd
  dsimp only
  have hr : HLim (stepH ar stop hs (decSet D l a).hd pos hH1 hp) (stepH ar stop hs D.hd pos hH2 hp) :=
    stepH_lim D.hd a pos ar stop hs hH1 hH2 hp
  generalize e1 : stepHR ar stop hs (decSet D l a).hd pos hH1 hp = rr1
  generalize e2 : stepHR ar stop hs D.hd pos hH2 hp = rr2
  obtain ⟨r1, h1⟩ := rr1
  obtain ⟨r2, h2⟩ := rr2
  have v1 : r1 = stepH ar stop hs (decSet D l a).hd pos hH1 hp := by rw [← stepHR_val (h := hH1) (hp := hp), e1]
  have v2 : r2 = stepH ar stop hs D.hd pos hH2 hp := by rw [← stepHR_val (h := hH2) (hp := hp), e2]
  rw [← v1, ← v2] at hr
  unfold hdrNext
  dsimp only
  rcases hr with h | h | ⟨a', rfl⟩
  · exact Or.inl (by split <;> first | rfl | (rename_i s; exact absurd (h.symm.trans s) (fun e => HStatus.noConfusion e)))
  · exact Or.inr (Or.inl (by split <;> first | rfl | (rename_i s; exact absurd (h.symm.trans s) (fun e => HStatus.noConfusion e))))
  · split <;> rename_i s1 <;> split <;> rename_i s2 <;> first
      | exact absurd (s1.symm.trans s2) (fun e => HStatus.noConfusion e)
      | exact Or.inl rfl
      | exact DLim.same (l := l) (a := a') (by rfl)
      | exact DLim.same (l := l) (a := 0) (by rfl)

theorem stepD_lim (h1 : DInv stop (decSet D l a)) (h2 : DInv stop D) :
    DLim (stepD ar stop hs (decSet D l a) h1) (stepD ar stop hs D h2) := by
  cases ht : D.tag with
  | wbits =>
    rw [stepD_wbits (D := decSet D l a) ht, stepD_wbits ht]
    exact stepDWbits_lim D l a ar stop hs D.pos
  | mblock =>
    rw [stepD_mblock (D := decSet D l a) ht, stepD_mblock ht]
    exact stepDMeta_lim D l a ar stop hs D.pos
  | skip =>
    rw [stepD_skip (D := decSet D l a) ht, stepD_skip ht]
    exact DLim.same (stepDSkip_lim D l a stop D.pos)
  | raw =>
    rw [stepD_raw (D := decSet D l a) ht, stepD_raw ht]
    exact DLim.same (stepDRaw_lim D l a ar stop hs D.pos)
  | hdr =>
    rw [stepD_hdr (D := decSet D l a) ht, stepD_hdr ht]
    exact stepDHdr_lim D l a ar stop hs D.pos _ _ h2.2
  | cmds =>
    rw [stepD_cmds (D := decSet D l a) ht, stepD_cmds ht]
    exact DLim.same (stepDCmds_lim D l a ar stop hs D.pos (h2.cmd ht))
  | ended =>
    rw [stepD_ended (D := decSet D l a) ht, stepD_ended ht]
    exact DLim.same (l := l) (a := a) rfl

end

/-- The loop from two states that differ only in their limit and table room. -/
theorem runD_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) : ∀ (x : RunArg ar stop hs) (l a : UInt64)
    (h1 : DInv stop (decSet x.D l a)), DLim (runD ar stop hs (decSet x.D l a) h1) (runD ar stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf ar stop hs).induction with
  | _ x ih =>
    intro l a h1
    rw [runD, runD]
    by_cases he : x.D.tag = .ended
    · rw [dite_eq_left (show (decSet x.D l a).tag = .ended from he), dite_eq_left he]
      exact DLim.same (l := l) (a := a) rfl
    · rw [dite_eq_right (show ¬ (decSet x.D l a).tag = .ended from he), dite_eq_right he]
      dsimp only
      have hs1 := stepD_lim x.D l a ar stop hs h1 x.inv
      rcases hs1 with h | h | ⟨l', a', e⟩
      · rw [dite_eq_right (show ¬ (stepD ar stop hs (decSet x.D l a) h1).status = .next by rw [h]; exact fun e => DStatus.noConfusion e)]
        exact Or.inl h
      · rw [dite_eq_right (show ¬ (stepD ar stop hs x.D x.inv).status = .next by rw [h]; exact fun e => DStatus.noConfusion e)]
        exact Or.inr (Or.inl h)
      · by_cases hn : (stepD ar stop hs x.D x.inv).status = .next
        · have hn1 : (stepD ar stop hs (decSet x.D l a) h1).status = .next := by rw [e]; exact hn
          rw [dite_eq_left hn1, dite_eq_left hn]
          have := ih ⟨stepD ar stop hs x.D x.inv, x.inv.step he hn⟩ ⟨he, hn, rfl⟩ l' a' (by rw [← e]; exact h1.step he hn1)
          simp only [e] at this ⊢
          exact this
        · have hn1 : ¬ (stepD ar stop hs (decSet x.D l a) h1).status = .next := by rw [e]; exact hn
          rw [dite_eq_right hn1, dite_eq_right hn]
          exact DLim.same e

/-- What two calls from states that differ only in their limit and table room leave, as a caller sees it. -/
def OLim (o1 o2 : Out) : Prop :=
  o1.status = .memoryLimit ∨ o2.status = .memoryLimit ∨
    (o1.status = o2.status ∧ o1.buf = o2.buf ∧ o1.pos = o2.pos ∧ ∃ l a, o1.D = decSet o2.D l a)

theorem OLim.same {o1 o2 : Out} {l a : UInt64} (hs : o1.status = o2.status) (hb : o1.buf = o2.buf) (hp : o1.pos = o2.pos)
    (hD : o1.D = decSet o2.D l a) : OLim o1 o2 := Or.inr (Or.inr ⟨hs, hb, hp, l, a, hD⟩)

theorem deadD_dec : deadD = decSet deadD 0 0 := rfl

theorem flushD_lim (D : Dec) (l a : UInt64) (buf : ByteArray) (space : Nat) :
    flushD (decSet D l a) buf space = ⟨decSet (flushD D buf space).D l a, (flushD D buf space).buf, (flushD D buf space).space⟩ := rfl

theorem endCheck_lim (D : Dec) (l a : UInt64) (stop : USize) (final : Bool) (buf : ByteArray) :
    OLim (endCheck (decSet D l a) stop final buf) (endCheck D stop final buf) := by
  show OLim (endCheck { D with limit := l, hd := hdSet D.hd a } stop final buf) _
  simp only [endCheck]
  (repeat' split) <;>
    first | exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl | exact OLim.same (l := l) (a := a) rfl rfl rfl rfl | contradiction |
      (simp_all [decSet, hdSet]; done)

theorem afterRun_lim {r1 r2 : Dec} (h : DLim r1 r2) (stop : USize) (final : Bool) (buf : ByteArray) (space : Nat) :
    OLim (afterRun r1 stop final buf space) (afterRun r2 stop final buf space) := by
  rcases h with h | h | ⟨l, a, rfl⟩
  · refine Or.inl ?_
    simp only [afterRun, h]
  · refine Or.inr (Or.inl ?_)
    simp only [afterRun, h]
  · unfold afterRun
    rw [show (decSet r2 l a).status = r2.status from rfl]
    cases r2.status with
    | bad => exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl
    | memory => exact Or.inl rfl
    | needsInput =>
      dsimp only
      rw [flushD_lim]
      dsimp only
      rw [show (decSet (flushD r2 buf space).D l a).cmd = (flushD r2 buf space).D.cmd from rfl]
      by_cases hp : (flushD r2 buf space).D.cmd.pend = 0
      · rw [ite_eq_left hp, ite_eq_left hp]
        cases final with
        | true => exact OLim.same (l := 0) (a := 0) rfl rfl rfl rfl
        | false => exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
      · rw [ite_eq_right hp, ite_eq_right hp]
        exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
    | next =>
      dsimp only
      rw [flushD_lim]
      dsimp only
      rw [show (decSet (flushD r2 buf space).D l a).cmd = (flushD r2 buf space).D.cmd from rfl]
      by_cases hp : (flushD r2 buf space).D.cmd.pend = 0
      · rw [ite_eq_left hp, ite_eq_left hp]
        exact endCheck_lim _ l a stop final _
      · rw [ite_eq_right hp, ite_eq_right hp]
        exact OLim.same (l := l) (a := a) rfl rfl rfl rfl
    | needsOutput => exact OLim.same (l := l) (a := a) rfl rfl rfl rfl

/-- A call from two states that differ only in their limit and table room. -/
theorem callD_lim (ar : ByteArray) (stop : USize) (hs : stop.toNat ≤ ar.size) (final : Bool) : ∀ (space : Nat) (D2 : Dec)
    (h2 : DInv stop D2) (D1 : Dec) (h1 : DInv stop D1) (buf : ByteArray), (∃ l a, D1 = decSet D2 l a) →
    OLim (callD ar stop hs final D1 h1 buf space) (callD ar stop hs final D2 h2 buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h2 D1 h1 buf ⟨l, a, hD⟩
    subst hD
    rw [callD, callD]
    have hr : DLim (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space))
        (runD ar stop hs (withCap D space) (h2.withCap space)) :=
      runD_lim ar stop hs ⟨withCap D space, h2.withCap space⟩ l a (h1.withCap space)
    rcases hr with h | h | ⟨l', a', e⟩
    · rw [dite_eq_right (show ¬ (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput by rw [h]; exact fun e => DStatus.noConfusion e)]
      exact Or.inl (by simp only [afterRun, h])
    · rw [dite_eq_right (show ¬ (runD ar stop hs (withCap D space) (h2.withCap space)).status = .needsOutput by rw [h]; exact fun e => DStatus.noConfusion e)]
      refine Or.inr (Or.inl ?_)
      simp only [afterRun, h]
    · by_cases hn : (runD ar stop hs (withCap D space) (h2.withCap space)).status = .needsOutput
      · have hn1 : (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput := by rw [e]; exact hn
        rw [dite_eq_left hn1, dite_eq_left hn]
        dsimp only
        have hf : flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space =
            ⟨decSet (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D l' a', (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).buf,
              (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space⟩ := by
          rw [e, flushD_lim]
        have hp : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).D.cmd.pend = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D.cmd.pend := by
          rw [hf]; rfl
        have hsp : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).space = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space := by
          rw [hf]
        have hb : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).buf = (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).buf := by
          rw [hf]
        have hDD : (flushD (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)) buf space).D = decSet (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D l' a' := by
          rw [hf]
        by_cases hq : (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).D.cmd.pend = 0
        · rw [ite_eq_left hq, ite_eq_left (hp.trans hq)]
          by_cases hl : (flushD (runD ar stop hs (withCap D space) (h2.withCap space)) buf space).space < space
          · rw [dite_eq_left hl, dite_eq_left (hsp ▸ hl)]
            rw [hb, hsp]
            exact ih _ hl _ _ _ _ _ ⟨l', a', hDD⟩
          · rw [dite_eq_right hl, dite_eq_right (show ¬ _ from hsp ▸ hl)]
            exact OLim.same (l := 0) (a := 0) rfl hb rfl rfl
        · rw [ite_eq_right hq, ite_eq_right (show ¬ _ from hp ▸ hq)]
          exact OLim.same (l := l') (a := a') rfl hb (by rw [hDD]; rfl) hDD
      · have hn1 : ¬ (runD ar stop hs (withCap (decSet D l a) space) (h1.withCap space)).status = .needsOutput := by rw [e]; exact hn
        rw [dite_eq_right hn1, dite_eq_right hn]
        exact afterRun_lim (DLim.same e) stop final buf space
