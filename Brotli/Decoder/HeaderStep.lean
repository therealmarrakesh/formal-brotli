import Brotli.Decoder.HeaderState

/-!
# The header's steps that read small fields

Each place in a header that needs no table built has a step here, with the theorem that it does what `HStepOk` says.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A small read in the spec's terms, applied to what follows it. -/
theorem ROk.run {A β : Type} {spec : List Bool → Option (A × List Bool)} {b b0 : BitBuffer} {room : Nat} {r : Rd} {v : A}
    {X : List Bool → Option β} {N : A → List Bool → Option β} (h : ROk spec b b0 room r v)
    (e : ∀ bs, X bs = spec bs >>= fun p => N p.1 p.2) :
    (r.status = .ok → r.buf.Wf ∧ ∀ f, X (b.held ++ f) = N v (r.buf.held ++ f)) ∧
    (r.status = .short → r.word = b0.word ∧ r.count = b0.count ∧ b.count.toNat < room ∧ X b.held = none) ∧
    (r.status = .bad → ∀ f, X (b.held ++ f) = none) := by
  refine ⟨fun s => ?_, fun s => ?_, fun s f => ?_⟩
  · obtain ⟨h1, h2⟩ := h.ok s
    exact ⟨h1, fun f => by rw [e, h2 f]; rfl⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.short s
    exact ⟨h1, h2, h3, by rw [e, h4]; rfl⟩
  · rw [e, h.bad s f]
    rfl

section
variable {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray} {stop : USize} {g : Gh} {p : HPhase}
  {st : Hd} {pos : USize}

/-- A short read of fewer than 56 bits means the chunk is used up. -/
theorem HStepOk.ofShortRead {X : Nat} (hrel : HRel st g p) (hfull : 56 < st.count.toNat ∨ pos = stop) (hX : X ≤ 56)
    (hc : st.count.toNat < X) (hn : hrest K g p (BitBuffer.mk st.word st.count).held = none) :
    HStepOk K a stop g p st pos (markH st pos .needsInput) :=
  HStepOk.ofShort hrel (hfull.resolve_left (by omega)) hn

/-- The bits after a read, whatever follows. -/
theorem avail_mk (word count : UInt64) (F : List Bool) (pos stop : USize) :
    availBits word count a pos stop F = (BitBuffer.mk word count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) := rfl

end

/-! ### Keeping what's settled -/

/-- Parts of the settled record that a category's facts depend on stay the same. -/
theorem CatOk.same {d d' : Done} {i : Cat} {c : BlockCategory} (h : CatOk d i c) (h1 : d'.arena = d.arena) (h2 : d'.nOf i = d.nOf i)
    (h3 : d'.countOf i = d.countOf i) (h4 : d'.baseTOf i = d.baseTOf i) (h5 : d'.baseCOf i = d.baseCOf i) : CatOk d' i c where
  n := by rw [h2]; exact h.n
  count := by rw [h3]; exact h.count
  rel := by rw [h1, h4, h5]; exact h.rel
  wf := h.wf
  tc := h.tc
  cc := h.cc

/-- What's settled at a stage among the categories. -/
theorem Upto.low {d : Done} {g : Gh} {n : Nat} (hn : n ≤ 3) (h1 : d.arena.size % 4 = 0) (h2 : d.arena.size ≤ d.arenaMax.toNat)
    (h3 : d.arenaMax.toNat + 132096 < 2 ^ 32) (hc : ∀ i, catIdx i < n → CatOk d i (g.catOf i)) : Upto d g n where
  four := h1
  le := h2
  max := h3
  cat := hc
  np h := absurd h (by omega)
  modes h := absurd h (by omega)
  lmap h := absurd h (by omega)
  dmap h := absurd h (by omega)
  codes k h := absurd h (by omega)

/-- Setting a category's fields keeps a stage up to it. -/
theorem Upto.setSame {d d' : Done} {g : Gh} {i : Cat} (h : Upto d g (catIdx i)) (h1 : d'.arena = d.arena) (hm : d'.arenaMax = d.arenaMax)
    (hs : ∀ j, j ≠ i → d'.nOf j = d.nOf j ∧ d'.countOf j = d.countOf j ∧ d'.baseTOf j = d.baseTOf j ∧ d'.baseCOf j = d.baseCOf j) :
    Upto d' g (catIdx i) := by
  refine Upto.low (by cases i <;> decide) (by rw [h1]; exact h.four) (by rw [h1, hm]; exact h.le) (by rw [hm]; exact h.max) ?_
  intro j hj
  have hne : j ≠ i := fun e => by subst e; omega
  obtain ⟨a, b, c, e⟩ := hs j hne
  exact (h.cat j hj).same h1 a b c e

/-- A category settled moves the stage on. -/
theorem Upto.catDone {d d' : Done} {g : Gh} {i : Cat} {c : BlockCategory} (h : Upto d g (catIdx i)) (h1 : d'.arena = d.arena)
    (hm : d'.arenaMax = d.arenaMax)
    (hs : ∀ j, j ≠ i → d'.nOf j = d.nOf j ∧ d'.countOf j = d.countOf j ∧ d'.baseTOf j = d.baseTOf j ∧ d'.baseCOf j = d.baseCOf j)
    (hc : CatOk d' i c) : Upto d' (g.setCat i c) (stageOf (catNextPhase i)) := by
  refine Upto.low (by cases i <;> decide) (by rw [h1]; exact h.four) (by rw [h1, hm]; exact h.le) (by rw [hm]; exact h.max) ?_
  intro j hj
  by_cases hne : j = i
  · subst hne
    cases j <;> exact hc
  · have hlt : catIdx j < catIdx i := by
      cases i <;> cases j <;> first | exact absurd rfl hne | simp only [catIdx, stageOf, catNextPhase] at hj ⊢ <;> omega
    obtain ⟨a, b, c', e⟩ := hs j hne
    have := (h.cat j hlt).same h1 a b c' e
    cases i <;> cases j <;> first | exact absurd rfl hne | exact this | (simp only [catIdx] at hlt; omega)

/-! ### Moving on from a category -/

/-- Moves to the place after a category. -/
@[inline] def catMoveOn (st : Hd) : Hd :=
  match st.cat with
  | .L => { st with tag := .cat, cat := .I }
  | .I => { st with tag := .cat, cat := .D }
  | .D => { st with tag := .np }

theorem catMoveOn_spec (s : Hd) : (catMoveOn s).word = s.word ∧ (catMoveOn s).count = s.count ∧ (catMoveOn s).pos = s.pos ∧
    (catMoveOn s).status = s.status ∧ (catMoveOn s).d = s.d := by
  unfold catMoveOn
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The fields besides a category's are the same after setting it. -/
private theorem setN_others (d : Done) (i : Cat) (v : UInt64) : ∀ j, j ≠ i →
    (d.setN i v).nOf j = d.nOf j ∧ (d.setN i v).countOf j = d.countOf j ∧ (d.setN i v).baseTOf j = d.baseTOf j ∧
      (d.setN i v).baseCOf j = d.baseCOf j := by
  intro j hne
  cases i <;> cases j <;> first | exact absurd rfl hne | exact ⟨rfl, rfl, rfl, rfl⟩

private theorem setCount_others (d : Done) (i : Cat) (v : UInt64) : ∀ j, j ≠ i →
    (d.setCount i v).nOf j = d.nOf j ∧ (d.setCount i v).countOf j = d.countOf j ∧ (d.setCount i v).baseTOf j = d.baseTOf j ∧
      (d.setCount i v).baseCOf j = d.baseCOf j := by
  intro j hne
  cases i <;> cases j <;> first | exact absurd rfl hne | exact ⟨rfl, rfl, rfl, rfl⟩

private theorem setN_nOf (d : Done) (i : Cat) (v : UInt64) : (d.setN i v).nOf i = v := by cases i <;> rfl

private theorem setCount_countOf (d : Done) (i : Cat) (v : UInt64) : (d.setCount i v).countOf i = v := by cases i <;> rfl

private theorem setN_arena (d : Done) (i : Cat) (v : UInt64) : (d.setN i v).arena = d.arena ∧ (d.setN i v).arenaMax = d.arenaMax := by
  cases i <;> exact ⟨rfl, rfl⟩

private theorem setCount_arena (d : Done) (i : Cat) (v : UInt64) :
    (d.setCount i v).arena = d.arena ∧ (d.setCount i v).arenaMax = d.arenaMax := by
  cases i <;> exact ⟨rfl, rfl⟩

private theorem setCount_nOf (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).nOf j = d.nOf j := by
  cases i <;> cases j <;> rfl

private theorem setN_countOf (d : Done) (i j : Cat) (v : UInt64) : (d.setN i v).countOf j = d.countOf j := by
  cases i <;> cases j <;> rfl

private theorem setN_baseT (d : Done) (i j : Cat) (v : UInt64) : (d.setN i v).baseTOf j = d.baseTOf j := by
  cases i <;> cases j <;> rfl

private theorem setN_baseC (d : Done) (i j : Cat) (v : UInt64) : (d.setN i v).baseCOf j = d.baseCOf j := by
  cases i <;> cases j <;> rfl

private theorem setCount_baseT (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).baseTOf j = d.baseTOf j := by
  cases i <;> cases j <;> rfl

private theorem setCount_baseC (d : Done) (i j : Cat) (v : UInt64) : (d.setCount i v).baseCOf j = d.baseCOf j := by
  cases i <;> cases j <;> rfl

/-- A state after a category stands for the next place. -/
theorem catMoveOn_rel {st : Hd} {g : Gh} {i : Cat} {c : BlockCategory} (hw : (BitBuffer.mk st.word st.count).Wf) (hi : st.cat = i)
    (hu : Upto st.d (g.setCat i c) (stageOf (catNextPhase i))) : HRel (catMoveOn st) (g.setCat i c) (catNextPhase i) := by
  unfold catMoveOn
  rw [hi]
  cases i
  · exact ⟨hw, hu, rfl, rfl⟩
  · exact ⟨hw, hu, rfl, rfl⟩
  · exact ⟨hw, hu, rfl⟩

/-! ### A category's number of block types -/

/-- The place at a category's number of block types. -/
def stepHCat (st : Hd) (pos : USize) : Hd :=
  let r := varLenFast ⟨st.word, st.count⟩
  match r.status with
  | .short => markH st pos .needsInput
  | .bad => markH st pos .bad
  | .ok =>
    let n := r.a
    if n < 2 then
      catMoveOn { st with
        word := r.word, count := r.count, pos := pos, status := .next
        d := (st.d.setN st.cat n).setCount st.cat 16777216 }
    else
      { st with
        word := r.word, count := r.count, pos := pos, status := .next, tag := .code, role := .type, size := n + 2
        d := st.d.setN st.cat n }

theorem stepHCat_ok {i : Cat} {st : Hd} {g : Gh} {pos : USize} {α : Type} {K : MetaBlockHeader → List Bool → Option α} {a : ByteArray}
    {stop : USize} (hrel : HRel st g (.cat i)) (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.cat i) st pos (stepHCat st pos) := by
  obtain ⟨hw, hu, ht, hi⟩ := hrel
  have hrel : HRel st g (.cat i) := ⟨hw, hu, ht, hi⟩
  have R := varLenFast_ok hw
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.cat i)) (N := fun v b =>
    if v < 2 then afterCat K g i ⟨v, .single 0, .single 0, 16777216⟩ b
    else hrest K g (.code (.type i v) (blockTypeAlphabetSize v)) b) (fun bs => hrest_cat K g i bs)
  have hval := R.ok
  unfold stepHCat
  dsimp only
  generalize varLenFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    exact HStepOk.ofShortRead (X := 11) hrel hfull (by omega) h3 h4
  | bad =>
    exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hrange := readVarLen_range ((hval hs).2 [])
    have hsh : (r.a < 2) ↔ r.a.toNat < 2 := UInt64.lt_iff_toNat_lt
    by_cases h2 : r.a < 2
    · rw [ite_eq_left h2]
      have h2' := hsh.mp h2
      have hd := setN_arena st.d st.cat r.a
      have hdc := setCount_arena (st.d.setN st.cat r.a) st.cat 16777216
      rw [← hi]
      generalize hc : (⟨r.a.toNat, .single 0, .single 0, 16777216⟩ : BlockCategory) = c
      have hcat : CatOk ((st.d.setN st.cat r.a).setCount st.cat 16777216) st.cat c := by
        subst hc
        refine ⟨?_, ?_, ?_, ?_, trivial, trivial⟩
        · rw [setCount_nOf, setN_nOf]
        · rw [setCount_countOf]
          rfl
        · exact ⟨fun h => absurd h (by simp only; omega), fun h => absurd h (by simp only; omega)⟩
        · exact ⟨hrange.1, hrange.2, fun h => absurd h (by simp only; omega)⟩
      subst hi
      have hup : Upto ((st.d.setN st.cat r.a).setCount st.cat 16777216) (g.setCat st.cat c) (stageOf (catNextPhase st.cat)) :=
        hu.catDone (hdc.1.trans hd.1) (hdc.2.trans hd.2) (fun j hj => by
          obtain ⟨e1, e2, e3, e4⟩ := setCount_others (st.d.setN st.cat r.a) st.cat 16777216 j hj
          obtain ⟨f1, f2, f3, f4⟩ := setN_others st.d st.cat r.a j hj
          exact ⟨e1.trans f1, e2.trans f2, e3.trans f3, e4.trans f4⟩) hcat
      have hrel2 := catMoveOn_rel (st := { st with
          word := r.word, count := r.count, pos := pos, status := .next
          d := (st.d.setN st.cat r.a).setCount st.cat 16777216 }) hw2 rfl hup
      obtain ⟨b1, b2, b3, b4, _⟩ := catMoveOn_spec { st with
          word := r.word, count := r.count, pos := pos, status := .next
          d := (st.d.setN st.cat r.a).setCount st.cat 16777216 }
      generalize catMoveOn { st with
          word := r.word, count := r.count, pos := pos, status := .next
          d := (st.d.setN st.cat r.a).setCount st.cat 16777216 } = r2 at hrel2 b1 b2 b3 b4 ⊢
      refine HStepOk.ofNext (hd := catNext_down _) b4 hrel2 (by rw [b3]; exact Nat.le_refl _) (by rw [b3]; exact hp) (fun F => ?_)
      have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      simp only [h2', ↓reduceIte]
      rw [← hc, afterCat_eq, avail_mk, b1, b2, b3]
      rfl
    · rw [ite_eq_right h2]
      have h2' : ¬ r.a.toNat < 2 := fun h => h2 (hsh.mpr h)
      have hd := setN_arena st.d st.cat r.a
      subst hi
      have hsz : (r.a + 2).toNat = r.a.toNat + 2 := by
        rw [UInt64.toNat_add, show (2 : UInt64).toNat = 2 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      refine HStepOk.ofNext (g' := g) (p' := .code (.type st.cat r.a.toNat) (blockTypeAlphabetSize r.a.toNat)) rfl
        ⟨hw2, hu.setSame hd.1 hd.2 (setN_others st.d st.cat r.a), rfl, ⟨hsz, by unfold blockTypeAlphabetSize; omega, by unfold blockTypeAlphabetSize; omega⟩,
          rfl, rfl, by show ((st.d.setN st.cat r.a).nOf st.cat).toNat = _; rw [setN_nOf], by omega, hrange.2, rfl⟩
        (Nat.le_refl _) hp (fun F => ?_)
      have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      simp only [h2', ↓reduceIte]
      rfl

end Brotli.Decoder
