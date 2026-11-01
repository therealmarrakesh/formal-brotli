import Brotli.Decoder.HeaderStep2

/-!
# The header's context maps and groups of codes, between their prefix codes

The places that start and end a context map or a group of codes.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

section
variable {α : Type} {K : HK α} {a : ByteArray} {stop : USize}

/-! ### A context map settled -/

/-- Moves on from a context map, with `n` trees. -/
def mapFinish (st : Hd) (n : UInt64) (map : ByteArray) : Hd :=
  match st.isL with
  | true => { st with tag := .trees, isL := false, d := { st.d with lMap := map, treesL := n } }
  | false =>
    { st with
      tag := .codes, ck := .L, idx := 0, left := st.d.treesL, fill := zeroBytes (4 * st.d.treesL.toNat)
      d := { st.d with dMap := map, treesD := n } }

theorem mapFinish_spec (st : Hd) (n : UInt64) (map : ByteArray) : (mapFinish st n map).word = st.word ∧
    (mapFinish st n map).count = st.count ∧ (mapFinish st n map).pos = st.pos ∧ (mapFinish st n map).status = st.status := by
  unfold mapFinish
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem Upto.lmapDone {d : Done} {g : Gh} (h : Upto d g 5) {b : ByteArray} {n : UInt64} {ntrees : Nat} {cmap : List Nat}
    (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256) (hm : MapOk b cmap (literalContextMapSize g.m.literal.n) ntrees) :
    Upto { d with lMap := b, treesL := n } (g.setMap true ntrees cmap) 6 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := ⟨hn, h1, h2, hm⟩
  dmap h := absurd h (by omega)
  codes _ h := absurd h (by omega)

theorem Upto.dmapDone {d : Done} {g : Gh} (h : Upto d g 6) {b : ByteArray} {n : UInt64} {ntrees : Nat} {cmap : List Nat}
    (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256) (hm : MapOk b cmap (distanceContextMapSize g.m.distance.n) ntrees) :
    Upto { d with dMap := b, treesD := n } (g.setMap false ntrees cmap) 7 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := h.lmap (by omega)
  dmap _ := ⟨hn, h1, h2, hm⟩
  codes _ h := absurd h (by cases ‹CK› <;> simp only [ckIdx] <;> omega)

theorem mapFinish_rel {st : Hd} {g : Gh} {isL : Bool} {n : UInt64} {ntrees : Nat} {map : ByteArray} {cmap : List Nat}
    (hw : (BitBuffer.mk st.word st.count).Wf) (hi : st.isL = isL) (hu : Upto st.d g (mapIdx isL))
    (hm : MapOk map cmap (mapSize g isL) ntrees) (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256) :
    HRel (mapFinish st n map) (g.setMap isL ntrees cmap) (mapNextPhase (g.setMap isL ntrees cmap) isL) := by
  unfold mapFinish
  rw [hi]
  cases isL with
  | true => exact ⟨hw, hu.lmapDone hn h1 h2 hm, rfl, rfl⟩
  | false =>
    have hu7 := hu.dmapDone (b := map) (n := n) hn h1 h2 hm
    obtain ⟨hT, hT1, hT2, _⟩ := hu.lmap (by decide)
    refine ⟨hw, hu7, rfl, rfl, rfl, hT, ?_, hT2, ?_⟩
    · show 0 + g.treesL = g.treesL
      omega
    · refine ⟨?_, by simp, fun i hi => absurd hi (by simp)⟩
      show (zeroBytes (4 * st.d.treesL.toNat)).size = 4 * g.treesL
      rw [zeroBytes_size (by omega), hT]

/-- What moving on from a context map does to what a state holds. -/
theorem mapFinish_move {st0 st : Hd} {g : Gh} {p : HPhase} {isL : Bool} {n : UInt64} {ntrees : Nat} {cmap : List Nat} {map : ByteArray} (hi : st.isL = isL)
    (hu : Upto st.d g (mapIdx isL)) (hms : map.size = mapSize g isL) (he : SameHeld { st with fill := st0.fill } st0) (hf : HSize st0 → st.fill.size ≤ 16384)
    (hcap : 768 ≤ capH p) : HMove st0 (mapFinish st n map) p (mapNextPhase (g.setMap isL ntrees cmap) isL) none := by
  unfold mapFinish
  rw [hi]
  have hm : st.d.arenaMax = st0.d.arenaMax := congrArg Done.arenaMax he.d
  have ha : st.d.arena = st0.d.arena := congrArg Done.arena he.d
  cases isL with
  | true =>
    have hL := hu.cat .L (by decide)
    have h256 : g.m.literal.n ≤ 256 := hL.wf.2.1
    have hsz : map.size ≤ 16384 := by
      rw [hms]
      show 64 * g.m.literal.n ≤ _
      omega
    refine ⟨hm, by show st.d.arena.size = _; rw [ha]; rfl, fun h0 => ?_, ?_, Nat.zero_le _⟩
    · have h := h0.same he
      exact ⟨hf h0, h.lens, h.clLens, h.clt, h.mapT, h.modes, hsz, h.dMap, h.litBase, h.icBase, h.dBase⟩
    · show 768 + (if (none : Option PrefixCode).isSome = true then 1 else 0) ≤ _
      simpa using hcap
  | false =>
    have hD := hu.cat .D (by decide)
    have h256 : g.m.distance.n ≤ 256 := hD.wf.2.1
    obtain ⟨hT, _, hT2, _⟩ := hu.lmap (by decide)
    have hsz : map.size ≤ 1024 := by
      rw [hms]
      show 4 * g.m.distance.n ≤ _
      omega
    have hfs : (zeroBytes (4 * st.d.treesL.toNat)).size ≤ 16384 := by
      rw [zeroBytes_size (by omega)]
      omega
    refine ⟨hm, by show st.d.arena.size = _; rw [ha]; rfl, fun h0 => ?_, ?_, Nat.zero_le _⟩
    · have h := h0.same he
      exact ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, hsz, h.litBase, h.icBase, h.dBase⟩
    · show 256 * ckN .L + (g.setMap false ntrees cmap).treesL + (if (none : Option PrefixCode).isSome = true then 1 else 0) ≤ _
      have e : (g.setMap false ntrees cmap).treesL = g.treesL := rfl
      rw [e]
      simp only [ckN, Option.isSome, Bool.false_eq_true, ↓reduceIte]
      omega

/-! ### A context map's number of trees -/

/-- A context map's size. -/
@[inline] def mapSizeFast (st : Hd) : Nat :=
  if st.isL then 64 * st.d.nL.toNat else 4 * st.d.nD.toNat

/-- The place at a context map's number of trees. -/
def stepHTrees (st : Hd) (pos : USize) : Hd :=
  let r := varLenFast ⟨st.word, st.count⟩
  match r.status with
  | .short => markH st pos .needsInput
  | .bad => markH st pos .bad
  | .ok =>
    let n := r.a
    if n < 2 then mapFinish { st with word := r.word, count := r.count, pos := pos, status := .next } n (zeroBytes (mapSizeFast st))
    else { st with word := r.word, count := r.count, pos := pos, status := .next, tag := .rlemax, ntrees := n }

theorem mapSizeFast_eq {st : Hd} {g : Gh} {isL : Bool} (hi : st.isL = isL) (hu : Upto st.d g (mapIdx isL)) :
    mapSizeFast st = mapSize g isL ∧ mapSize g isL ≤ 16384 := by
  have hL := hu.cat .L (by cases isL <;> decide)
  have hD := hu.cat .D (by cases isL <;> decide)
  have h1 : st.d.nL.toNat = g.m.literal.n := hL.n
  have h2 : st.d.nD.toNat = g.m.distance.n := hD.n
  have h3 : g.m.literal.n ≤ 256 := hL.wf.2.1
  have h4 : g.m.distance.n ≤ 256 := hD.wf.2.1
  unfold mapSizeFast mapSize literalContextMapSize distanceContextMapSize
  rw [hi]
  cases isL
  · simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · simp only [↓reduceIte]
    omega

theorem stepHTrees_ok {isL : Bool} {st : Hd} {g : Gh} {pos : USize} (hrel : HRel st g (.trees isL)) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) : HStepOk K a stop g (.trees isL) st pos (stepHTrees st pos) := by
  obtain ⟨hw, hu, ht, hi⟩ := hrel
  have hrel : HRel st g (.trees isL) := ⟨hw, hu, ht, hi⟩
  have R := varLenFast_ok hw
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.trees isL)) (N := fun v b =>
    if v < 2 then afterMap K g isL v (List.replicate (mapSize g isL) 0) b
    else hrest K g (.rlemax isL v) b) (fun bs => hrest_trees K g isL bs)
  have hval := R.ok
  unfold stepHTrees
  dsimp only
  generalize varLenFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    exact HStepOk.ofShortRead (X := 11) hrel hfull (by omega) h3 h4
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hrange := readVarLen_range ((hval hs).2 [])
    have hsh : (r.a < 2) ↔ r.a.toNat < 2 := UInt64.lt_iff_toNat_lt
    by_cases h2 : r.a < 2
    · rw [ite_eq_left h2]
      have h2' := hsh.mp h2
      obtain ⟨hsz, hle⟩ := mapSizeFast_eq hi hu
      have hmap : MapOk (zeroBytes (mapSizeFast st)) (List.replicate (mapSize g isL) 0) (mapSize g isL) r.a.toNat := by
        rw [hsz]
        refine ⟨zeroBytes_size (by omega), by simp, fun i hi => ?_, fun v hv => ?_⟩
        · rw [zeroBytes_get (by omega), List.getElem?_replicate, ite_eq_left hi]
          rfl
        · rw [(List.mem_replicate.mp hv).2]
          omega
      have hrel2 := mapFinish_rel (st := { st with word := r.word, count := r.count, pos := pos, status := .next })
        hw2 hi hu hmap rfl hrange.1 hrange.2
      obtain ⟨b1, b2, b3, b4⟩ := mapFinish_spec { st with word := r.word, count := r.count, pos := pos, status := .next } r.a
        (zeroBytes (mapSizeFast st))
      have hmv := mapFinish_move (st0 := st) (st := { st with word := r.word, count := r.count, pos := pos, status := .next }) (g := g) (p := .trees isL) (n := r.a) (map := zeroBytes (mapSizeFast st))
        (ntrees := r.a.toNat) (cmap := List.replicate (mapSize g isL) 0) hi hu hmap.sz ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun h => h.fill) (Nat.le_refl _)
      generalize mapFinish { st with word := r.word, count := r.count, pos := pos, status := .next } r.a
        (zeroBytes (mapSizeFast st)) = r2 at hrel2 b1 b2 b3 b4 hmv ⊢
      refine HStepOk.ofNext (hd := treesNext_down _ _) (hm := hmv) b4 hrel2 (by rw [b3]; exact Nat.le_refl _) (by rw [b3]; exact hp) (fun F => ?_)
      have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      simp only [h2', ↓reduceIte]
      rw [afterMap_eq, avail_mk, b1, b2, b3]
      rfl
    · rw [ite_eq_right h2]
      have h2' : ¬ r.a.toNat < 2 := fun h => h2 (hsh.mpr h)
      refine HStepOk.ofNext (g' := g) (p' := .rlemax isL r.a.toNat) rfl ⟨hw2, hu, rfl, hi, rfl, by omega, hrange.2⟩
        (Nat.le_refl _) hp (fun F => ?_)
      have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      simp only [h2', ↓reduceIte]
      rfl

/-! ### RLEMAX -/

/-- The place at RLEMAX. -/
def stepHRlemax (st : Hd) (pos : USize) : Hd :=
  let r := rlemaxFast ⟨st.word, st.count⟩
  match r.status with
  | .short => markH st pos .needsInput
  | .bad => markH st pos .bad
  | .ok =>
    { st with
      word := r.word, count := r.count, pos := pos, status := .next, tag := .code, role := .map, rlemax := r.a
      size := st.ntrees + r.a }

theorem stepHRlemax_ok {isL : Bool} {ntrees : Nat} {st : Hd} {g : Gh} {pos : USize} (hrel : HRel st g (.rlemax isL ntrees))
    (hp : pos.toNat ≤ stop.toNat) (hfull : 56 < st.count.toNat ∨ pos = stop) :
    HStepOk K a stop g (.rlemax isL ntrees) st pos (stepHRlemax st pos) := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256⟩ := hrel
  have hrel : HRel st g (.rlemax isL ntrees) := ⟨hw, hu, ht, hi, hn, h2, h256⟩
  have R := rlemaxFast_ok hw
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := hrest K g (.rlemax isL ntrees)) (N := fun v b =>
    hrest K g (.code (.map isL ntrees v) (contextMapAlphabetSize ntrees v)) b) (fun bs => rfl)
  have hval := R.ok
  unfold stepHRlemax
  dsimp only
  generalize rlemaxFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    exact HStepOk.ofShortRead (X := 5) hrel hfull (by omega) h3 h4
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hrange := readRLEMAX_range ((hval hs).2 [])
    have hsum : (st.ntrees + r.a).toNat = ntrees + r.a.toNat := by
      rw [UInt64.toNat_add, hn]
      exact Nat.mod_eq_of_lt (by omega)
    refine HStepOk.ofNext (g' := g) (p' := .code (.map isL ntrees r.a.toNat) (contextMapAlphabetSize ntrees r.a.toNat)) rfl
      ⟨hw2, hu, rfl, ⟨hsum, ?_, ?_⟩, rfl, hi, hn, rfl, h2, h256, hrange, rfl⟩ (Nat.le_refl _) hp (fun F => ?_)
    · unfold contextMapAlphabetSize
      omega
    · unfold contextMapAlphabetSize
      omega
    · have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      rfl

/-! ### A group of codes -/

/-- A group of codes' alphabet. -/
@[inline] def ckSizeFast (d : Done) : CK → UInt64
  | .L => 256
  | .I => 704
  | .D => 16 + d.ndirect + ((48 : UInt64) <<< d.npostfix)

/-- Moves on from a group of codes. -/
def ckFinish (st : Hd) : Hd :=
  let fill := st.fill
  match st.ck with
  | .L =>
    { st with
      ck := .I, idx := 0, left := st.d.nI, fill := zeroBytes (4 * st.d.nI.toNat), d := { st.d with litBase := fill } }
  | .I =>
    { st with
      ck := .D, idx := 0, left := st.d.treesD, fill := zeroBytes (4 * st.d.treesD.toNat), d := { st.d with icBase := fill } }
  | .D => { st with tag := .ready, status := .ready, d := { st.d with dBase := fill } }

theorem ckFinish_spec (st : Hd) : (ckFinish st).word = st.word ∧ (ckFinish st).count = st.count ∧ (ckFinish st).pos = st.pos := by
  unfold ckFinish
  dsimp only
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The place at the start of a group of codes' next one, or at its end. -/
def stepHCodes (st : Hd) (pos : USize) : Hd :=
  if st.left = 0 then ckFinish { st with pos := pos, status := .next }
  else { st with pos := pos, status := .next, tag := .code, role := .codes, left := st.left - 1, size := ckSizeFast st.d st.ck }

/-- A group of codes settled moves the stage on. -/
theorem Upto.codesDoneL {d : Done} {g : Gh} (h : Upto d g 7) {b : ByteArray} {cs : List PrefixCode} (hl : cs.length = g.treesL)
    (hp : CodesPart d.arena b cs g.treesL literalAlphabetSize) : Upto { d with litBase := b } (g.setCodes .L cs) 8 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := h.lmap (by omega)
  dmap _ := h.dmap (by omega)
  codes k hk := by
    cases k with
    | L => exact ⟨hl.symm, hp⟩
    | I => simp only [ckIdx] at hk; omega
    | D => simp only [ckIdx] at hk; omega

theorem Upto.codesDoneI {d : Done} {g : Gh} (h : Upto d g 8) {b : ByteArray} {cs : List PrefixCode} (hl : cs.length = g.m.insertCopy.n)
    (hp : CodesPart d.arena b cs g.m.insertCopy.n insertCopyAlphabetSize) : Upto { d with icBase := b } (g.setCodes .I cs) 9 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := h.lmap (by omega)
  dmap _ := h.dmap (by omega)
  codes k hk := by
    cases k with
    | L => exact h.codes .L (by decide)
    | I => exact ⟨hl.symm, hp⟩
    | D => simp only [ckIdx] at hk; omega

theorem Upto.codesDoneD {d : Done} {g : Gh} (h : Upto d g 9) {b : ByteArray} {cs : List PrefixCode} (hl : cs.length = g.treesD)
    (hp : CodesPart d.arena b cs g.treesD (distanceAlphabetSize g.m.npostfix g.m.ndirect)) :
    Upto { d with dBase := b } (g.setCodes .D cs) 10 where
  four := h.four
  le := h.le
  max := h.max
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := h.lmap (by omega)
  dmap _ := h.dmap (by omega)
  codes k hk := by
    cases k with
    | L => exact h.codes .L (by decide)
    | I => exact h.codes .I (by decide)
    | D => exact ⟨hl.symm, hp⟩

private theorem ckSizeFast_eq {d : Done} {g : Gh} {k : CK} (hu : Upto d g (ckIdx k + 7)) :
    (ckSizeFast d k).toNat = ckSize k g ∧ 2 ≤ ckSize k g ∧ ckSize k g ≤ 704 := by
  cases k with
  | L => exact ⟨rfl, by show 2 ≤ 256; omega, by show 256 ≤ 704; omega⟩
  | I => exact ⟨rfl, by show 2 ≤ 704; omega, by show 704 ≤ 704; omega⟩
  | D =>
    obtain ⟨h1, h2, h3, h4⟩ := hu.np (by simp only [ckIdx]; omega)
    have key : ∀ x, x < 4 → 48 <<< x ≤ 384 := by decide
    have hk := key _ (show g.m.npostfix < 4 by omega)
    have hs : ((48 : UInt64) <<< d.npostfix).toNat = 48 <<< g.m.npostfix := by
      rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (show d.npostfix.toNat < 64 by omega), h1,
        show (48 : UInt64).toNat = 48 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · show (16 + d.ndirect + ((48 : UInt64) <<< d.npostfix)).toNat = 16 + g.m.ndirect + (48 <<< g.m.npostfix)
      rw [UInt64.toNat_add, UInt64.toNat_add, h2, hs, show (16 : UInt64).toNat = 16 from rfl, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    · show 2 ≤ 16 + g.m.ndirect + (48 <<< g.m.npostfix)
      omega
    · show 16 + g.m.ndirect + (48 <<< g.m.npostfix) ≤ 704
      omega

theorem stepHCodes_ok {k : CK} {done : List PrefixCode} {left : Nat} {st : Hd} {g : Gh} {pos : USize}
    (hrel : HRel st g (.codes k done left)) (hp : pos.toNat ≤ stop.toNat) :
    HStepOk K a stop g (.codes k done left) st pos (stepHCodes st pos) := by
  obtain ⟨hw, hu, ht, hk, hidx, hleft, hlen, h256, hpart⟩ := hrel
  unfold stepHCodes
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    have hl0 : left = 0 := by
      rw [← hleft, h0]
      rfl
    subst hl0
    have hlen' : done.length = g.ckCount k := by omega
    obtain ⟨b1, b2, b3⟩ := ckFinish_spec { st with pos := pos, status := .next }
    have hfill : st.fill.size ≤ 1024 := by
      rw [hpart.basesSize]
      omega
    cases k with
    | L =>
      have hCI := hu.cat .I (by show 1 < 0 + 7; omega)
      have hn : st.d.nI.toNat = g.m.insertCopy.n := hCI.n
      have h256' : g.m.insertCopy.n ≤ 256 := hCI.wf.2.1
      have hfs : (zeroBytes (4 * st.d.nI.toNat)).size ≤ 16384 := by
        rw [zeroBytes_size (by omega)]
        omega
      have e : ckFinish { st with pos := pos, status := .next } = { st with
          pos := pos, status := .next, ck := .I, idx := 0, left := st.d.nI, fill := zeroBytes (4 * st.d.nI.toNat)
          d := { st.d with litBase := st.fill } } := by
        unfold ckFinish
        dsimp only
        rw [hk]
      rw [e]
      refine HStepOk.ofNext (g' := g.setCodes .L done) (p' := .codes .I [] g.m.insertCopy.n) rfl
        ⟨hw, hu.codesDoneL hlen' hpart, ht, rfl, rfl, hn, by show 0 + g.m.insertCopy.n = g.m.insertCopy.n; omega, h256', ?_⟩
        (Nat.le_refl _) hp (fun F => ?_)
        (hm := ⟨rfl, rfl, fun h => ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, hfill, h.icBase, h.dBase⟩,
          by simp only [capH, ckN, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩)
      · refine ⟨?_, by simp, fun i hi => absurd hi (by simp)⟩
        show (zeroBytes (4 * st.d.nI.toNat)).size = 4 * g.m.insertCopy.n
        rw [zeroBytes_size (by omega), hn]
      · exact hrest_codes_L K g done _
    | I =>
      obtain ⟨hT, hT1, hT2, _⟩ := hu.dmap (by show 6 < 1 + 7; omega)
      have hfs : (zeroBytes (4 * st.d.treesD.toNat)).size ≤ 16384 := by
        rw [zeroBytes_size (by omega)]
        omega
      have e : ckFinish { st with pos := pos, status := .next } = { st with
          pos := pos, status := .next, ck := .D, idx := 0, left := st.d.treesD, fill := zeroBytes (4 * st.d.treesD.toNat)
          d := { st.d with icBase := st.fill } } := by
        unfold ckFinish
        dsimp only
        rw [hk]
      rw [e]
      refine HStepOk.ofNext (g' := g.setCodes .I done) (p' := .codes .D [] g.treesD) rfl
        ⟨hw, hu.codesDoneI hlen' hpart, ht, rfl, rfl, hT, by show 0 + g.treesD = g.treesD; omega, hT2, ?_⟩
        (Nat.le_refl _) hp (fun F => ?_)
        (hm := ⟨rfl, rfl, fun h => ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, hfill, h.dBase⟩,
          by simp only [capH, ckN, Option.isSome, Bool.false_eq_true, ↓reduceIte]; omega, Nat.zero_le _⟩)
      · refine ⟨?_, by simp, fun i hi => absurd hi (by simp)⟩
        show (zeroBytes (4 * st.d.treesD.toNat)).size = 4 * g.treesD
        rw [zeroBytes_size (by omega), hT]
      · exact hrest_codes_I K g done _
    | D =>
      have e : ckFinish { st with pos := pos, status := .next } = { st with
          pos := pos, status := .ready, tag := .ready, d := { st.d with dBase := st.fill } } := by
        unfold ckFinish
        dsimp only
        rw [hk]
      rw [e]
      exact ⟨fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e,
        fun _ => ⟨g.setCodes .D done, hu.codesDoneD hlen' hpart, hw, Nat.le_refl _, hp, (fun F => hrest_codes_D K g done _), rfl, rfl,
          fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, hfill⟩⟩⟩
  · rw [ite_eq_right h0]
    have hl0 : st.left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    obtain ⟨n, rfl⟩ : ∃ n, left = n + 1 := ⟨left - 1, by omega⟩
    have hl1 : (st.left - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hleft]
      rfl
    obtain ⟨hs1, hs2, hs3⟩ := ckSizeFast_eq hu
    subst hk
    refine HStepOk.ofNext (g' := g) (p' := .code (.codes st.ck done n) (ckSize st.ck g))
      (hd := Or.inl (Or.inr ⟨rfl, show 2 * n + 1 < 2 * (n + 1) by omega⟩)) rfl
      ⟨hw, hu, rfl, ⟨hs1, hs2, hs3⟩, rfl, rfl, hidx, hl1, rfl, by omega, h256, hpart⟩ (Nat.le_refl _) hp (fun F => ?_)
    exact hrest_codes_succ K st.ck g done n _

end

end Brotli.Decoder
