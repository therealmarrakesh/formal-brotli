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

/-- A group of codes' alphabet. -/
@[inline] def ckSizeFast (d : Done) : CK → UInt64
  | .L => 256
  | .I => 704
  | .D => 16 + d.ndirect + ((48 : UInt64) <<< d.npostfix)

theorem ckSizeFast_eq {d : Done} {g : Gh} {n : Nat} (k : CK) (hu : Upto d g n) (h3 : 3 < n) :
    (ckSizeFast d k).toNat = ckSize k g ∧ 2 ≤ ckSize k g ∧ ckSize k g ≤ 704 := by
  cases k with
  | L => exact ⟨rfl, by show 2 ≤ 256; omega, by show 256 ≤ 704; omega⟩
  | I => exact ⟨rfl, by show 2 ≤ 704; omega, by show 704 ≤ 704; omega⟩
  | D =>
    obtain ⟨h1, h2, h3, h4⟩ := hu.np h3
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

/-- What the decoder reserves for the groups' tables, with the distance context map's `n` trees: `treeMax` of each group's
alphabet for each of its codes. -/
@[inline] def resFast (d : Done) (n : UInt64) : UInt64 :=
  d.treesL * 2528 + d.nI * 4320 + n * (4 * (ckSizeFast d .D + 376))

theorem resFast_eq {d : Done} {g : Gh} {n : UInt64} {ntrees : Nat} {cmap : List Nat} (hu : Upto d g 6) (hn : n.toNat = ntrees)
    (h2 : ntrees ≤ 256) : (resFast d n).toNat = resBytes (g.setMap false ntrees cmap) := by
  obtain ⟨hT, _, hT2, _⟩ := hu.lmap (by decide)
  have hI := hu.cat .I (by decide)
  have hIn : d.nI.toNat = g.m.insertCopy.n := hI.n
  have hI2 : g.m.insertCopy.n ≤ 256 := hI.wf.2.1
  obtain ⟨hs1, _, hs3⟩ := ckSizeFast_eq (g := g) .D hu (by decide)
  have e1 : (d.treesL * 2528).toNat = g.treesL * 2528 := by
    rw [UInt64.toNat_mul, hT, show (2528 : UInt64).toNat = 2528 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have e2 : (d.nI * 4320).toNat = g.m.insertCopy.n * 4320 := by
    rw [UInt64.toNat_mul, hIn, show (4320 : UInt64).toNat = 4320 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have i1 : (ckSizeFast d .D + 376).toNat = ckSize .D g + 376 := by
    rw [UInt64.toNat_add, hs1, show (376 : UInt64).toNat = 376 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have e3 : (4 * (ckSizeFast d .D + 376)).toNat = 4 * (ckSize .D g + 376) := by
    rw [UInt64.toNat_mul, i1, show (4 : UInt64).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have e4 : (n * (4 * (ckSizeFast d .D + 376))).toNat = ntrees * (4 * (ckSize .D g + 376)) := by
    rw [UInt64.toNat_mul, hn, e3]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul h2 (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hs3 376))) (by decide))
  have hb1 : g.treesL * 2528 ≤ 256 * 2528 := Nat.mul_le_mul_right _ hT2
  have hb2 : g.m.insertCopy.n * 4320 ≤ 256 * 4320 := Nat.mul_le_mul_right _ hI2
  have hb3 : ntrees * (4 * (ckSize .D g + 376)) ≤ 256 * (4 * (704 + 376)) :=
    Nat.mul_le_mul h2 (Nat.mul_le_mul_left 4 (Nat.add_le_add_right hs3 376))
  have s1 : (d.treesL * 2528 + d.nI * 4320).toNat = g.treesL * 2528 + g.m.insertCopy.n * 4320 := by
    rw [UInt64.toNat_add, e1, e2]
    exact Nat.mod_eq_of_lt (by omega)
  have hlt : g.treesL * 2528 + g.m.insertCopy.n * 4320 + ntrees * (4 * (ckSize .D g + 376)) < 2 ^ 64 := by omega
  unfold resFast
  rw [UInt64.toNat_add, s1, e4, Nat.mod_eq_of_lt hlt]
  show _ = g.treesL * (4 * (256 + 376)) + g.m.insertCopy.n * (4 * (704 + 376)) + ntrees * (4 * (ckSize .D g + 376))
  rfl

/-- What the groups' tables can take is at most `resMax`. -/
theorem resBytes_le {d : Done} {g : Gh} {ntrees : Nat} {cmap : List Nat} (hu : Upto d g 6) (h2 : ntrees ≤ 256) :
    resBytes (g.setMap false ntrees cmap) ≤ resMax := by
  obtain ⟨_, _, hT2, _⟩ := hu.lmap (by decide)
  have hI2 : g.m.insertCopy.n ≤ 256 := (hu.cat .I (by decide)).wf.2.1
  obtain ⟨_, _, hnp, hnd⟩ := hu.np (by decide)
  exact resBytes_bound (g := g.setMap false ntrees cmap) hT2 hI2 h2 hnp hnd

/-- An array holding `t`'s bytes, with room for `cap` bytes in all, so that tables appended within it are written in
place. -/
def reserve (t : ByteArray) (cap : Nat) : ByteArray := ByteArray.emptyWithCapacity cap ++ t

theorem reserve_eq (t : ByteArray) (cap : Nat) : reserve t cap = t := by
  apply ByteArray.ext
  rw [reserve, ByteArray.data_append]
  exact Array.empty_append

/-- Moves on from a context map, with `n` trees. After the distance context map, every group's number of codes is known,
and the arena reserves room for all their tables, unless that would pass its limit. -/
def mapFinish (st : Hd) (n : UInt64) (map : ByteArray) : Hd :=
  match st.isL with
  | true => { st with tag := .trees, isL := false, d := { st.d with lMap := map, treesL := n } }
  | false =>
    let res := resFast st.d n
    if res ≤ st.d.arenaMax then
      let cap := UInt64.ofNat st.d.arena.size + res
      { st with
        tag := .codes, ck := .L, idx := 0, left := st.d.treesL, fill := zeroBytes (4 * st.d.treesL.toNat)
        d := { st.d with dMap := map, treesD := n, arena := reserve st.d.arena cap.toNat, arenaCap := cap } }
    else { st with status := .memory }

theorem mapFinish_spec (st : Hd) (n : UInt64) (map : ByteArray) : (mapFinish st n map).word = st.word ∧
    (mapFinish st n map).count = st.count ∧ (mapFinish st n map).pos = st.pos ∧
    ((mapFinish st n map).status = st.status ∨ (mapFinish st n map).status = .memory) := by
  unfold mapFinish
  split
  · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
  · dsimp only
    split
    · exact ⟨rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, rfl, Or.inr rfl⟩

theorem mapFinish_tag (st : Hd) (n : UInt64) (map : ByteArray) :
    (mapFinish st n map).tag = .trees ∨ (mapFinish st n map).tag = .codes ∨ (mapFinish st n map).tag = st.tag := by
  unfold mapFinish
  split
  · exact Or.inl rfl
  · dsimp only
    split
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem Upto.lmapDone {d : Done} {g : Gh} (h : Upto d g 5) {b : ByteArray} {n : UInt64} {ntrees : Nat} {cmap : List Nat}
    (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256) (hm : MapOk b cmap (literalContextMapSize g.m.literal.n) ntrees) :
    Upto { d with lMap := b, treesL := n } (g.setMap true ntrees cmap) 6 where
  four := h.four
  le := h.le
  max := h.max
  capLe := h.capLe
  room := h.room
  small _ := h.small (by omega)
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := ⟨hn, h1, h2, hm⟩
  dmap h := absurd h (by omega)
  codes _ h := absurd h (by omega)

/-- The distance context map settled, with the arena's reservation for the groups' tables made. -/
theorem Upto.dmapRes {d : Done} {g : Gh} (h : Upto d g 6) {b : ByteArray} {n : UInt64} {ntrees : Nat} {cmap : List Nat}
    (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256) (hm : MapOk b cmap (distanceContextMapSize g.m.distance.n) ntrees)
    {cap : UInt64} (hc1 : d.arena.size ≤ cap.toNat) (hc2 : cap.toNat ≤ smallMax + d.arenaMax.toNat) :
    Upto { d with dMap := b, treesD := n, arenaCap := cap } (g.setMap false ntrees cmap) 7 where
  four := h.four
  le := hc1
  max := by
    have := h.room
    show cap.toNat + 132096 < 2 ^ 32
    omega
  capLe := hc2
  room := h.room
  small h := absurd h (by omega)
  cat i hi := by
    have hc := h.cat i (by cases i <;> decide)
    cases i <;> exact ⟨hc.n, hc.count, hc.rel, hc.wf, hc.tc, hc.cc⟩
  np _ := h.np (by omega)
  modes _ := h.modes (by omega)
  lmap _ := h.lmap (by omega)
  dmap _ := ⟨hn, h1, h2, hm⟩
  codes _ h := absurd h (by cases ‹CK› <;> simp only [ckIdx] <;> omega)

/-- A step that ends a context map, once what follows it is read: it moves on, and after the distance context map the arena
reserves the groups' tables, or the limit is reported. -/
theorem mapFinish_ok {st0 st : Hd} {g : Gh} {p : HPhase} {isL : Bool} {n : UInt64} {ntrees : Nat} {cmap : List Nat}
    {map : ByteArray} (hw : (BitBuffer.mk st.word st.count).Wf) (hi : st.isL = isL) (hu : Upto st.d g (mapIdx isL))
    (hm : MapOk map cmap (mapSize g isL) ntrees) (hn : n.toNat = ntrees) (h1 : 1 ≤ ntrees) (h2 : ntrees ≤ 256)
    (hs : st.status = .next) (hp : st.pos.toNat ≤ stop.toNat)
    (he : SameHeld { st with fill := st0.fill, xf := st0.xf, mtf := st0.mtf, seenR := st0.seenR, seenX := st0.seenX } st0)
    (hf : HSize st0 → st.fill.size ≤ 16384 ∧ st.xf.size ≤ 16384 ∧ st.mtf.size ≤ 256 ∧ st.seenR.size ≤ 256 ∧ st.seenX.size ≤ 256)
    (hb : budH g p = 0) (hs6 : stageOf p ≤ 6)
    (hd : HDown p (mapNextPhase (g.setMap isL ntrees cmap) isL))
    (hr : ∀ F, hrest K g p (availBits st0.word st0.count a st.pos stop F) =
      afterMap K g isL ntrees cmap (availBits st.word st.count a st.pos stop F))
    (hj : ∀ F, hStepP (g, p) (availBits st0.word st0.count a st.pos stop F) =
      .next (g.setMap isL ntrees cmap, mapNextPhase (g.setMap isL ntrees cmap) isL) (availBits st.word st.count a st.pos stop F)) :
    HStepOk K a stop g p st0 st.pos (mapFinish st n map) := by
  have hmx : st.d.arenaMax = st0.d.arenaMax := congrArg Done.arenaMax he.d
  have ha : st.d.arena = st0.d.arena := congrArg Done.arena he.d
  have hcp : st.d.arenaCap = st0.d.arenaCap := congrArg Done.arenaCap he.d
  have hms := hm.sz
  unfold mapFinish
  rw [hi]
  cases isL with
  | true =>
    have hL := hu.cat .L (by decide)
    have h256 : g.m.literal.n ≤ 256 := hL.wf.2.1
    have hsz : map.size ≤ 16384 := by
      rw [hms]
      show 64 * g.m.literal.n ≤ _
      omega
    refine HStepOk.ofNext (g' := g.setMap true ntrees cmap) (p' := mapNextPhase (g.setMap true ntrees cmap) true) hs
      ⟨hw, hu.lmapDone hn h1 h2 hm, rfl, rfl⟩ (Nat.le_refl _) hp (fun F => by rw [hr, afterMap_eq]; rfl) (fun F => hj F) hd
      ⟨hmx, by show st.d.arena.size = _; rw [ha]; rfl, fun h0 => ?_, ⟨hcp, by rw [hb]; simp [budH, mapNextPhase, tableOf]⟩⟩
    have h := h0.same he
    exact ⟨(hf h0).1, h.lens, h.clLens, h.clt, h.mapT, h.modes, hsz, h.dMap, h.litBase, h.icBase, h.dBase, (hf h0).2⟩
  | false =>
    have hD := hu.cat .D (by decide)
    have h256 : g.m.distance.n ≤ 256 := hD.wf.2.1
    obtain ⟨hT, _, hT2, _⟩ := hu.lmap (by decide)
    have hsz : map.size ≤ 1024 := by
      rw [hms]
      show 4 * g.m.distance.n ≤ _
      omega
    have hres := resFast_eq (cmap := cmap) hu hn h2
    have hrest' : ∀ F, hrest K g p (availBits st0.word st0.count a st.pos stop F) = K.r (g.setMap false ntrees cmap)
        (hrest K (g.setMap false ntrees cmap) (mapNextPhase (g.setMap false ntrees cmap) false) (availBits st.word st.count a st.pos stop F)) :=
      fun F => by rw [hr, afterMap_eq]; rfl
    dsimp only
    by_cases hc : resFast st.d n ≤ st.d.arenaMax
    · rw [ite_eq_left hc, reserve_eq]
      have hcN := UInt64.le_iff_toNat_le.mp hc
      have hsmall := hu.small (by decide)
      have hle := hu.le
      have hroom := hu.room
      have hcap : (UInt64.ofNat st.d.arena.size + resFast st.d n).toNat = st.d.arena.size + resBytes (g.setMap false ntrees cmap) := by
        rw [UInt64.toNat_add, u64_lit (by omega), hres]
        exact Nat.mod_eq_of_lt (by omega)
      have hfs : (zeroBytes (4 * st.d.treesL.toNat)).size ≤ 16384 := by
        rw [zeroBytes_size (by omega)]
        omega
      have hu7 := hu.dmapRes (b := map) (n := n) (cap := UInt64.ofNat st.d.arena.size + resFast st.d n) hn h1 h2 hm
        (by rw [hcap]; omega) (by rw [hcap]; omega)
      refine ⟨fun _ => ⟨g.setMap false ntrees cmap, mapNextPhase (g.setMap false ntrees cmap) false,
          some (.res (g.setMap false ntrees cmap)), ?_, Nat.le_refl _, hp, hrest', hd, ?_, fun F => hj F⟩,
        fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e),
        fun e => HStatus.noConfusion (hs.symm.trans e), fun e => HStatus.noConfusion (hs.symm.trans e)⟩
      · refine ⟨hw, hu7, rfl, rfl, rfl, hT, ?_, hT2, ?_⟩
        · show 0 + g.treesL = g.treesL
          omega
        · refine ⟨?_, by simp, fun i hi => absurd hi (by simp)⟩
          show (zeroBytes (4 * st.d.treesL.toNat)).size = 4 * g.treesL
          rw [zeroBytes_size (by omega), hT]
      · refine ⟨hmx, by show st.d.arena.size = st0.d.arena.size + 0; rw [ha, Nat.add_zero], fun h0 => ?_,
          hcap, rfl, by rw [← hcp]; exact hsmall, by rw [← hmx, ← hres]; exact hcN, hs6, Nat.le_refl _⟩
        have h := h0.same he
        exact ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, hsz, h.litBase, h.icBase, h.dBase, (hf h0).2⟩
    · rw [ite_eq_right hc]
      have hlt : st0.d.arenaMax.toNat < resBytes (g.setMap false ntrees cmap) := by
        rw [← hmx, ← hres]
        exact Nat.lt_of_not_le fun e => hc (UInt64.le_iff_toNat_le.mpr e)
      exact ⟨fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e, fun e => HStatus.noConfusion e,
        fun _ => Or.inr ⟨g.setMap false ntrees cmap, hlt, resBytes_le hu h2, by rw [← hcp]; exact hu.small (by decide),
          fun F => ⟨_, hrest' F⟩⟩, fun e => HStatus.noConfusion e⟩

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
  have hsh0 := R.short
  unfold stepHTrees
  dsimp only
  generalize varLenFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval hsh0
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    obtain ⟨_, _, _, h5⟩ := hsh0 hs
    exact HStepOk.ofShortRead (X := 11) hrel hfull (by omega) h3 h4
      (by show readIn 11 readVarLen _ _ = _; exact readIn_short h5 (by rw [held_len]; exact h3))
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
      exact mapFinish_ok (st0 := st) (st := { st with word := r.word, count := r.count, pos := pos, status := .next }) (p := .trees isL)
        (ntrees := r.a.toNat) (cmap := List.replicate (mapSize g isL) 0) hw2 hi hu hmap rfl hrange.1 hrange.2 rfl hp
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl, rfl⟩⟩ (fun h => ⟨h.fill, h.work⟩) rfl
        (by show mapIdx isL ≤ 6; unfold mapIdx; split <;> omega) (treesNext_down _ _)
        (fun F => by
          have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
          rw [avail_mk, e]
          simp only [h2', ↓reduceIte]
          rfl)
        (fun F => by
          rw [avail_mk]
          show readIn 11 readVarLen _ _ = _
          rw [readIn_some ((hval hs).2 _)]
          simp only [h2', ↓reduceIte]
          rfl)
    · rw [ite_eq_right h2]
      have h2' : ¬ r.a.toNat < 2 := fun h => h2 (hsh.mpr h)
      refine HStepOk.ofNext (g' := g) (p' := .rlemax isL r.a.toNat) rfl ⟨hw2, hu, rfl, hi, rfl, by omega, hrange.2⟩
        (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
      · have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
        rw [avail_mk, e]
        simp only [h2', ↓reduceIte]
        rfl
      · rw [avail_mk]
        show readIn 11 readVarLen _ _ = _
        rw [readIn_some ((hval hs).2 _)]
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
  have hsh0 := R.short
  unfold stepHRlemax
  dsimp only
  generalize rlemaxFast ⟨st.word, st.count⟩ = r at Rok Rshort Rbad hval hsh0
  cases hs : r.status with
  | short =>
    obtain ⟨_, _, h3, h4⟩ := Rshort hs
    obtain ⟨_, _, _, h5⟩ := hsh0 hs
    exact HStepOk.ofShortRead (X := 5) hrel hfull (by omega) h3 h4
      (by show readIn 5 readRLEMAX _ _ = _; exact readIn_short h5 (by rw [held_len]; exact h3))
  | bad => exact HStepOk.ofBad rfl (fun F => Rbad hs _)
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hs
    have hrange := readRLEMAX_range ((hval hs).2 [])
    have hsum : (st.ntrees + r.a).toNat = ntrees + r.a.toNat := by
      rw [UInt64.toNat_add, hn]
      exact Nat.mod_eq_of_lt (by omega)
    refine HStepOk.ofNext (g' := g) (p' := .code (.map isL ntrees r.a.toNat) (contextMapAlphabetSize ntrees r.a.toNat)) rfl
      ⟨hw2, hu, rfl, ⟨hsum, ?_, ?_⟩, rfl, hi, hn, rfl, h2, h256, hrange, rfl⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => ?_)
    · unfold contextMapAlphabetSize
      omega
    · unfold contextMapAlphabetSize
      omega
    · have e := hN (chunkBits a pos.toNat stop.toNat ++ F)
      rw [avail_mk, e]
      rfl
    · rw [avail_mk]
      show readIn 5 readRLEMAX _ _ = _
      rw [readIn_some ((hval hs).2 _)]
      rfl

/-! ### A group of codes -/

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
  capLe := h.capLe
  room := h.room
  small h := absurd h (by omega)
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
  capLe := h.capLe
  room := h.room
  small h := absurd h (by omega)
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
  capLe := h.capLe
  room := h.room
  small h := absurd h (by omega)
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
        (Nat.le_refl _) hp (fun F => ?_) (fun F => rfl)
        (hm := ⟨rfl, rfl, fun h => ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, hfill, h.icBase, h.dBase, h.work⟩,
          ⟨rfl, by simp only [budH, groupsFrom, tableOf, Gh.setCodes, ckSize]; omega⟩⟩)
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
        (Nat.le_refl _) hp (fun F => ?_) (fun F => rfl)
        (hm := ⟨rfl, rfl, fun h => ⟨hfs, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, hfill, h.dBase, h.work⟩,
          ⟨rfl, by simp only [budH, groupsFrom, tableOf, Gh.setCodes, ckSize]; omega⟩⟩)
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
        fun _ => ⟨g.setCodes .D done, hu.codesDoneD hlen' hpart, hw, Nat.le_refl _, hp, (fun F => hrest_codes_D K g done _), rfl, rfl, rfl,
          fun h => ⟨h.fill, h.lens, h.clLens, h.clt, h.mapT, h.modes, h.lMap, h.dMap, h.litBase, h.icBase, hfill, h.work⟩, fun F => rfl⟩⟩
  · rw [ite_eq_right h0]
    have hl0 : st.left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
    obtain ⟨n, rfl⟩ : ∃ n, left = n + 1 := ⟨left - 1, by omega⟩
    have hl1 : (st.left - 1).toNat = n := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [show (1 : UInt64).toNat = 1 from rfl]; omega)), hleft]
      rfl
    obtain ⟨hs1, hs2, hs3⟩ := ckSizeFast_eq k hu (by show 3 < ckIdx k + 7; omega)
    subst hk
    refine HStepOk.ofNext (g' := g) (p' := .code (.codes st.ck done n) (ckSize st.ck g))
      (hd := Or.inl (Or.inr ⟨rfl, show 2 * n + 1 < 2 * (n + 1) by omega⟩)) rfl
      ⟨hw, hu, rfl, ⟨hs1, hs2, hs3⟩, rfl, rfl, hidx, hl1, rfl, by omega, h256, hpart⟩ (Nat.le_refl _) hp (fun F => ?_) (fun F => rfl)
    exact hrest_codes_succ K st.ck g done n _

end

end Brotli.Decoder
