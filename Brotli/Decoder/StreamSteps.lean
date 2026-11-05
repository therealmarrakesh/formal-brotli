import Brotli.Decoder.StreamCmds

/-!
# The stream's steps

The places outside a header's and a meta-block's own machines: reading a header through the header machine, WBITS, a
meta-block's start, and the stream's end.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Through the header machine -/

/-- What follows a header step: a header left ready was read, so the command loop's header is made from it. -/
@[inline] def hdrNext (c : Cmd) (left : UInt64) (D0 : Dec) (r : { r : Hd // r.status = .ready → ∃ g, Upto r.d g 10 }) : Dec :=
  let r1 := r.1
  let rp := r1.pos
  match hst : r1.status with
  | .next => { D0 with hd := r1, pos := rp, status := .next }
  | .needsInput => { D0 with hd := r1, pos := rp, status := .needsInput }
  | .bad => { D0 with hd := r1, pos := rp, status := .bad }
  | .memory => { D0 with hd := r1, pos := rp, status := .memory }
  | .ready => { D0 with tag := .cmds, H := mkHdr r1.d (r.2 hst), cmd := cmdStart c r1.d r1.word r1.count left, pos := rp, status := .next }

/-- The place in a header. -/
def stepDHdr (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) (hH : HIn D.hd)
    (hp : pos.toNat ≤ stop.toNat) : Dec :=
  let c := D.cmd
  let left := D.left
  match hT : takeHd D with
  | (h, D0) => hdrNext c left D0 (stepHR a stop hs h pos (by rw [← show (takeHd D).1 = h from congrArg Prod.fst hT]; exact hH) hp)

theorem stepDHdr_ok {α : Type} {S : Sem α} {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} {hH : HIn D.hd} (hrel : DRel D (.hdr w st last mlen g p))
    (hpos : pos.toNat ≤ stop.toNat) : DStepOk S a stop (.hdr w st last mlen g p) D pos (stepDHdr a stop hs D pos hH hpos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hall, hl, hleft, hm1, hm2, hR, hp0, hb⟩ := hrel
  have ht' : tag = .hdr := ht
  subst ht'
  have hstep := stepH_ok (K := hdrK w (S.after w last) st mlen) (a := a) (hs := hs) (h := ⟨g, p, hR, hb⟩) hR hpos hb
  have hbadH := stepH_bad (K := hdrK w (S.after w last) st mlen) (a := a) (hs := hs) (h := ⟨g, p, hR, hb⟩) hR hpos hb
  have hmemH := stepH_memory (K := hdrK w (S.after w last) st mlen) (a := a) (hs := hs) (h := ⟨g, p, hR, hb⟩) hR hpos hb
  unfold stepDHdr takeHd
  dsimp only
  generalize hrr : stepHR a stop hs hd pos ⟨g, p, hR, hb⟩ hpos = rr
  obtain ⟨r, hr⟩ := rr
  have e : r = stepH a stop hs hd pos ⟨g, p, hR, hb⟩ hpos := by rw [← stepHR_val (h := ⟨g, p, hR, hb⟩) (hp := hpos), hrr]
  rw [← e] at hstep hbadH hmemH
  unfold hdrNext
  dsimp only
  split
  next hst =>
    obtain ⟨g', p', oc, hR', h1, h2, h3, h4, hmv, h5⟩ := hstep.next hst
    exact ⟨fun _ => ⟨.hdr w st last mlen g' p', ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0, hmv.bud hb⟩, h1, h2, (fun t => (h3 _).trans (Wr_id (fun _ _ => rfl) oc _)), h4, ⟨[], rfl, rfl⟩,
      fun t => (sreach_hdr (q := (g, p)) (q' := (g', p')) (Reach.one (h5 _)))⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  next hst =>
    obtain ⟨h1, h2, hR', h3, h4, hmv, h5, h6⟩ := hstep.needsInput hst
    exact ⟨fun e => DStatus.noConfusion e, fun _ => ⟨h1, h2, .hdr w st last mlen g p, ⟨rfl, ⟨hall.win, hall.produced, hall.limit⟩, hl, hleft, hm1, hm2, hR', hp0, hmv.bud hb⟩,
      (fun t => h3 _), h4, ⟨rfl, rfl⟩, (fun _ _ e => SPhase.noConfusion e), ⟨[], rfl, rfl⟩, (fun t => SReach.ofEq (h5 _)),
      ⟨_, _, .refl _ _, short_hdr h6, rfl⟩⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  next hst =>
    obtain ⟨g1, g2, g3, g4⟩ := hbadH hst
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨fun t => hstep.bad hst _, .hdr w st last mlen g p, (BitBuffer.mk hd.word hd.count).held, pos, Nat.le_refl _, g1, g2,
        by rw [BitBuffer.held_length]; exact g3, fun t => .refl _ _, fun t => g4 _⟩⟩
  next hst =>
    obtain ⟨g1, g2, _, _⟩ := hmemH hst
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨g1, g2, rfl, hp0, Or.inr ⟨_, _, _, _, _, _, rfl⟩⟩, fun e => DStatus.noConfusion e⟩
  next hst =>
    obtain ⟨g', hu, hw, h1, h2, h3, _, _, _, _, h4⟩ := hstep.ready hst
    have hrelH := mkHdr_ok hu (hr hst)
    have hRel := cmdStart_rel (c := cmd) (word := r.word) (count := r.count) (mlen := left) hw hu
      (w := w) hall.win hall.produced
    rw [show left.toNat = mlen from hleft] at hRel
    exact ⟨fun _ => ⟨.cmds w last g'.m (.command (startState st mlen g'.m)), ⟨rfl, hl, hall.limit, hrelH, hRel⟩, h1, h2, (fun t => h3 _), ⟨_, rfl⟩, ⟨[], rfl, rfl⟩,
      fun t => (SReach.one (exit_hdr (h4 _)))⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩

/-! ### A meta-block's start -/

/-- The bits of an integer are the list's first. -/
theorem readInt_drop : ∀ (n : Nat) (bs : List Bool) (v : Nat) (r : List Bool), readInt n bs = some (v, r) → r = bs.drop n
  | 0, bs, v, r, h => by
    simp only [readInt, Option.some.injEq, Prod.mk.injEq] at h
    simpa using h.2.symm
  | _ + 1, [], _, _, h => by simp [readInt] at h
  | n + 1, b :: bs, v, r, h => by
    simp only [readInt] at h
    cases hr : readInt n bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨w, r'⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact readInt_drop n bs w r' hr

/-- Dropping bits the buffer holds. -/
theorem held_drop {b : BitBuffer} {k : UInt64} (f : List Bool) (hk : k.toNat < 64) (hle : k ≤ b.count) :
    (b.held ++ f).drop k.toNat = (b.drop k).held ++ f :=
  (readInt_drop _ _ _ _ (read_int (b := b) f hk hle)).symm

private theorem msUnc_val {last : Bool} {m : Nat} {bs r : List Bool} {v : MetaStart} (h : msUnc last m bs = some (v, r)) :
    ∃ l u, v = .data l m u := by
  unfold msUnc at h
  cases last with
  | true =>
    simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨_, _, h.1.symm⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hx : readInt 1 bs with
    | none => rw [hx] at h; cases h
    | some u =>
      rw [hx] at h
      have h' : some (MetaStart.data false m (decide (u.1 = 1)), u.2) = some (v, r) := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      exact ⟨_, _, h'.1.symm⟩

/-- A meta-block's start, as far as its values' sizes go. -/
def MsOk : MetaStart → Prop
  | .lastEmpty => True
  | .metadata _ s => s ≤ 16777216
  | .data _ m _ => 1 ≤ m ∧ m ≤ 16777216

private theorem msLen_ok {last : Bool} {mn : Nat} {bs r : List Bool} {v : MetaStart} (hn : mn ≤ 6) (h : msLen last mn bs = some (v, r)) : MsOk v := by
  unfold msLen at h
  cases hx : readInt (mn * 4) bs with
  | none => rw [hx] at h; cases h
  | some q =>
    obtain ⟨x, b1⟩ := q
    rw [hx] at h
    have hlt := readInt_lt _ _ _ _ hx
    have hp : 2 ^ (mn * 4) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
    change (if 4 < mn ∧ x >>> ((mn - 1) * 4) = 0 then none else msUnc last (x + 1) b1) = _ at h
    split at h
    · cases h
    · obtain ⟨l, u, rfl⟩ := msUnc_val h
      show 1 ≤ x + 1 ∧ x + 1 ≤ 16777216
      omega

private theorem msSkip_ok {last : Bool} {n : Nat} {bs r : List Bool} {v : MetaStart} (hn : n ≤ 3) (h : msSkip last n bs = some (v, r)) : MsOk v := by
  unfold msSkip at h
  cases hx : readInt (n * 8) bs with
  | none => rw [hx] at h; cases h
  | some q =>
    obtain ⟨x, b1⟩ := q
    rw [hx] at h
    have hlt := readInt_lt _ _ _ _ hx
    have hp : 2 ^ (n * 8) ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) (by omega)
    have h24 : (2 : Nat) ^ 24 = 16777216 := rfl
    change (if 1 < n ∧ x >>> ((n - 1) * 8) = 0 then none else some (MetaStart.metadata last (if n = 0 then 0 else x + 1), b1)) = _ at h
    split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      show (if n = 0 then 0 else x + 1) ≤ 16777216
      split <;> omega

private theorem msBody_ok {last : Bool} {bs r : List Bool} {v : MetaStart} (h : msBody last bs = some (v, r)) : MsOk v := by
  unfold msBody at h
  cases hx : readInt 2 bs with
  | none => rw [hx] at h; cases h
  | some q =>
    obtain ⟨x, b1⟩ := q
    rw [hx] at h
    have hlt : x < 4 := by simpa using readInt_lt 2 _ _ _ hx
    change (if x = 3 then _ else msLen last (x + 4) b1) = _ at h
    split at h
    · cases hr : readInt 1 b1 with
      | none => rw [hr] at h; cases h
      | some q2 =>
        rw [hr] at h
        change (if q2.1 ≠ 0 then none else readInt 2 q2.2 >>= fun n => msSkip last n.1 n.2) = _ at h
        split at h
        · cases h
        · cases hn : readInt 2 q2.2 with
          | none => rw [hn] at h; cases h
          | some q3 =>
            rw [hn] at h
            have hlt3 : q3.1 < 4 := by simpa using readInt_lt 2 _ q3.1 q3.2 hn
            exact msSkip_ok (by omega) h
    · exact msLen_ok (by omega) h

/-- A meta-block's start has values of these sizes. -/
theorem metaStart_ok {bs r : List Bool} {v : MetaStart} (h : metaStart bs = some (v, r)) : MsOk v := by
  unfold metaStart at h
  cases hx : readInt 1 bs with
  | none => rw [hx] at h; cases h
  | some q =>
    obtain ⟨l, b1⟩ := q
    rw [hx] at h
    change (if l = 0 then msBody false b1 else _) = _ at h
    split at h
    · exact msBody_ok h
    · cases hy : readInt 1 b1 with
      | none => rw [hy] at h; cases h
      | some q2 =>
        rw [hy] at h
        change (if q2.1 = 1 then some (MetaStart.lastEmpty, q2.2) else msBody true q2.2) = _ at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          trivial
        · exact msBody_ok h

/-- The header machine's state at the start of a header: the arena reserves room for the categories' codes. -/
def hdStart (word count : UInt64) (limit : UInt64) : Hd :=
  { Hd.none with
    word := word, count := count
    d := { Done.none with arena := freshBytes smallMax, arenaMax := limit, arenaCap := UInt64.ofNat smallMax } }

/-- A meta-block's start, read. -/
def metaGo (D : Dec) (c : Cmd) (r : Rd) (pos : USize) : Dec :=
  if r.a = 0 then { D with tag := .ended, cmd := { c with word := r.word, count := r.count }, pos := pos, status := .next }
  else if r.a = 1 then
    if r.buf.peek (r.count &&& 7) = 0 then
      let b1 := r.buf.drop (r.count &&& 7)
      { D with tag := .skip, cmd := { c with word := b1.word, count := b1.count }, last := r.b != 0, left := r.c, pos := pos, status := .next }
    else { D with pos := pos, status := .bad }
  else if r.d != 0 then
    if r.buf.peek (r.count &&& 7) = 0 then
      let b1 := r.buf.drop (r.count &&& 7)
      { D with tag := .raw, cmd := { c with word := b1.word, count := b1.count }, last := r.b != 0, left := r.c, pos := pos, status := .next }
    else { D with pos := pos, status := .bad }
  else { D with tag := .hdr, hd := hdStart r.word r.count D.limit, cmd := c, last := r.b != 0, left := r.c, pos := pos, status := .next }

/-- The place at a meta-block's start. -/
def stepDMeta (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  if D.cmd.pend = 0 then
    if hp : pos ≤ stop then
      let rf := refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
      let rp := rf.pos
      let r := metaStartFast ⟨rf.word, rf.count⟩
      match r.status with
      | .short => { D with cmd := { D.cmd with word := rf.word, count := rf.count }, pos := rp, status := .needsInput }
      | .bad => { D with pos := rp, status := .bad }
      | .ok => metaGo D D.cmd r rp
    else { D with pos := pos, status := .bad }
  else { D with pos := pos, status := .needsOutput }

theorem smallMax_eq : smallMax = 6216 := rfl

/-- Nothing is settled at a header's start, and the arena has reserved room for the categories' codes. -/
theorem Upto.start {d : Done} {g : Gh} (h0 : d.arena.size = 0) (hc : d.arenaCap.toNat = smallMax)
    (hl : d.arenaMax.toNat + 8888 < 2 ^ 32) : Upto d g 0 where
  four := by rw [h0]
  le := by rw [h0]; exact Nat.zero_le _
  max := by
    rw [hc, smallMax_eq]
    omega
  capLe := by rw [hc]; omega
  room := by
    rw [smallMax_eq, Nat.add_assoc]
    exact Nat.lt_of_le_of_lt (Nat.add_le_add_left (by decide) _) hl
  small _ := hc
  cat i hi := absurd hi (by cases i <;> decide)
  np h := absurd h (by decide)
  modes h := absurd h (by decide)
  lmap h := absurd h (by decide)
  dmap h := absurd h (by decide)
  codes _ h := absurd h (by omega)

theorem hdStart_rel {word count limit : UInt64} (hw : (BitBuffer.mk word count).Wf) (hl : limit.toNat + 8888 < 2 ^ 32) :
    HRel (hdStart word count limit) Gh.start (.cat .L) :=
  ⟨hw, Upto.start rfl (u64_lit (by decide)) hl, rfl, rfl⟩

/-- At a header's start, the arena reserves room for the categories' codes. -/
theorem hdStart_bud (word count limit : UInt64) :
    (hdStart word count limit).d.arena.size + budH Gh.start (.cat .L) ≤ (hdStart word count limit).d.arenaCap.toNat := by
  rw [show (hdStart word count limit).d.arenaCap.toNat = smallMax from u64_lit (by decide)]
  show 0 + catMax * (catN .L + 1) ≤ smallMax
  decide

theorem whole_bytes {a : ByteArray} {p stop : Nat} (hs : stop ≤ a.size) (t : List UInt8) : (chunkBits a p stop ++ bits t).length % 8 = 0 := by
  rw [List.length_append, chunkBits_length hs, bits_length]
  omega

theorem stepDMeta_ok {α : Type} {S : Sem α} {w : Nat} {st : StreamState} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.mblock w st)) (hpos : pos.toNat ≤ stop.toNat) : DStepOk S a stop (.mblock w st) D pos (stepDMeta a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hall⟩ := hrel
  have ht' : tag = .mblock := ht
  subst ht'
  obtain ⟨hwin, hprod, hlim⟩ := hall
  have hallF : ∀ (word count : UInt64) (hd1 : Hd) (tag1 : DTag) (last1 : Bool) (left1 : UInt64) (p1 : USize) (s1 : DStatus),
      WinAll ⟨tag1, { cmd with word := word, count := count }, hd1, H, k, last1, left1, limit, p1, s1⟩ w st := by
    intro word count hd1 tag1 last1 left1 p1 s1
    exact ⟨{ hwin with }, hprod, hlim⟩
  unfold stepDMeta
  by_cases hz0 : cmd.pend = 0
  rotate_left
  · rw [ite_eq_right hz0]
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨.mblock w st, ⟨rfl, hw, ⟨hwin, hprod, hlim⟩⟩, Nat.le_refl _, hpos, (fun _ => rfl), (fun e => hz0 (USize.toNat_inj.mp e)), rfl,
        (fun _ _ _ _ => rfl), ⟨[], rfl, rfl⟩, fun _ => .refl _ _⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  rw [ite_eq_left hz0]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hpos)]
  dsimp only
  obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := cmd.word) (count := cmd.count) hs hpos hw
  have hbits : ∀ F, availBits cmd.word cmd.count a pos stop F =
      availBits (refill cmd.word cmd.count a pos stop hs hpos).word (refill cmd.word cmd.count a pos stop hs hpos).count a
        (refill cmd.word cmd.count a pos stop hs hpos).pos stop F := by
    intro F
    show (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
      (refill cmd.word cmd.count a pos stop hs hpos).buf.held ++ (chunkBits a (refill cmd.word cmd.count a pos stop hs hpos).pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, r4]
  obtain ⟨l1, l2⟩ := refill_local (word := cmd.word) (count := cmd.count) hs hpos hw
  generalize hrf : refill cmd.word cmd.count a pos stop hs hpos = rf at r1 r2 r3 r4 r5 hbits l1 l2
  have hloc : ∀ t : List UInt8, (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits t) =
      (BitBuffer.mk rf.word rf.count).held ++ bits t := by
    intro t
    rw [← List.append_assoc, ← l1]
    rfl
  have hwhole : ∀ t : List UInt8, (bits t).length % 8 = 0 := fun t => by rw [bits_length]; omega
  have hsrc : ∀ t : List UInt8, sLeave S (.mblock w st) (Dec.bits ⟨.mblock, cmd, hd, H, k, last', left, limit, pos', status⟩ a pos stop (bits t)) =
      sLeave S (.mblock w st) ((BitBuffer.mk rf.word rf.count).held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) := by
    intro t
    show sLeave S (.mblock w st) (availBits cmd.word cmd.count a pos stop (bits t)) = _
    rw [hbits]
    rfl
  have R := metaStartFast_ok (b0 := ⟨rf.word, rf.count⟩) r1
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := sLeave S (.mblock w st)) (N := afterStart w (S.after w) st) (fun bs => rfl)
  have hval := R.ok
  have hsh0 := R.short
  generalize metaStartFast ⟨rf.word, rf.count⟩ = r at Rok Rshort Rbad hval hsh0
  have hso : ∀ t : List UInt8, r.status = .ok → sStep (.mblock w st) (Dec.bits ⟨.mblock, cmd, hd, H, k, last', left, limit, pos', status⟩ a pos stop (bits t)) =
      startPlace w st (msValue r) (r.buf.held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) := by
    intro t hs1
    show readIn 31 metaStart (availBits cmd.word cmd.count a pos stop (bits t)) _ = _
    rw [hbits]
    show readIn 31 metaStart ((BitBuffer.mk rf.word rf.count).held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) _ = _
    exact readIn_some ((hval hs1).2 _)
  cases hsr : r.status with
  | short =>
    dsimp only
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    have hstop : rf.pos = stop := r5.resolve_left (by have : (BitBuffer.mk rf.word rf.count).count = rf.count := rfl; rw [this] at h3; omega)
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨hstop, hpos, .mblock w st, ⟨rfl, r1, hallF _ _ _ _ _ _ _ _⟩, (fun t => ?_), h4, rfl, (fun _ _ _ t => (hbits _).symm), ⟨[], rfl, rfl⟩,
      (fun t => SReach.ofEq (hbits _).symm), ⟨_, _, .refl _ _, ?_, rfl⟩⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · rw [hsrc]
      rfl
    · show readIn 31 metaStart (BitBuffer.mk rf.word rf.count).held _ = _
      exact readIn_short h5 (by rw [held_len]; exact h3)
  | bad =>
    dsimp only
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨fun t => by rw [hsrc]; exact Rbad hsr _, .mblock w st, (BitBuffer.mk cmd.word cmd.count).held, pos, Nat.le_refl _, r2, r3,
        by rw [BitBuffer.held_length]; exact l2, fun t => .refl _ _, fun t => by rw [hloc]; exact Rbad hsr _⟩⟩
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    have hms := metaStart_ok (r := _) (v := msValue r) (by simpa using (hval hsr).2 [])
    have hfin : ∀ t : List UInt8, sLeave S (.mblock w st) (Dec.bits ⟨.mblock, cmd, hd, H, k, last', left, limit, pos', status⟩ a pos stop (bits t)) =
        afterStart w (S.after w) st (msValue r) (r.buf.held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) := by
      intro t
      rw [hsrc, hN]
    have hfinL : ∀ t : List UInt8, sLeave S (.mblock w st) ((BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits t)) =
        afterStart w (S.after w) st (msValue r) (r.buf.held ++ bits t) := by
      intro t
      rw [hloc, hN]
    unfold metaGo
    by_cases h0 : r.a = 0
    · rw [ite_eq_left h0]
      have hv : msValue r = .lastEmpty := by
        unfold msValue
        rw [ite_eq_left h0]
      exact ⟨fun _ => ⟨.ended st, ⟨rfl, hw2, w, hallF _ _ _ _ _ _ _ _⟩, r2, r3, (fun t => by rw [hfin, hv]; exact S.after_true ..), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one (by rw [hso t hsr, hv]; rfl))⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    rw [ite_eq_right h0]
    by_cases h1 : r.a = 1
    · rw [ite_eq_left h1]
      have hv : msValue r = .metadata (r.b != 0) r.c.toNat := by
        unfold msValue
        rw [ite_eq_right h0, ite_eq_left h1]
      rw [hv] at hfin hfinL hms
      have hms' : r.c.toNat ≤ 16777216 := hms
      obtain ⟨fa1, fa2⟩ := fill_aligned hw2
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        dsimp only
        refine ⟨fun _ => ⟨.skip w st (r.b != 0) r.c.toNat, ⟨rfl, fa2, hallF _ _ _ _ _ _ _ _, rfl, rfl, fa1, by omega⟩, r2, r3, (fun t => ?_), trivial, ⟨[], rfl, rfl⟩,
          fun t => (SReach.one ?_)⟩, fun e => DStatus.noConfusion e,
          fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
        · rw [hfin]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        · rw [hso t hsr, hv]
          show (match readFill _ with | some b => _ | none => _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
      · rw [ite_eq_right hz]
        refine ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
          fun _ => ⟨fun t => ?_, .mblock w st, (BitBuffer.mk cmd.word cmd.count).held, pos, Nat.le_refl _, r2, r3,
            by rw [BitBuffer.held_length]; exact l2, fun t => .refl _ _, fun t => ?_⟩⟩
        · rw [hfin]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_right (show ¬ r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        · show sLeave S (.mblock w st) _ = none
          rw [hfinL]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (hwhole t), ite_eq_right (show ¬ r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
    rw [ite_eq_right h1]
    have hv : msValue r = .data (r.b != 0) r.c.toNat (r.d != 0) := by
      unfold msValue
      rw [ite_eq_right h0, ite_eq_right h1]
    rw [hv] at hfin hfinL hms
    obtain ⟨hm1, hm2⟩ := (hms : 1 ≤ r.c.toNat ∧ r.c.toNat ≤ 16777216)
    obtain ⟨fa1, fa2⟩ := fill_aligned hw2
    by_cases hu : (r.d != 0) = true
    · rw [ite_eq_left hu]
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        dsimp only
        refine ⟨fun _ => ⟨.raw w st (r.b != 0) r.c.toNat, ⟨rfl, fa2, hallF _ _ _ _ _ _ _ _, rfl, rfl, by omega⟩, r2, r3, (fun t => ?_), trivial, ⟨[], rfl, rfl⟩,
          fun t => (SReach.one ?_)⟩, fun e => DStatus.noConfusion e,
          fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
        · rw [hfin]
          unfold afterStart
          rw [hu]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        · rw [hso t hsr, hv]
          unfold startPlace
          rw [hu]
          show (match readFill _ with | some b => _ | none => _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
      · rw [ite_eq_right hz]
        refine ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
          fun _ => ⟨fun t => ?_, .mblock w st, (BitBuffer.mk cmd.word cmd.count).held, pos, Nat.le_refl _, r2, r3,
            by rw [BitBuffer.held_length]; exact l2, fun t => .refl _ _, fun t => ?_⟩⟩
        · rw [hfin]
          unfold afterStart
          rw [hu]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (whole_bytes hs t), ite_eq_right (show ¬ r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        · show sLeave S (.mblock w st) _ = none
          rw [hfinL]
          unfold afterStart
          rw [hu]
          show (readFill _ >>= _) = _
          rw [readFill_held _ (hwhole t), ite_eq_right (show ¬ r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
    · rw [ite_eq_right hu]
      have hu' : (r.d != 0) = false := by simpa using hu
      refine ⟨fun _ => ⟨.hdr w st (r.b != 0) r.c.toNat Gh.start (.cat .L), ⟨rfl, ⟨hwin, hprod, hlim⟩, rfl, rfl, hm1, hm2, hdStart_rel hw2 hlim, hz0, hdStart_bud _ _ _⟩, r2, r3, (fun t => ?_), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one ?_)⟩,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      · rw [hfin]
        unfold afterStart
        rw [hu']
        exact readCompressed_eq w (S.after w (r.b != 0)) st r.c.toNat Gh.start _
      · rw [hso t hsr, hv]
        unfold startPlace
        rw [hu']
        rfl

/-! ### WBITS -/

/-- A window's first state, with the buffer as it is after WBITS. -/
def winStart (c : Cmd) (word count need : UInt64) : Cmd :=
  { c with
    word := word, count := count, ring := zeroBytes need.toNat, wpos := 0, pend := 0, written := 0, p1 := 0, p2 := 0
    d0 := 4, d1 := 11, d2 := 15, d3 := 16, wordBuf := ByteArray.empty }

/-- The place at the stream's first bits. -/
def stepDWbits (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  if hp : pos ≤ stop then
    let rf := refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let rp := rf.pos
    let r := wbitsFast ⟨rf.word, rf.count⟩
    match r.status with
    | .short => { D with cmd := { D.cmd with word := rf.word, count := rf.count }, pos := rp, status := .needsInput }
    | .bad => { D with pos := rp, status := .bad }
    | .ok =>
      let need := (1 : UInt64) <<< r.a
      if need ≤ D.limit then
        { D with tag := .mblock, cmd := winStart D.cmd r.word r.count need, k := r.a.toUSize, limit := D.limit - need, pos := rp, status := .next }
      else { D with pos := rp, status := .memory }
  else { D with pos := pos, status := .bad }

/-- WBITS is in 10..24 (§9.1). -/
theorem readWBITS_range {bs r : List Bool} {v : Nat} (h : readWBITS bs = some (v, r)) : 10 ≤ v ∧ v ≤ 24 := by
  unfold readWBITS at h
  obtain ⟨⟨wbits, n, printed⟩, hm, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only at hf
  split at hf
  · split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      rw [← hf.1]
      exact wbitsCode_range _ hm
    · cases hf
  · cases hf

theorem winStart_win {c : Cmd} {word count need : UInt64} {kv : Nat} (h10 : 10 ≤ kv) (h24 : kv ≤ 24) (hn : need.toNat = 2 ^ kv) :
    WinRel (windowSize kv) kv (winStart c word count need) [] initialDistances := by
  have hp : 2 ^ kv ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h24
  have hp1 : 2 ^ 10 ≤ 2 ^ kv := Nat.pow_le_pow_right (by decide) h10
  have h1024 : (2 : Nat) ^ 10 = 1024 := rfl
  have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
  have hws : windowSize kv + 16 = 2 ^ kv := by
    unfold windowSize
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    omega
  exact {
    win := hws
    k24 := h24
    ring := by
      have : (winStart c word count need).ring.size = 2 ^ kv := by
        show (zeroBytes need.toNat).size = _
        rw [hn, zeroBytes_size (by omega)]
      exact RingOk.empty this
    bytes := by simp
    ctx := rfl
    pendLe := Nat.zero_le _
    pendOut := Nat.zero_le _
    written := by simp; rfl
    d0 := rfl
    d1 := rfl
    d2 := rfl
    d3 := rfl
    dsLt := by decide
    wordLe := by show ByteArray.empty.size ≤ 38; decide }

theorem stepDWbits_ok {α : Type} {S : Sem α} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D .wbits) (hpos : pos.toNat ≤ stop.toNat) : DStepOk S a stop .wbits D pos (stepDWbits a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hlim, hz⟩ := hrel
  have ht' : tag = .wbits := ht
  subst ht'
  have hz' : cmd.pend = 0 := hz
  unfold stepDWbits
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hpos)]
  dsimp only
  obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := cmd.word) (count := cmd.count) hs hpos hw
  have hbits : ∀ F, availBits cmd.word cmd.count a pos stop F =
      availBits (refill cmd.word cmd.count a pos stop hs hpos).word (refill cmd.word cmd.count a pos stop hs hpos).count a
        (refill cmd.word cmd.count a pos stop hs hpos).pos stop F := by
    intro F
    show (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
      (refill cmd.word cmd.count a pos stop hs hpos).buf.held ++ (chunkBits a (refill cmd.word cmd.count a pos stop hs hpos).pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, r4]
  obtain ⟨l1, l2⟩ := refill_local (word := cmd.word) (count := cmd.count) hs hpos hw
  generalize refill cmd.word cmd.count a pos stop hs hpos = rf at r1 r2 r3 r4 r5 hbits l1 l2
  have hloc : ∀ t : List UInt8, (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits t) =
      (BitBuffer.mk rf.word rf.count).held ++ bits t := by
    intro t
    rw [← List.append_assoc, ← l1]
    rfl
  have hsrc : ∀ t : List UInt8, sLeave S .wbits (Dec.bits ⟨.wbits, cmd, hd, H, k, last', left, limit, pos', status⟩ a pos stop (bits t)) =
      sLeave S .wbits ((BitBuffer.mk rf.word rf.count).held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) := by
    intro t
    show sLeave S .wbits (availBits cmd.word cmd.count a pos stop (bits t)) = _
    rw [hbits]
    rfl
  have R := wbitsFast_ok (b0 := ⟨rf.word, rf.count⟩) r1
  obtain ⟨Rok, Rshort, Rbad⟩ := R.run (X := sLeave S .wbits) (N := fun v b => S.block (windowSize v) ⟨[], 0, initialDistances⟩ b) (fun bs => S.first_eq bs)
  have hval := R.ok
  have hsh0 := R.short
  generalize wbitsFast ⟨rf.word, rf.count⟩ = r at Rok Rshort Rbad hval hsh0
  cases hsr : r.status with
  | short =>
    dsimp only
    obtain ⟨_, _, h3, h4⟩ := Rshort hsr
    obtain ⟨_, _, _, h5⟩ := hsh0 hsr
    have hstop : rf.pos = stop := r5.resolve_left (by have : (BitBuffer.mk rf.word rf.count).count = rf.count := rfl; rw [this] at h3; omega)
    refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨hstop, hpos, .wbits, ⟨rfl, r1, hlim, hz'⟩, (fun t => ?_), h4, rfl, (fun _ _ e => SPhase.noConfusion e), ⟨[], rfl, rfl⟩,
      (fun t => SReach.ofEq (hbits _).symm), ⟨_, _, .refl _ _, ?_, rfl⟩⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · rw [hsrc]
      rfl
    · show readIn 7 readWBITS (BitBuffer.mk rf.word rf.count).held _ = _
      exact readIn_short h5 (by rw [held_len]; exact h3)
  | bad =>
    dsimp only
    exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e,
      fun _ => ⟨fun t => by rw [hsrc]; exact Rbad hsr _, .wbits, (BitBuffer.mk cmd.word cmd.count).held, pos, Nat.le_refl _, r2, r3,
        by rw [BitBuffer.held_length]; exact l2, fun t => .refl _ _, fun t => by rw [hloc]; exact Rbad hsr _⟩⟩
  | ok =>
    dsimp only
    obtain ⟨hw2, hN⟩ := Rok hsr
    obtain ⟨h10, h24⟩ := readWBITS_range (by simpa using (hval hsr).2 [])
    have hneed : ((1 : UInt64) <<< r.a).toNat = 2 ^ r.a.toNat := by
      have hpw : 2 ^ r.a.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h24
      have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
      rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show r.a.toNat < 64 by omega), Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hc : (1 : UInt64) <<< r.a ≤ limit
    · rw [ite_eq_left hc]
      have hle := UInt64.le_iff_toNat_le.mp hc
      rw [hneed] at hle
      have hus : r.a.toUSize.toNat = r.a.toNat := word_toUSize (by omega)
      have hwin := winStart_win (c := cmd) (word := r.word) (count := r.count) h10 h24 hneed
      refine ⟨fun _ => ⟨.mblock (windowSize r.a.toNat) ⟨[], 0, initialDistances⟩, ⟨rfl, hw2, ⟨?_, rfl, ?_⟩⟩, r2, r3, (fun t => ?_), trivial,
        ⟨[], rfl, by show (0 : USize).toNat = cmd.pend.toNat + 0; rw [hz']; rfl⟩, fun t => (SReach.one ?_)⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      · show WinRel _ r.a.toUSize.toNat _ _ _
        rw [hus]
        exact hwin
      · show (limit - (1 : UInt64) <<< r.a).toNat + 8888 < 2 ^ 32
        have hlim' : limit.toNat + 8888 < 2 ^ 32 := hlim
        rw [UInt64.toNat_sub_of_le _ _ hc, hneed]
        omega
      · rw [hsrc, hN]
        rfl
      · show readIn 7 readWBITS (availBits cmd.word cmd.count a pos stop (bits t)) _ = _
        rw [hbits]
        show readIn 7 readWBITS ((BitBuffer.mk rf.word rf.count).held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) _ = _
        exact readIn_some ((hval hsr).2 _)
    · rw [ite_eq_right hc]
      exact ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => ⟨r2, r3, rfl, hz', Or.inl rfl⟩,
        fun e => DStatus.noConfusion e⟩

/-! ### Metadata -/

/-- Moves on from a meta-block's data. -/
@[inline] def moveOn (D : Dec) (pos : USize) : Dec :=
  { D with tag := if D.last then .ended else .mblock, pos := pos, status := .next }

/-- The place in metadata: bytes held go first, then bytes of the chunk. -/
def stepDSkip (stop : USize) (D : Dec) (pos : USize) : Dec :=
  let left := D.left
  let c := D.cmd
  if left = 0 then moveOn D pos
  else if c.count ≠ 0 then
    let held := c.count >>> 3
    let n := if held < 7 then held else 7
    let m := if left < n then left else n
    let k := m * 8
    let b := (BitBuffer.mk c.word c.count).drop k
    { D with cmd := { c with word := b.word, count := b.count }, left := left - m, pos := pos, status := .next }
  else if pos ≤ stop then
    let room := (stop - pos).toUInt64
    let m := if left < room then left else room
    let left' := left - m
    { D with left := left', pos := pos + m.toUSize, status := if left' = 0 then .next else .needsInput }
  else { D with pos := pos, status := .bad }

/-- Skipping bits of metadata. -/
theorem skipK_drop {α : Type} (A : StreamState → List Bool → Option α) (st : StreamState) {n m : Nat} {bs : List Bool} (hm : m ≤ n) (hl : m * 8 ≤ bs.length) :
    skipK A st n bs = skipK A st (n - m) (bs.drop (m * 8)) := by
  have hn : n * 8 = m * 8 + (n - m) * 8 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  unfold skipK
  have hlen : (bs.drop (m * 8)).length = bs.length - m * 8 := List.length_drop ..
  rw [List.drop_drop, hlen, ← hn]
  by_cases h : bs.length < n * 8
  · rw [ite_eq_left h, ite_eq_left (by omega)]
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem stepDSkip_ok {α : Type} {S : Sem α} {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {D : Dec} {pos : USize}
    (hrel : DRel D (.skip w st last n)) (hpos : pos.toNat ≤ stop.toNat) : DStepOk S a stop (.skip w st last n) D pos (stepDSkip stop D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hall, hl, hleft, halign, hn32⟩ := hrel
  have ht' : tag = .skip := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  have hleft' : left.toNat = n := hleft
  obtain ⟨hwin, hprod, hlim⟩ := hall
  have halign' : cmd.count.toNat % 8 = 0 := halign
  unfold stepDSkip
  dsimp only
  by_cases h0 : left = 0
  · rw [ite_eq_left h0]
    have hn0 : n = 0 := by rw [← hleft', h0]; rfl
    subst hn0
    cases last' with
    | true =>
      exact ⟨fun _ => ⟨.ended st, ⟨rfl, hw, w, ⟨hwin, hprod, hlim⟩⟩, Nat.le_refl _, hpos, (fun t => (skipK_zero (S.after w true) st _).trans (S.after_true ..)), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one rfl)⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    | false =>
      exact ⟨fun _ => ⟨.mblock w st, ⟨rfl, hw, ⟨hwin, hprod, hlim⟩⟩, Nat.le_refl _, hpos, (fun t => (skipK_zero (S.after w false) st _).trans (S.after_false ..)), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one rfl)⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  rw [ite_eq_right h0]
  have hl0' : left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
  by_cases hc : cmd.count ≠ 0
  · rw [ite_eq_left hc]
    have hc' : cmd.count.toNat ≠ 0 := fun e => hc (UInt64.toNat_inj.mp e)
    have hheld : (cmd.count >>> 3).toNat = cmd.count.toNat / 8 := by
      rw [UInt64.toNat_shiftRight, show (3 : UInt64).toNat % 64 = 3 from rfl, Nat.shiftRight_eq_div_pow]
    have hcle := hw.count_le
    have hnv : (if cmd.count >>> 3 < 7 then cmd.count >>> 3 else 7).toNat = min (cmd.count.toNat / 8) 7 := by
      by_cases hlt : cmd.count >>> 3 < 7
      · have := UInt64.lt_iff_toNat_lt.mp hlt
        rw [hheld] at this
        rw [ite_eq_left hlt, hheld]
        have h7 : (7 : UInt64).toNat = 7 := rfl
        omega
      · have : ¬ (cmd.count >>> 3).toNat < (7 : UInt64).toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
        rw [hheld] at this
        rw [ite_eq_right hlt]
        have h7 : (7 : UInt64).toNat = 7 := rfl
        rw [h7] at this ⊢
        omega
    generalize (if cmd.count >>> 3 < 7 then cmd.count >>> 3 else 7) = nh at hnv
    have hmv : (if left < nh then left else nh).toNat = min left.toNat nh.toNat := by
      by_cases hlt : left < nh
      · have := UInt64.lt_iff_toNat_lt.mp hlt
        rw [ite_eq_left hlt]
        omega
      · have : ¬ left.toNat < nh.toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
        rw [ite_eq_right hlt]
        omega
    generalize (if left < nh then left else nh) = m at hmv
    have hmle7 : m.toNat ≤ 7 := by omega
    have hmn : m.toNat ≤ n := by omega
    have hk : (m * 8).toNat = m.toNat * 8 := by
      rw [UInt64.toNat_mul, show (8 : UInt64).toNat = 8 from rfl]
      exact Nat.mod_eq_of_lt (by omega)
    have hkle : m * 8 ≤ cmd.count := UInt64.le_iff_toNat_le.mpr (by rw [hk]; omega)
    have hk64 : (m * 8).toNat < 64 := by rw [hk]; omega
    have hw1 := drop_wf' hw hk64 hkle
    have hcnt := drop_count (b := ⟨cmd.word, cmd.count⟩) (UInt64.le_iff_toNat_le.mp hkle)
    have hsub : (left - m).toNat = n - m.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hleft']
    have hm1 : m.toNat ≠ 0 := by omega
    refine ⟨fun _ => ⟨.skip w st last' (n - m.toNat), ⟨rfl, hw1, ⟨{ hwin with }, hprod, hlim⟩, rfl, hsub, ?_, by omega⟩, Nat.le_refl _, hpos, (fun t => ?_), show n - m.toNat < n by omega, ⟨[], rfl, rfl⟩,
      fun t => ?_⟩,
      fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    rotate_right
    · have hr := sreach_skip (w := w) (st := st) (last := last') m.toNat n (availBits cmd.word cmd.count a pos stop (bits t)) hmn (by
        show m.toNat * 8 ≤ ((BitBuffer.mk cmd.word cmd.count).held ++ _).length
        simp only [List.length_append, BitBuffer.held, lowBits_length]
        omega)
      rw [← hk, avail_mk, held_drop _ hk64 hkle] at hr
      exact hr
    · show ((BitBuffer.mk cmd.word cmd.count).drop (m * 8)).count.toNat % 8 = 0
      rw [hcnt, hk]
      have : (BitBuffer.mk cmd.word cmd.count).count.toNat = cmd.count.toNat := rfl
      omega
    · show skipK (S.after w last') st n (availBits cmd.word cmd.count a pos stop (bits t)) = skipK (S.after w last') st (n - m.toNat) _
      rw [skipK_drop (S.after w last') st hmn (m := m.toNat) (by
        show m.toNat * 8 ≤ ((BitBuffer.mk cmd.word cmd.count).held ++ _).length
        simp only [List.length_append, BitBuffer.held, lowBits_length]
        omega)]
      rw [← hk]
      show skipK (S.after w last') st _ (((BitBuffer.mk cmd.word cmd.count).held ++ _).drop (m * 8).toNat) = _
      rw [held_drop _ hk64 hkle]
      rfl
  · rw [ite_eq_right hc]
    have hcz : cmd.count = 0 := by simpa using hc
    have hle : pos ≤ stop := USize.le_iff_toNat_le.mpr hpos
    rw [ite_eq_left hle]
    have hroom : (stop - pos).toUInt64.toNat = stop.toNat - pos.toNat := by
      rw [USize.toNat_toUInt64, USize.toNat_sub_of_le _ _ hle]
    have hmv : (if left < (stop - pos).toUInt64 then left else (stop - pos).toUInt64).toNat = min left.toNat (stop.toNat - pos.toNat) := by
      by_cases hlt : left < (stop - pos).toUInt64
      · have := UInt64.lt_iff_toNat_lt.mp hlt
        rw [hroom] at this
        rw [ite_eq_left hlt]
        omega
      · have : ¬ left.toNat < (stop - pos).toUInt64.toNat := fun e => hlt (UInt64.lt_iff_toNat_lt.mpr e)
        rw [hroom] at this
        rw [ite_eq_right hlt, hroom]
        omega
    generalize (if left < (stop - pos).toUInt64 then left else (stop - pos).toUInt64) = m at hmv
    have hsub : (left - m).toNat = n - m.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), hleft']
    have hpsum : (pos + m.toUSize).toNat = pos.toNat + m.toNat := by
      have hu := stop.toNat_lt_size
      have hmU : m.toUSize.toNat = m.toNat := by
        rw [word_toUSize (by omega)]
      rw [USize.toNat_add, hmU, ← USize.size_eq_two_pow]
      exact Nat.mod_eq_of_lt (by omega)
    have hheld : (BitBuffer.mk cmd.word cmd.count).held = [] := by
      unfold BitBuffer.held
      rw [hcz]
      rfl
    have hbit : ∀ t : List UInt8, skipK (S.after w last') st n (availBits cmd.word cmd.count a pos stop (bits t)) =
        skipK (S.after w last') st (n - m.toNat) (availBits cmd.word cmd.count a (pos + m.toUSize) stop (bits t)) := by
      intro t
      have hclen := chunkBits_length (input := a) (pos := pos.toNat) hs
      rw [skipK_drop (S.after w last') st (m := m.toNat) (by omega) (by
        unfold availBits
        rw [hheld, List.nil_append, List.length_append, hclen]
        rw [show (8 : Nat) = 8 from rfl]
        have : m.toNat * 8 ≤ (stop.toNat - pos.toNat) * 8 := Nat.mul_le_mul_right 8 (by omega)
        omega)]
      unfold availBits
      rw [hheld, List.nil_append, List.nil_append, hpsum, chunkBits_drop, List.drop_append_of_le_length (by rw [hclen]; have : m.toNat * 8 ≤ (stop.toNat - pos.toNat) * 8 := Nat.mul_le_mul_right 8 (by omega); omega),
        Nat.mul_comm 8 m.toNat]
    have hreach : ∀ t : List UInt8, SReach (.skip w st last' n) (availBits cmd.word cmd.count a pos stop (bits t))
        (.skip w st last' (n - m.toNat)) (availBits cmd.word cmd.count a (pos + m.toUSize) stop (bits t)) := by
      intro t
      have hclen := chunkBits_length (input := a) (pos := pos.toNat) hs
      have hm8 : m.toNat * 8 ≤ (stop.toNat - pos.toNat) * 8 := Nat.mul_le_mul_right 8 (by omega)
      have hr := sreach_skip (w := w) (st := st) (last := last') m.toNat n (availBits cmd.word cmd.count a pos stop (bits t)) (by omega) (by
        unfold availBits
        rw [hheld, List.nil_append, List.length_append, hclen]
        omega)
      have e : (availBits cmd.word cmd.count a pos stop (bits t)).drop (m.toNat * 8) =
          availBits cmd.word cmd.count a (pos + m.toUSize) stop (bits t) := by
        unfold availBits
        rw [hheld, List.nil_append, List.nil_append, hpsum, chunkBits_drop, List.drop_append_of_le_length (by rw [hclen]; omega),
          Nat.mul_comm 8 m.toNat]
      rw [e] at hr
      exact hr
    have hrel2 : ∀ s, DRel ⟨.skip, cmd, hd, H, k, last', left - m, limit, pos + m.toUSize, s⟩ (.skip w st last' (n - m.toNat)) := fun _ =>
      ⟨rfl, hw, ⟨hwin, hprod, hlim⟩, rfl, hsub, halign, by omega⟩
    by_cases hz : left - m = 0
    · rw [ite_eq_left hz]
      have hz' : (left - m).toNat = 0 := by rw [hz]; rfl
      refine ⟨fun _ => ⟨.skip w st last' (n - m.toNat), hrel2 _, ?_, ?_, (fun t => hbit t), show n - m.toNat < n by omega, ⟨[], rfl, rfl⟩,
        fun t => (hreach t)⟩,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      · show pos.toNat ≤ (pos + m.toUSize).toNat
        rw [hpsum]
        omega
      · show (pos + m.toUSize).toNat ≤ _
        rw [hpsum]
        omega
    · rw [ite_eq_right hz]
      have hnz : n - m.toNat ≠ 0 := by
        rw [← hsub]
        exact fun e => hz (UInt64.toNat_inj.mp e)
      have hpstop : pos + m.toUSize = stop := by
        apply USize.toNat_inj.mp
        rw [hpsum]
        omega
      refine ⟨fun e => DStatus.noConfusion e, fun _ => ⟨hpstop, hpos, .skip w st last' (n - m.toNat), hrel2 _, (fun t => hbit t), ?_, (if hm0 : m.toNat = 0 then Or.inr ⟨by omega, rfl⟩ else Or.inl (show n - m.toNat < n by omega)), (fun _ _ e => SPhase.noConfusion e), ⟨[], rfl, rfl⟩,
        (fun t => (hreach t)), ⟨_, _, .refl _ _, ?_, rfl⟩⟩,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
      · show skipK (S.after w last') st (n - m.toNat) (BitBuffer.mk cmd.word cmd.count).held = none
        rw [hheld]
        exact skipK_short (by simp only [List.length_nil]; omega)
      · obtain ⟨j, hj⟩ : ∃ j, n - m.toNat = j + 1 := ⟨n - m.toNat - 1, by omega⟩
        rw [hj]
        show readIn 8 (readInt 8) (BitBuffer.mk cmd.word cmd.count).held _ = _
        rw [hheld]
        exact readIn_short rfl (by simp)

/-! ### Uncompressed bytes -/

/-- A state after bytes moved into its window. -/
@[inline] def rawFinish (D0 : Dec) (c : Cmd) (left : UInt64) (n : USize) (r : RawRun) : Dec :=
  let moved := n - r.left
  { D0 with
    cmd := { c with word := r.word, count := r.count, ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2, pend := c.pend + moved,
                    written := usmin (ringSize D0.k - USize.ofNat 16) (c.written + moved) }
    left := left - moved.toUInt64
    pos := r.pos
    status := if r.left = 0 then .next else .needsInput }

/-- A stream state's window, with the stream state and its command loop state emptied of it, as `takeCmd` takes the command
loop state. -/
@[noinline] def takeRing (D : Dec) : { t : ByteArray × Dec × Cmd // t.1 = D.cmd.ring } :=
  ⟨(D.cmd.ring, clearCmd D, clearRing D.cmd), rfl⟩

/-- The place in uncompressed bytes. -/
def stepDRaw (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Dec :=
  let left := D.left
  if left = 0 then moveOn D pos
  else
    let k := D.k
    let c := D.cmd
    if h : winCheck k c.wpos c.ring = true ∧ pos ≤ stop then
      if room k c.cap ≤ c.pend then { D with pos := pos, status := .needsOutput }
      else
        let n := usmin left.toUSize (room k c.cap - c.pend)
        let word := c.word
        let count := c.count
        let wpos := c.wpos
        let p1 := c.p1
        let p2 := c.p2
        have hsize := winCheck_size h.1
        have hwp := winCheck_pos h.1
        match takeRing D with
        | ⟨(ring, D0, c1), he⟩ =>
        rawFinish D0 c1 left n
          (rawRun a stop hs (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) n word count pos ring wpos p1 p2
            (USize.le_iff_toNat_le.mp h.2) ((congrArg ByteArray.size he).trans hsize) hwp)
    else { D with pos := pos, status := .bad }

theorem rawFinish_ok {α : Type} {S : Sem α} {w : Nat} {st : StreamState} {last : Bool} {left : Nat} {a : ByteArray} {stop : USize} {cmd : Cmd} {hd : Hd} {H : Hdr} {k : USize}
    {left' limit : UInt64} {pos' pos : USize} {status : DStatus} {n : USize} {moved : List Nat} {r : RawRun}
    (hw : WinRel w k.toNat cmd st.output st.distances) (hprod : st.produced = st.output.length) (hlim : limit.toNat + 8888 < 2 ^ 32)
    (hleft : left'.toNat = left) (hl32 : left < 2 ^ 32) (hnl : n.toNat ≤ left) (hn0 : n.toNat ≠ 0) (hnp : cmd.pend.toNat + n.toNat ≤ 2 ^ k.toNat)
    (hm : RawOk a stop k.toNat cmd.word cmd.count pos st.output n.toNat moved r) :
    DStepOk S a stop (.raw w st last left) ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩ pos
      (rawFinish (clearCmd ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩) (clearRing cmd) left' n r) := by
  have hk24 := hw.k24
  have hp24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk24
  have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
  have hlen := hm.len
  have hml : (n - r.left).toNat = moved.length := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
    omega
  have hmU : (n - r.left).toUInt64.toNat = moved.length := by
    rw [USize.toNat_toUInt64, hml]
  have hsub : (left' - (n - r.left).toUInt64).toNat = r.left.toNat + (left - n.toNat) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hmU]; omega)), hmU, hleft]
    omega
  have hle := hw.pendLe
  have hout := hw.pendOut
  have hwr := hw.written
  have hpend : (cmd.pend + (n - r.left)).toNat = cmd.pend.toNat + moved.length := by
    rw [pend_after hk24 (by rw [hml]; omega), hml]
  have hwritten : (usmin (ringSize k - USize.ofNat 16) (cmd.written + (n - r.left))).toNat = min w (cmd.written.toNat + moved.length) := by
    have := written_after (W := w) (written := cmd.written) (run := n - r.left) (k := k) hk24 hw.win (by omega) (by rw [hml]; omega) rfl
    rw [this, hml]
  let st' : StreamState := ⟨moved.reverse ++ st.output, st.produced + moved.length, st.distances⟩
  have hrel2 : DRel (rawFinish (clearCmd ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩) (clearRing cmd) left' n r)
      (.raw w st' last (r.left.toNat + (left - n.toNat))) := by
    refine ⟨rfl, hm.wf, ⟨?_, ?_, hlim⟩, rfl, hsub, by omega⟩
    · exact {
        win := hw.win
        k24 := hk24
        ring := hm.ring
        bytes := by
          intro b hb
          rcases List.mem_append.mp hb with h | h
          · exact hm.bytes b (List.mem_reverse.mp h)
          · exact hw.bytes b h
        ctx := hm.ctx
        pendLe := by
          show (cmd.pend + (n - r.left)).toNat ≤ 2 ^ k.toNat
          rw [hpend]
          omega
        pendOut := by
          show (cmd.pend + (n - r.left)).toNat ≤ _
          rw [hpend, List.length_append, List.length_reverse]
          omega
        written := by
          show (usmin (ringSize k - USize.ofNat 16) (cmd.written + (n - r.left))).toNat = _
          rw [hwritten, List.length_append, List.length_reverse]
          omega
        d0 := hw.d0
        d1 := hw.d1
        d2 := hw.d2
        d3 := hw.d3
        dsLt := hw.dsLt
        wordLe := hw.wordLe }
    · show st.produced + moved.length = (moved.reverse ++ st.output).length
      rw [List.length_append, List.length_reverse]
      omega
  have hbit : ∀ t : List UInt8, sLeave S (.raw w st last left) (availBits cmd.word cmd.count a pos stop (bits t)) =
      srest S (.raw w st' last (r.left.toNat + (left - n.toNat))) (availBits r.word r.count a r.pos stop (bits t)) := by
    intro t
    show rawK (S.after w last) st left _ = rawK (S.after w last) st' _ _
    have := hm.bits (S.after w last) st (left - n.toNat) (bits t) rfl
    rwa [show n.toNat + (left - n.toNat) = left by omega] at this
  have hposle := hm.posLe
  have hposst := hm.posStop
  have hstatus : (rawFinish (clearCmd ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩) (clearRing cmd) left' n r).status =
      if r.left = 0 then .next else .needsInput := rfl
  have hoD : OutD (.raw w st last left) (.raw w st' last (r.left.toNat + (left - n.toNat))) ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩
      (rawFinish (clearCmd ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩) (clearRing cmd) left' n r) :=
    ⟨moved.reverse, rfl, by
      show (cmd.pend + (n - r.left)).toNat = _
      rw [hpend, List.length_reverse]⟩
  have hreach : ∀ t : List UInt8, SReach (.raw w st last left) (availBits cmd.word cmd.count a pos stop (bits t))
      (.raw w st' last (r.left.toNat + (left - n.toNat))) (availBits r.word r.count a r.pos stop (bits t)) := by
    intro t
    have := hm.reach w last st (left - n.toNat) (bits t) rfl
    rwa [show n.toNat + (left - n.toNat) = left by omega] at this
  refine ⟨fun hs0 => ⟨_, hrel2, hposle, hposst, hbit, ?_, hoD, fun t => (hreach t)⟩, fun hs0 => ?_, fun hs0 => ?_, fun hs0 => ?_, fun hs0 => ?_⟩
  · rw [hstatus] at hs0
    by_cases h0 : r.left = 0
    · have h0N : r.left.toNat = 0 := by rw [h0]; rfl
      show r.left.toNat + (left - n.toNat) < left
      omega
    · rw [ite_eq_right h0] at hs0
      cases hs0
  · rw [hstatus] at hs0
    by_cases h0 : r.left = 0
    · rw [ite_eq_left h0] at hs0
      cases hs0
    · have hne : r.left.toNat ≠ 0 := fun e => h0 (USize.toNat_inj.mp e)
      obtain ⟨hc8, hst⟩ := hm.short hne
      have hdeq : SDownEq (.raw w st last left) (.raw w st' last (r.left.toNat + (left - n.toNat)))
          ((rawFinish (clearCmd ⟨.raw, cmd, hd, H, k, last, left', limit, pos', status⟩) (clearRing cmd) left' n r).cmd.pend = cmd.pend) := by
        by_cases hm0 : moved.length = 0
        · refine Or.inr ⟨by omega, ?_⟩
          apply USize.toNat_inj.mp
          show (cmd.pend + (n - r.left)).toNat = _
          rw [hpend]
          omega
        · exact Or.inl (show r.left.toNat + (left - n.toNat) < left by omega)
      refine ⟨hst, Nat.le_trans hposle hposst, _, hrel2, hbit, ?_, hdeq, (fun _ _ e => SPhase.noConfusion e), hoD,
        (fun t => (hreach t)), ⟨_, _, .refl _ _, ?_, rfl⟩⟩
      · exact rawK_short (b := ⟨r.word, r.count⟩) (by omega) hc8
      · obtain ⟨j, hj⟩ : ∃ j, r.left.toNat + (left - n.toNat) = j + 1 := ⟨r.left.toNat + (left - n.toNat) - 1, by omega⟩
        rw [hj]
        show readIn 8 (readInt 8) (BitBuffer.mk r.word r.count).held _ = _
        exact readIn_short (readInt_short (b := ⟨r.word, r.count⟩) hc8) (by rw [held_len]; exact hc8)
  · rw [hstatus] at hs0
    split at hs0 <;> cases hs0
  · rw [hstatus] at hs0
    split at hs0 <;> cases hs0
  · rw [hstatus] at hs0
    split at hs0 <;> cases hs0

theorem stepDRaw_ok {α : Type} {S : Sem α} {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.raw w st last n)) (hpos : pos.toNat ≤ stop.toNat) : DStepOk S a stop (.raw w st last n) D pos (stepDRaw a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hall, hl, hleft, hn32⟩ := hrel
  have ht' : tag = .raw := ht
  subst ht'
  have hl0 : last' = last := hl
  subst hl0
  have hleft' : left.toNat = n := hleft
  obtain ⟨hwin, hprod, hlim⟩ := hall
  have hwin' : WinRel w k.toNat cmd st.output st.distances := hwin
  unfold stepDRaw
  dsimp only
  by_cases h0 : left = 0
  · rw [ite_eq_left h0]
    have hn0 : n = 0 := by rw [← hleft', h0]; rfl
    subst hn0
    cases last' with
    | true =>
      exact ⟨fun _ => ⟨.ended st, ⟨rfl, hw, w, ⟨hwin, hprod, hlim⟩⟩, Nat.le_refl _, hpos, (fun t => (rawK_zero (S.after w true) st _).trans (S.after_true ..)), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one rfl)⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    | false =>
      exact ⟨fun _ => ⟨.mblock w st, ⟨rfl, hw, ⟨hwin, hprod, hlim⟩⟩, Nat.le_refl _, hpos, (fun t => (rawK_zero (S.after w false) st _).trans (S.after_false ..)), trivial, ⟨[], rfl, rfl⟩,
        fun t => (SReach.one rfl)⟩, fun e => DStatus.noConfusion e,
        fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  rw [ite_eq_right h0]
  have hl0' : left.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp e)
  have hk24 := hwin'.k24
  have hring := hwin'.ring
  have hck : winCheck k cmd.wpos cmd.ring = true := winCheck_of hk24 hring.size hring.pos_lt
  have hle : pos ≤ stop := USize.le_iff_toNat_le.mpr hpos
  rw [dite_eq_left (⟨hck, hle⟩ : winCheck k cmd.wpos cmd.ring = true ∧ pos ≤ stop)]
  by_cases hf : room k cmd.cap ≤ cmd.pend
  · rw [ite_eq_left hf]
    refine ⟨fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e, fun _ => ⟨.raw w st last' n, ⟨rfl, hw, ⟨hwin, hprod, hlim⟩, rfl, hleft, hn32⟩, Nat.le_refl _, hpos, (fun t => rfl), ?_, Or.inr ⟨rfl, rfl⟩, (fun _ _ e => SPhase.noConfusion e), ⟨[], rfl, rfl⟩,
      fun t => SReach.refl _ _⟩, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    exact full_ne hk24 hf
  · rw [ite_eq_right hf]
    have hpn := room_lt hf
    have hRl := room_le (cap := cmd.cap) hk24
    have hple := hwin'.pendLe
    have hp24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk24
    have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
    have hroom : (room k cmd.cap - cmd.pend).toNat = (room k cmd.cap).toNat - cmd.pend.toNat := room_sub' (by omega)
    have hu : left.toUSize.toNat = n := by
      rw [word_toUSize (by omega), hleft']
    have hnv : (usmin left.toUSize (room k cmd.cap - cmd.pend)).toNat = min n ((room k cmd.cap).toNat - cmd.pend.toNat) := by
      rw [usmin_toNat, hu, hroom]
    obtain ⟨moved, hm⟩ := rawRun_spec (a := a) (stop := stop) (hs := hs) (winCheck_k hck) (ringMask_toNat (winCheck_k hck)) _ (usmin left.toUSize (room k cmd.cap - cmd.pend))
      cmd.word cmd.count pos cmd.ring cmd.wpos cmd.p1 cmd.p2 (USize.le_iff_toNat_le.mp hle) (winCheck_size hck) (winCheck_pos hck) st.output rfl hw hring hwin'.ctx
    exact rawFinish_ok hwin' hprod hlim hleft' hn32 (by omega) (by omega) (by omega) hm

end Brotli.Decoder
