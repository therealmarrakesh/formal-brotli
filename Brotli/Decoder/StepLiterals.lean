module

public import Brotli.Decoder.StepRead

@[expose] public section

/-!
# The literals' step

A step in a command's literals does one of these: moves on to the distance, switches block, pauses with the window
full, or runs the literal loop for as many literals as the command, the block and the window allow.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- A cheap check that a buffer is well formed, for the literal loop's entry. -/
@[inline] def wfCheck (word count : UInt64) : Bool :=
  decide (count ≤ 64) && (decide (count = 64) || decide (word >>> count = 0))

theorem wfCheck_wf {word count : UInt64} (h : wfCheck word count = true) : (BitBuffer.mk word count).Wf := by
  simp only [wfCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hc := UInt64.le_iff_toNat_le.mp h1
  have h64 : (64 : UInt64).toNat = 64 := rfl
  rw [h64] at hc
  refine ⟨hc, ?_⟩
  show word.toNat < 2 ^ count.toNat
  by_cases he : count.toNat = 64
  · rw [he]
    exact word.toNat_lt
  · rcases h2 with h2 | h2
    · exact absurd (by rw [h2]; rfl) he
    · have hz := congrArg UInt64.toNat h2
      rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow] at hz
      exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).mp hz

theorem wfCheck_of_wf {word count : UInt64} (h : (BitBuffer.mk word count).Wf) : wfCheck word count = true := by
  have hc : count.toNat ≤ 64 := h.count_le
  have hw : word.toNat < 2 ^ count.toNat := h.word_lt
  have h64 : (64 : UInt64).toNat = 64 := rfl
  simp only [wfCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨UInt64.le_iff_toNat_le.mpr (by rw [h64]; exact hc), ?_⟩
  by_cases he : count.toNat = 64
  · exact Or.inl (UInt64.toNat_inj.mp (by rw [he]; rfl))
  · refine Or.inr (UInt64.toNat_inj.mp ?_)
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hw

/-- A literal step's new state, around the loop's result. Not inlined, so the state stays live across the loop and is
reused here. -/
@[noinline] def finishLiterals (st0 : Cmd) (r : LitRun) (run size : USize) : Cmd :=
  let used := run - r.left
  { st0 with
    word := r.word, count := r.count, ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
    left := st0.left - used.toUInt64, lCount := st0.lCount - used.toUInt64, remaining := st0.remaining - used.toUInt64
    pend := st0.pend + used
    written := usmin (size - USize.ofNat 16) (st0.written + used)
    pos := r.pos, status := if r.left = 0 then .next else .needsInput }

theorem cur_small {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) : t.toNat < 2 ^ 26 := by
  have h1 := H.lit.map32
  have h2 := H.lMapSize
  omega

theorem cur_usize {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) : t.toUSize.toNat = t.toNat := by
  have := cur_small ht
  exact word_toUSize (by omega)

theorem mapBase_toNat {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) : (t <<< 6).toUSize.toNat = 64 * t.toNat := by
  have hs := cur_small ht
  have hv : (t <<< 6).toNat = 64 * t.toNat := by
    rw [UInt64.toNat_shiftLeft, show (6 : UInt64).toNat % 64 = 6 from rfl, Nat.shiftLeft_eq]
    have : t.toNat * 2 ^ 6 = 64 * t.toNat := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  rw [word_toUSize (by rw [hv]; omega), hv]

theorem modeOff_toNat {m : UInt8} (h : m.toNat < 4) : (m.toUInt64 <<< 9).toUSize.toNat = 512 * m.toNat := by
  have hv : (m.toUInt64 <<< 9).toNat = 512 * m.toNat := by
    rw [UInt64.toNat_shiftLeft, show (9 : UInt64).toNat % 64 = 9 from rfl, Nat.shiftLeft_eq, UInt8.toNat_toUInt64]
    have : m.toNat * 2 ^ 9 = 512 * m.toNat := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)
  rw [word_toUSize (by rw [hv]; omega), hv]

theorem mapBase_le {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) : (t <<< 6).toUSize.toNat + 64 ≤ H.lMap.size := by
  rw [mapBase_toNat ht, H.lMapSize]
  omega

/-! ### Block types whose contexts share one table -/

theorem triv_idx {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) : 4 * t.toUSize.toNat + 4 ≤ H.lTriv.size := by
  rw [cur_usize ht, H.trivSize]
  omega

theorem triv32 (H : Hdr) : H.lTriv.size < 2 ^ 32 := by
  have h1 := H.lit.map32
  have h2 := H.lMapSize
  have h3 := H.trivSize
  omega

/-- The table base all of block type `t`'s contexts share, or `0xFFFFFFFF`. -/
@[inline] def trivBase (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) : UInt64 :=
  slotWord H.lTriv t.toUSize (triv_idx ht) (triv32 H)

/-- A shared base is each context's table base, and so a table that fits. -/
theorem trivBase_spec {H : Hdr} {t : UInt64} (ht : t.toNat < H.nL.toNat) (hne : ¬ trivBase H t ht = 4294967295) :
    TableFits H.arena (trivBase H t ht).toUSize.toNat ∧
      ∀ c, c < 64 → u32At H.litBase (H.lMap.data[(t <<< 6).toUSize.toNat + c]?.getD 0).toNat =
        (trivBase H t ht).toUSize.toNat := by
  have hv : (trivBase H t ht).toNat = u32At H.lTriv t.toNat := by
    unfold trivBase
    rw [slotWord_toNat, cur_usize ht]
  have hu : (trivBase H t ht).toUSize.toNat = u32At H.lTriv t.toNat := by
    rw [word_toUSize (by rw [hv]; exact u32At_lt _ _), hv]
  have hne' : u32At H.lTriv t.toNat ≠ 4294967295 := fun e => hne (UInt64.toNat_inj.mp (by rw [hv, e]; rfl))
  have hall := H.trivOk _ ht hne'
  rw [hu, mapBase_toNat ht]
  refine ⟨?_, hall⟩
  have hp : 64 * t.toNat < H.lMap.size := by
    rw [H.lMapSize]
    omega
  have hpu : (USize.ofNat (64 * t.toNat)).toNat = 64 * t.toNat := by
    rw [USize.toNat_ofNat', Nat.mod_eq_of_lt]
    have h1 := USize.le_size
    have h2 := H.lit.map32
    rw [USize.size_eq_two_pow] at h1
    omega
  have htree := H.lit.treeLt (USize.ofNat (64 * t.toNat)) (by rw [hpu]; exact hp)
  rw [uget_lit, hpu] at htree
  have e0 := hall 0 (by decide)
  rw [Nat.add_zero] at e0
  rw [← e0]
  exact H.lit.fits _ htree

/-- The literal loop for block type `t`: the loop that skips the context when all the type's contexts share a table,
the loop otherwise. -/
@[inline] def literalRunS (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) (a : ByteArray) (stop : USize)
    (hs : stop.toNat ≤ a.size) (modeOff mask : USize) (k : Nat) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : LitRun :=
  if hb : trivBase H t ht = 4294967295 then
    literalRun H.lit a stop hs (t <<< 6).toUSize modeOff mask k (mapBase_le ht) hm hd hmask hk n word count pos wpos ring
      p1 p2 hp hw hsize hwp
  else
    literalRunT H.arena H.lit.arena32 (trivBase H t ht).toUSize (trivBase_spec ht hb).1 a stop hs mask k hmask n word count
      pos wpos ring p1 p2 hp hw hsize hwp

/-- The selected loop is the loop. -/
theorem literalRunS_eq (H : Hdr) (t : UInt64) (ht : t.toNat < H.nL.toNat) (a : ByteArray) (stop : USize)
    (hs : stop.toNat ≤ a.size) (modeOff mask : USize) (k : Nat) (hm : modeOff.toNat + 512 ≤ 2048)
    (hd : modeOff.toNat % 512 = 0) (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) (n : USize) (word count : UInt64)
    (pos wpos : USize) (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) :
    literalRunS H t ht a stop hs modeOff mask k hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp =
      literalRun H.lit a stop hs (t <<< 6).toUSize modeOff mask k (mapBase_le ht) hm hd hmask hk n word count pos wpos ring
        p1 p2 hp hw hsize hwp := by
  unfold literalRunS
  by_cases hb : trivBase H t ht = 4294967295
  · rw [dite_eq_left hb]
  · rw [dite_eq_right hb]
    exact literalRunT_eq H.lit _ _ a stop hs _ modeOff mask k _ hm hd hmask hk (trivBase_spec ht hb).2 _ n word count pos
      wpos ring p1 p2 hp hw hsize hwp rfl

/-- Runs the literal loop. -/
def literalsRun (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Cmd :=
  if ht : st.lCur < H.nL then
    have ht' := UInt64.lt_iff_toNat_lt.mp ht
    have hm : st.lCur.toUSize.toNat < H.modes.size := by
      rw [cur_usize ht', H.modesSize]
      exact ht'
    have hmLt := H.modesLt _ hm
    if h : winCheck k st.wpos st.ring = true ∧ pos ≤ stop ∧ wfCheck st.word st.count = true then
      let run := (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize
      let ring := st.ring
      let st0 := clearRing st
      let r := literalRunS H st.lCur ht' a stop hs ((H.modes.uget st.lCur.toUSize hm).toUInt64 <<< 9).toUSize
        (ringMask k) k.toNat
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (by
          rw [modeOff_toNat hmLt]
          omega)
        (ringMask_toNat (winCheck_k h.1)) (winCheck_k h.1) run st0.word st0.count pos st0.wpos ring st0.p1 st0.p2
        (USize.le_iff_toNat_le.mp h.2.1) (wfCheck_wf h.2.2) (winCheck_size h.1) (winCheck_pos h.1)
      finishLiterals st0 r run (ringSize k)
    else markStep st pos .bad
  else markStep st pos .bad

/-- A step in a command's literals. -/
def stepLiterals (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Cmd :=
  if st.left = 0 then { st with tag := .distance, pos := pos, status := .next }
  else if st.lCount = 0 then
    if hn : 2 ≤ H.nL then
      let hn' := UInt64.le_iff_toNat_le.mp hn
      let r := blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL (H.swL hn').1 (H.swL hn').2 H.nL st.lCur st.lPrev
        st.word st.count
      match r.status with
      | .ok =>
        { st with
          word := r.word, count := r.count, lCount := r.blockCount, ext := { st.ext with lCur := r.cur, lPrev := st.lCur }
          flags := { st.flags with
            fL0 := markWord st.flags.fL0 r.cur 0, fL1 := markWord st.flags.fL1 r.cur 1, fL2 := markWord st.flags.fL2 r.cur 2
            fL3 := markWord st.flags.fL3 r.cur 3 }
          pos := pos, status := .next }
      | .short => markStep st pos .needsInput
      | .bad => markStep st pos .bad
    else markStep st pos .bad
  else if room k st.cap ≤ st.pend then markStep st pos .needsOutput
  else literalsRun H k a stop hs st pos

/-- What follows the literal loop, whatever it returned. -/
private theorem literals_after {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState}
    {out : List Nat} {st : Cmd} {pos : USize}
    (hC : Core w k.toNat m st out (s.remaining - (ilen - n)) s.distances ic lit s.distance) (htag : st.tag = .literals)
    (hprod : s.produced = s.output.length) (hcode : st.code.toNat = c) (hilen : st.ilen.toNat = ilen)
    (hclen : st.clen.toNat = clen) (hleft : st.left.toNat = n) (hnle : n ≤ ilen) (hirem : ilen ≤ s.remaining)
    (hlen : out.length + n = s.output.length + ilen) (hp : pos.toNat ≤ stop.toNat) (r : LitRun) {run : USize}
    (hrun0 : run.toNat ≠ 0) (hrunL : run.toNat ≤ n) (hrunC : run.toNat ≤ st.lCount.toNat) (hrunR : run.toNat + st.pend.toNat + 16 ≤ 2 ^ k.toNat)
    (hspec : ∃ (lit' : BlockState) (out' : List Nat),
      r.left.toNat ≤ run.toNat ∧ lit'.types = lit.types ∧ lit'.seen = lit.seen ∧ lit'.count = lit.count - (run.toNat - r.left.toNat) ∧
      out'.length = out.length + (run.toNat - r.left.toNat) ∧ (∃ l, out' = l ++ out) ∧ RingOk r.ring k.toNat r.wpos.toNat out' ∧
      contextBytes out' = (r.p1.toNat, r.p2.toNat) ∧ (BitBuffer.mk r.word r.count).Wf ∧
      pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ (∀ b ∈ out', b < 256) ∧
      (∀ F, rest w m K (.literals s ic c ilen clen n lit out) (availBits st.word st.count a pos stop F) =
        rest w m K (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') (availBits r.word r.count a r.pos stop F)) ∧
      (r.left.toNat ≠ 0 → r.pos = stop ∧
        rest w m K (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') (BitBuffer.mk r.word r.count).held = none ∧
        CShort w m (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') (BitBuffer.mk r.word r.count).held) ∧
      (∀ F, Reach (cStep w m) (.literals s ic c ilen clen n lit out) (availBits st.word st.count a pos stop F)
        (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') (availBits r.word r.count a r.pos stop F))) :
    StepOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out) st pos (finishLiterals (clearRing st) r run (ringSize k)) := by
  obtain ⟨lit', out', h1, h2, h3, h4, h5, ⟨lx, hlx⟩, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hspec
  have hk := hC.k24
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hwin := hC.win
  have hrem := hC.rem
  have hple := hC.pendLe
  have hpo := hC.pendOut
  have hwri := hC.written
  have hlcount : lit.count = st.lCount.toNat := hC.lRel.count
  have huN : (run - r.left).toNat = run.toNat - r.left.toNat :=
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h1)
  have huU : (run - r.left).toUInt64.toNat = run.toNat - r.left.toNat := by
    rw [USize.toNat_toUInt64, huN]
  have hnew : Rel w k.toNat m (finishLiterals (clearRing st) r run (ringSize k))
      (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') := by
    refine ⟨?_, htag, hprod, hcode, hilen, hclen, ?_, by omega, hirem, by omega⟩
    · refine { hC with
        wf := h8, ring := h6, bytes := h11, ctx := h7, pendLe := ?_, pendOut := ?_, written := ?_, rem := ?_
        lRel := hC.lRel.run h2 h3 ?_ }
      · show (st.pend + (run - r.left)).toNat + 16 ≤ _
        rw [pend_after hk (by rw [huN]; omega), huN]
        omega
      · show (st.pend + (run - r.left)).toNat ≤ _
        rw [pend_after hk (by rw [huN]; omega), huN, h5]
        omega
      · show (usmin (ringSize k - USize.ofNat 16) (st.written + (run - r.left))).toNat = _
        rw [written_after hk hwin (by omega) (by rw [huN]; omega) rfl, huN, h5, hwri]
        omega
      · show (st.remaining - (run - r.left).toUInt64).toNat = _
        rw [u64_sub (by rw [huU]; omega), huU]
        omega
      · show lit'.count = (st.lCount - (run - r.left).toUInt64).toNat
        rw [u64_sub (by rw [huU]; omega), huU, h4]
        omega
    · show (st.left - (run - r.left).toUInt64).toNat = _
      rw [u64_sub (by rw [huU]; omega), huU]
      omega
  have hoAll : OutStep (.literals s ic c ilen clen n lit out) (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out') st
      (finishLiterals (clearRing st) r run (ringSize k)) := by
    refine ⟨lx, hlx, ?_⟩
    have hll : lx.length = run.toNat - r.left.toNat := by
      have := congrArg List.length hlx
      rw [List.length_append] at this
      omega
    show (st.pend + (run - r.left)).toNat = _
    rw [pend_after hk (by rw [huN]; omega), huN, hll]
  by_cases hz : r.left = 0
  · have hz0 : r.left.toNat = 0 := by rw [hz]; rfl
    have hdn : (rankC (.literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out')).2 < (rankC (.literals s ic c ilen clen n lit out)).2 := by
      simp only [rankC]
      split <;> split <;> omega
    exact StepOk.ofNext (p' := .literals s ic c ilen clen (n - (run.toNat - r.left.toNat)) lit' out')
      (hd := Or.inr (Or.inr ⟨rfl, hdn⟩)) (hout := hoAll) (by show (if r.left = 0 then _ else _) = _; rw [ite_eq_left hz]) hnew h9 h10
      (fun F => h12 F) (fun F => h14 F)
  · obtain ⟨hstop, hnone, hcs⟩ := h13 (usize_ne hz)
    refine StepOk.ofInput (by show (if r.left = 0 then _ else _) = _; rw [ite_eq_right hz]) hstop hp hnew (fun F => h12 F) hnone ?_ hoAll
      (fun F => h14 F) hcs
    by_cases hu : run.toNat - r.left.toNat = 0
    · refine Or.inr ⟨?_, ?_⟩
      · simp only [rankC, hu, h4, Nat.sub_zero]
      · apply USize.toNat_inj.mp
        show (st.pend + (run - r.left)).toNat = _
        rw [pend_after hk (by rw [huN]; omega), huN]
        omega
    · refine Or.inl (Or.inr ⟨rfl, ?_⟩)
      simp only [rankC]
      split <;> split <;> omega

/-- The literal loop's step does its job. -/
theorem literalsRun_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat}
    {lit : BlockState} {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st (.literals s ic c ilen clen n lit out)) (hp : pos.toNat ≤ stop.toNat)
    (hl0 : st.left.toNat ≠ 0) (hc0 : st.lCount.toNat ≠ 0) (hroom : st.pend.toNat < (room k st.cap).toNat) :
    StepOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out) st pos (literalsRun H k a stop hs st pos) := by
  obtain ⟨hC, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ := hrel
  have hk := hC.k24
  have hRl := room_le16 (cap := st.cap) hk (by have := hC.win; omega)
  have hRmax : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hple := hC.pendLe
  have ht : st.lCur.toNat < H.nL.toNat := by
    rw [hH.nL, ← hC.lRel.cur]
    exact hC.lRel.wf.2.1
  have hum := cur_usize ht
  have hm : st.lCur.toUSize.toNat < H.modes.size := by
    rw [hum, H.modesSize]
    exact ht
  have hmodeLt := H.modesLt _ hm
  have hmodeSpec := hH.modes _ hm
  rw [hum] at hmodeSpec
  have hmapB := mapBase_toNat ht
  have hmodeO := modeOff_toNat hmodeLt
  unfold literalsRun
  rw [dite_eq_left (UInt64.lt_iff_toNat_lt.mpr ht)]
  have hguard : winCheck k st.wpos st.ring = true ∧ pos ≤ stop ∧ wfCheck st.word st.count = true :=
    ⟨winCheck_of hk hC.ring.size hC.ring.pos_lt, USize.le_iff_toNat_le.mpr hp, wfCheck_of_wf hC.wf⟩
  rw [dite_eq_left hguard]
  dsimp only
  rw [literalRunS_eq]
  dsimp only [clearRing]
  have hmodeNat : m.contextModes[st.lCur.toNat]? =
      some (((H.modes.uget st.lCur.toUSize hm).toUInt64 <<< 9).toUSize.toNat / 512) := by
    rw [hmodeO, hmodeSpec]
    congr 1
    omega
  have hrunU : (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize.toNat =
      min st.left.toNat (min st.lCount.toNat ((room k st.cap).toNat - st.pend.toNat)) := by
    rw [word_toUSize (by rw [umin_toNat, umin_toNat, room_sub (by omega)]; omega), umin_toNat, umin_toNat, room_sub (by omega)]
  have hlcount : lit.count = st.lCount.toNat := hC.lRel.count
  have hspec := literalRun_spec H.lit hs (mapBase := (st.lCur <<< 6).toUSize)
    (modeOff := ((H.modes.uget st.lCur.toUSize hm).toUInt64 <<< 9).toUSize) (mask := ringMask k) (k := k.toNat)
    (by
      rw [mapBase_toNat ht, H.lMapSize]
      omega)
    (by rw [hmodeO]; omega) (by rw [hmodeO]; omega) (ringMask_toNat hk) hk hH.lit
    (w := w) (K := K) (t := st.lCur.toNat) hmapB hmodeNat s ic c ilen clen _
    (umin st.left (umin st.lCount (room k st.cap - st.pend).toUInt64)).toUSize st.word st.count pos st.wpos st.ring st.p1 st.p2
    hp hC.wf hC.ring.size hC.ring.pos_lt n lit out rfl (by omega) (by omega)
    hC.lRel.cur hC.ctx hC.ring hC.bytes
  dsimp only at hspec
  exact literals_after hC htag hprod hcode hilen hclen hleft hnle hirem hlen hp _ (by omega) (by omega) (by omega) (by omega) hspec

/-- The literals' step does its job. -/
theorem stepLiterals_ok {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat}
    {lit : BlockState} {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st (.literals s ic c ilen clen n lit out)) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out) st pos (stepLiterals H k a stop hs st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ := hrel
  have hrem := hC.rem
  unfold stepLiterals
  split
  · rename_i hz
    have hn0 : n = 0 := by
      have := u64_zero hz
      omega
    subst hn0
    refine StepOk.ofNext (p' := .distance (withLiterals s ic lit out ilen) c clen) rfl ⟨?_, rfl, ?_, hcode, hclen⟩
      (Nat.le_refl _) hp (fun F => rest_literals_distance _) (fun F => Reach.one rfl)
    · refine { hC with rem := ?_ }
      show st.remaining.toNat = s.remaining - ilen
      omega
    · show s.produced + ilen = out.length
      omega
  · rename_i hnz
    have hnzN := u64_ne hnz
    have hn0 : n ≠ 0 := by omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    split
    · rename_i hcnt
      have hcntN := u64_zero hcnt
      have hcz : lit.count = 0 := by
        rw [hC.lRel.count]
        exact hcntN
      split
      · rename_i hn
        have hn' : 2 ≤ H.nL.toNat := UInt64.le_iff_toNat_le.mp hn
        have hn2 : 2 ≤ m.literal.n := by
          rw [← hH.nL]
          exact hn'
        have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swL hn').1) (hCt := (H.swL hn').2) hH.nL hH.catL
          hH.ok.literal hC.lRel hcntN hC.wf hn2
        dsimp only at hsp ⊢
        generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
        obtain ⟨hok, hshort, hbad⟩ := hsp
        cases hst : r.status with
        | ok =>
          obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hst
          have h256 := hH.ok.literal.2.1
          have hdn : (rankC (.literals s ic c ilen clen (n' + 1) ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat, r.cur.toNat :: lit.seen⟩ out)).2 <
              (rankC (.literals s ic c ilen clen (n' + 1) lit out)).2 := by
            simp only [rankC, hcz, ↓reduceIte]
            rw [ite_eq_right (show ¬ r.blockCount.toNat = 0 by omega)]
            omega
          refine StepOk.ofNext (p' := .literals s ic c ilen clen (n' + 1)
            ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat, r.cur.toNat :: lit.seen⟩ out)
            (hd := Or.inr (Or.inr ⟨rfl, hdn⟩)) rfl
            ⟨?_, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ (Nat.le_refl _) hp (fun F => ?_)
            (fun F => Reach.one (by
              rw [stateBits_eq]
              show (if lit.count = 0 then _ else _) = _
              rw [ite_eq_left hcz, nextIn_some (fun h => absurd h.2 (by omega)) (hnext _)]
              show ORes.next (Phase.literals s ic c ilen clen (n' + 1) ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat - 1 + 1, r.cur.toNat :: lit.seen⟩ out) _ = _
              rw [show r.blockCount.toNat - 1 + 1 = r.blockCount.toNat by omega]
              rfl))
          · exact { hC with
              wf := hw
              lRel := hC.lRel.switched hlt h256 rfl }
          · rw [stateBits_eq, stateBits_eq, rest_literal, rest_literal, hnext,
              nextElement_count (st := ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat, r.cur.toNat :: lit.seen⟩) _
                (by show r.blockCount.toNat ≠ 0; omega)]
        | short =>
          obtain ⟨_, _, hc54, hnone⟩ := hshort hst
          refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_ (by
            show (if lit.count = 0 then _ else _) = _
            rw [ite_eq_left hcz]
            exact nextIn_short (fun h => absurd h.2 (by omega)) hnone (by simp only [BitBuffer.held_length]; omega))
          rw [rest_literal, hnone]
          rfl
        | bad =>
          refine StepOk.ofBad rfl fun F => ?_
          rw [stateBits_eq, rest_literal, hbad hst]
          rfl
      · rename_i hn
        have hn' : m.literal.n < 2 := by
          rw [← hH.nL]
          exact Nat.lt_of_not_le fun e => hn (UInt64.le_iff_toNat_le.mpr e)
        refine StepOk.ofBad rfl fun F => ?_
        rw [rest_literal, nextElement_single _ hcz hn']
        rfl
    · rename_i hcnt
      split
      · rename_i hroom
        exact StepOk.ofFull hrel0 hp (full_ne hC.k24 hC.k10 hroom)
      · rename_i hroom
        exact literalsRun_ok hH hrel0 hp hnzN (u64_ne hcnt) (room_lt hroom)

end Brotli.Decoder
