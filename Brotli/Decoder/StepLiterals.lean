import Brotli.Decoder.StepRead

/-!
# The literals' step

A step in a command's literals does one of these: moves on to the distance, switches block, pauses with the window
full, or runs the literal loop for as many literals as the command, the block and the window allow.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A cheap check that a buffer is well formed, for the literal loop's entry. -/
@[inline] def wfCheck (word count : UInt64) : Bool :=
  count ≤ 64 && (count == 64 || word >>> count == 0)

theorem wfCheck_wf {word count : UInt64} (h : wfCheck word count = true) : (BitBuffer.mk word count).Wf := by
  simp only [wfCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
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
  simp only [wfCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨UInt64.le_iff_toNat_le.mpr (by rw [h64]; exact hc), ?_⟩
  by_cases he : count.toNat = 64
  · exact Or.inl (UInt64.toNat_inj.mp (by rw [he]; rfl))
  · refine Or.inr (UInt64.toNat_inj.mp ?_)
    rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hw

/-- Runs the literal loop. -/
def literalsRun (H : Hdr) (w k : Nat) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) : Stepped :=
  let run := min st.left.toNat (min st.lCount.toNat (2 ^ k - st.pend.toNat))
  if ht : st.lCur.toNat < H.nL.toNat then
    have hm : st.lCur.toUSize.toNat < H.modes.size := by
      rw [word_toUSize (by have := H.lit.map32; have := H.lMapSize; omega), H.modesSize]
      exact ht
    let mode := H.modes.uget st.lCur.toUSize hm
    let mapBase := USize.ofNat (64 * st.lCur.toNat)
    let modeOff := USize.ofNat (512 * mode.toNat)
    if h : mapBase.toNat + 64 ≤ H.lMap.size ∧ modeOff.toNat + 512 ≤ 2048 ∧ modeOff.toNat % 512 = 0 ∧
        (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧ k ≤ 24 ∧ pos.toNat ≤ stop.toNat ∧ st.ring.size = 2 ^ k ∧
        st.wpos.toNat < 2 ^ k ∧ wfCheck st.word st.count = true then
      let ring := st.ring
      let st0 := clearRing st
      let r := literalRun H.lit a stop hs mapBase modeOff (USize.ofNat (2 ^ k - 1)) k h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
        run st0.word st0.count pos st0.wpos ring st0.p1 st0.p2 h.2.2.2.2.2.1 (wfCheck_wf h.2.2.2.2.2.2.2.2) h.2.2.2.2.2.2.1
        h.2.2.2.2.2.2.2.1
      let used := UInt64.ofNat (run - r.left)
      ⟨{ st0 with
          word := r.word, count := r.count, ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
          left := st0.left - used, lCount := st0.lCount - used, remaining := st0.remaining - used
          pend := USize.ofNat (st0.pend.toNat + (run - r.left))
          written := USize.ofNat (min w (st0.written.toNat + (run - r.left))) },
        r.pos, if r.left = 0 then .next else .needsInput⟩
    else ⟨st, pos, .bad⟩
  else ⟨st, pos, .bad⟩

/-- A step in a command's literals. -/
def stepLiterals (H : Hdr) (w k : Nat) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (pos : USize) :
    Stepped :=
  if st.left.toNat = 0 then ⟨{ st with tag := .distance }, pos, .next⟩
  else if st.lCount.toNat = 0 then
    if hn : 2 ≤ H.nL.toNat then
      let r := blockSwitch H.arena H.lit.arena32 H.baseTL H.baseCL (H.swL hn).1 (H.swL hn).2 H.nL.toNat st.lCur st.lPrev
        st.word st.count
      match r.status with
      | .ok =>
        let seen := st.seen
        let st0 := clearSeen st
        ⟨{ st0 with
            word := r.word, count := r.count, lCur := r.cur, lPrev := st0.lCur, lCount := r.blockCount
            seen := markSeen seen 0 r.cur.toNat }, pos, .next⟩
      | .short => ⟨st, pos, .needsInput⟩
      | .bad => ⟨st, pos, .bad⟩
    else ⟨st, pos, .bad⟩
  else if 2 ^ k - st.pend.toNat = 0 then ⟨st, pos, .needsOutput⟩
  else literalsRun H w k a stop hs st pos

/-- What follows the literal loop, whatever it returned. -/
private theorem literals_after {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState}
    {out : List Nat} {st : Cmd} {pos : USize}
    (hC : Core w k m st out (s.remaining - (ilen - n)) s.distances ic lit s.distance) (htag : st.tag = .literals)
    (hprod : s.produced = s.output.length) (hcode : st.code.toNat = c) (hilen : st.ilen.toNat = ilen)
    (hclen : st.clen.toNat = clen) (hleft : st.left.toNat = n) (hnle : n ≤ ilen) (hirem : ilen ≤ s.remaining)
    (hlen : out.length + n = s.output.length + ilen) (hp : pos.toNat ≤ stop.toNat) (r : LitRun) {run : Nat}
    (hrunL : run ≤ n) (hrunC : run ≤ st.lCount.toNat) (hrunR : run + st.pend.toNat ≤ 2 ^ k)
    (hspec : ∃ (lit' : BlockState) (out' : List Nat),
      r.left ≤ run ∧ lit'.types = lit.types ∧ lit'.seen = lit.seen ∧ lit'.count = lit.count - (run - r.left) ∧
      out'.length = out.length + (run - r.left) ∧ RingOk r.ring k r.wpos.toNat out' ∧
      contextBytes out' = (r.p1.toNat, r.p2.toNat) ∧ (BitBuffer.mk r.word r.count).Wf ∧
      pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧ (∀ b ∈ out', b < 256) ∧
      (∀ F, rest w m K (.literals s ic c ilen clen n lit out) (availBits st.word st.count a pos stop F) =
        rest w m K (.literals s ic c ilen clen (n - (run - r.left)) lit' out') (availBits r.word r.count a r.pos stop F)) ∧
      (r.left ≠ 0 → r.pos = stop ∧
        rest w m K (.literals s ic c ilen clen (n - (run - r.left)) lit' out') (BitBuffer.mk r.word r.count).held = none)) :
    StepOk w k m K a stop (.literals s ic c ilen clen n lit out) st pos
      ⟨{ st with
          word := r.word, count := r.count, ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
          left := st.left - UInt64.ofNat (run - r.left), lCount := st.lCount - UInt64.ofNat (run - r.left)
          remaining := st.remaining - UInt64.ofNat (run - r.left)
          pend := USize.ofNat (st.pend.toNat + (run - r.left))
          written := USize.ofNat (min w (st.written.toNat + (run - r.left))) },
        r.pos, if r.left = 0 then .next else .needsInput⟩ := by
  obtain ⟨lit', out', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := hspec
  have hk := hC.k24
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hwin := hC.win
  have hrem := hC.rem
  have hple := hC.pendLe
  have hpo := hC.pendOut
  have hwri := hC.written
  have hlcount : lit.count = st.lCount.toNat := hC.lRel.count
  generalize hu : run - r.left = used at h4 h5 h12 h13 ⊢
  have hused : used ≤ run := by omega
  have huU : (UInt64.ofNat used).toNat = used := u64_ofNat (by omega)
  have hnew : Rel w k m
      { st with
        word := r.word, count := r.count, ring := r.ring, wpos := r.wpos, p1 := r.p1, p2 := r.p2
        left := st.left - UInt64.ofNat used, lCount := st.lCount - UInt64.ofNat used
        remaining := st.remaining - UInt64.ofNat used
        pend := USize.ofNat (st.pend.toNat + used)
        written := USize.ofNat (min w (st.written.toNat + used)) }
      (.literals s ic c ilen clen (n - used) lit' out') := by
    refine ⟨?_, htag, hprod, hcode, hilen, hclen, ?_, by omega, hirem, by omega⟩
    · refine { hC with
        wf := h8, ring := h6, bytes := h11, ctx := h7, pendLe := ?_, pendOut := ?_, written := ?_, rem := ?_
        lRel := hC.lRel.run h2 h3 ?_ }
      · show (USize.ofNat (st.pend.toNat + used)).toNat ≤ _
        rw [usize_ofNat' (by omega)]
        omega
      · show (USize.ofNat (st.pend.toNat + used)).toNat ≤ _
        rw [usize_ofNat' (by omega), h5]
        omega
      · show (USize.ofNat (min w (st.written.toNat + used))).toNat = _
        rw [usize_ofNat' (by omega), h5, hwri]
        omega
      · show (st.remaining - UInt64.ofNat used).toNat = _
        rw [u64_sub (by rw [huU]; omega), huU]
        omega
      · show lit'.count = (st.lCount - UInt64.ofNat used).toNat
        rw [u64_sub (by rw [huU]; omega), huU, h4]
        omega
    · show (st.left - UInt64.ofNat used).toNat = _
      rw [u64_sub (by rw [huU]; omega), huU]
      omega
  split
  · exact StepOk.ofNext rfl hnew h9 h10 fun F => h12 F
  · rename_i hne
    obtain ⟨hstop, hnone⟩ := h13 hne
    exact StepOk.ofInput rfl hstop hp hnew (fun F => h12 F) hnone

/-- The literal loop's step does its job. -/
theorem literalsRun_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat}
    {lit : BlockState} {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.literals s ic c ilen clen n lit out)) (hp : pos.toNat ≤ stop.toNat) :
    StepOk w k m K a stop (.literals s ic c ilen clen n lit out) st pos (literalsRun H w k a stop hs st pos) := by
  obtain ⟨hC, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ := hrel
  have hk := hC.k24
  have hRmax : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h24 : (2 : Nat) ^ 24 = 16777216 := by decide
  have hRpos : 1 ≤ 2 ^ k := Nat.two_pow_pos _
  have hwin := hC.win
  have hrem := hC.rem
  have hple := hC.pendLe
  have hpo := hC.pendOut
  have hwri := hC.written
  have ht : st.lCur.toNat < H.nL.toNat := by
    rw [hH.nL, ← hC.lRel.cur]
    exact hC.lRel.wf.2.1
  have hmap32 := H.lit.map32
  have hmapSize := H.lMapSize
  have hLt : st.lCur.toNat < 2 ^ 32 := by omega
  have hum : st.lCur.toUSize.toNat = st.lCur.toNat := word_toUSize hLt
  have hm : st.lCur.toUSize.toNat < H.modes.size := by
    rw [hum, H.modesSize]
    exact ht
  have hmodeLt := H.modesLt _ hm
  have hmodeSpec := hH.modes _ hm
  rw [hum] at hmodeSpec
  have hmapB : (USize.ofNat (64 * st.lCur.toNat)).toNat = 64 * st.lCur.toNat := usize_ofNat' (by omega)
  have hmodeO : (USize.ofNat (512 * (H.modes.uget st.lCur.toUSize hm).toNat)).toNat =
      512 * (H.modes.uget st.lCur.toUSize hm).toNat := usize_ofNat' (by omega)
  unfold literalsRun
  dsimp only
  rw [dite_eq_left ht]
  have hguard : (USize.ofNat (64 * st.lCur.toNat)).toNat + 64 ≤ H.lMap.size ∧
      (USize.ofNat (512 * (H.modes.uget st.lCur.toUSize hm).toNat)).toNat + 512 ≤ 2048 ∧
      (USize.ofNat (512 * (H.modes.uget st.lCur.toUSize hm).toNat)).toNat % 512 = 0 ∧
      (USize.ofNat (2 ^ k - 1)).toNat = 2 ^ k - 1 ∧ k ≤ 24 ∧ pos.toNat ≤ stop.toNat ∧ st.ring.size = 2 ^ k ∧
      st.wpos.toNat < 2 ^ k ∧ wfCheck st.word st.count = true :=
    ⟨by omega, by omega, by omega, usize_ofNat' (by omega), hk, hp, hC.ring.size, hC.ring.pos_lt, wfCheck_of_wf hC.wf⟩
  rw [dite_eq_left hguard]
  dsimp only [clearRing]
  have hmodeNat : m.contextModes[st.lCur.toNat]? =
      some ((USize.ofNat (512 * (H.modes.uget st.lCur.toUSize hm).toNat)).toNat / 512) := by
    rw [hmodeO, hmodeSpec]
    congr 1
    omega
  generalize hrunD : min st.left.toNat (min st.lCount.toNat (2 ^ k - st.pend.toNat)) = run
  have hlcount : lit.count = st.lCount.toNat := hC.lRel.count
  have hspec := literalRun_spec H.lit hs hguard.1 hguard.2.1 hguard.2.2.1 hguard.2.2.2.1 hk hH.lit
    (w := w) (K := K) (t := st.lCur.toNat) hmapB hmodeNat s ic c ilen clen run st.word st.count pos st.wpos st.ring st.p1 st.p2
    hp (wfCheck_wf hguard.2.2.2.2.2.2.2.2) hguard.2.2.2.2.2.2.1 hguard.2.2.2.2.2.2.2.1 n lit out (by omega) (by omega)
    hC.lRel.cur hC.ctx hC.ring hC.bytes
  dsimp only at hspec
  exact literals_after hC htag hprod hcode hilen hclen hleft hnle hirem hlen hp _ (by omega) (by omega) (by omega) hspec

/-- The literals' step does its job. -/
theorem stepLiterals_ok {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat}
    {lit : BlockState} {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k m st (.literals s ic c ilen clen n lit out)) (hp : pos.toNat ≤ stop.toNat)
    (hfull : 56 < st.count.toNat ∨ pos = stop) :
    StepOk w k m K a stop (.literals s ic c ilen clen n lit out) st pos (stepLiterals H w k a stop hs st pos) := by
  have hrel0 := hrel
  obtain ⟨hC, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ := hrel
  have hrem := hC.rem
  unfold stepLiterals
  split
  · rename_i hz
    have hn0 : n = 0 := by omega
    subst hn0
    refine StepOk.ofNext (p' := .distance (withLiterals s ic lit out ilen) c clen) rfl ⟨?_, rfl, ?_, hcode, hclen⟩
      (Nat.le_refl _) hp fun F => rest_literals_distance _
    · refine { hC with rem := ?_ }
      show st.remaining.toNat = s.remaining - ilen
      omega
    · show s.produced + ilen = out.length
      omega
  · rename_i hnz
    have hn0 : n ≠ 0 := by omega
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    split
    · rename_i hcnt
      have hcz : lit.count = 0 := by
        rw [hC.lRel.count]
        exact hcnt
      split
      · rename_i hn
        have hn2 : 2 ≤ m.literal.n := by
          rw [← hH.nL]
          exact hn
        have hsp := blockSwitch_rel (h32 := H.lit.arena32) (hT := (H.swL hn).1) (hCt := (H.swL hn).2) hH.nL hH.catL
          hH.ok.literal hC.lRel hcnt hC.wf hn2
        dsimp only at hsp ⊢
        generalize blockSwitch _ _ _ _ _ _ _ _ _ _ _ = r at hsp ⊢
        obtain ⟨hok, hshort, hbad⟩ := hsp
        cases hst : r.status with
        | ok =>
          obtain ⟨hw, hlt, hc1, hc2, hnext⟩ := hok hst
          have h256 := hH.ok.literal.2.1
          have hsize := hC.seenSize
          refine StepOk.ofNext (p' := .literals s ic c ilen clen (n' + 1)
            ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat, r.cur.toNat :: lit.seen⟩ out) rfl
            ⟨?_, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ (Nat.le_refl _) hp fun F => ?_
          · exact { hC with
              wf := hw
              lRel := hC.lRel.switched (by omega) hlt rfl
              iRel := hC.iRel.marked (by omega)
              dRel := hC.dRel.marked (by omega)
              seenSize := by rw [show _ = (markSeen st.seen 0 r.cur.toNat).size from rfl, size_markSeen]; exact hsize }
          · rw [stateBits_eq, stateBits_eq, rest_literal, rest_literal, hnext,
              nextElement_count (st := ⟨⟨st.lCur.toNat, r.cur.toNat⟩, r.blockCount.toNat, r.cur.toNat :: lit.seen⟩) _
                (by show r.blockCount.toNat ≠ 0; omega)]
        | short =>
          obtain ⟨_, _, hc54, hnone⟩ := hshort hst
          refine StepOk.ofShort hrel0 (hfull.resolve_left (by omega)) ?_
          rw [rest_literal, hnone]
          rfl
        | bad =>
          refine StepOk.ofBad rfl fun F => ?_
          rw [stateBits_eq, rest_literal, hbad hst]
          rfl
      · rename_i hn
        have hn' : m.literal.n < 2 := by
          rw [← hH.nL]
          omega
        refine StepOk.ofBad rfl fun F => ?_
        rw [rest_literal, nextElement_single _ hcz hn']
        rfl
    · rename_i hcnt
      split
      · rename_i hroom
        have hle := hC.pendLe
        exact ⟨fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h,
          fun _ => ⟨_, hrel0, Nat.le_refl _, hp, fun _ => rfl, by show st.pend.toNat = _; omega⟩,
          fun h => StepStatus.noConfusion h, fun h => StepStatus.noConfusion h⟩
      · rename_i hroom
        exact literalsRun_ok hH hrel0 hp

end Brotli.Decoder
