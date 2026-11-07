module

public import Brotli.Decoder.LoopK

@[expose] public section

/-!
# The fast command loop does the spec's work

The fast loop (`FastLoop.lean`) reads its bits differently from the step machine: it refills at other points, and a
round of it is several of the step machine's steps. Its proof reuses the step machine's: a fast operation equals a step
function on the bits the fast loop holds, and a step taken with the chunk ending where the step starts (`stop := pos`)
needs no refill, so its contract, for every future, is the contract at the real chunk's end with that future after the
rest of the chunk (`stateBits_widen`). The moves compose by `RunOk.trans`.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The bits from `pos` with the chunk ending at `stop` are those with it ending at `pos`, followed by the rest of the
chunk. -/
theorem stateBits_widen (st : Cmd) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    stateBits st a pos stop F = stateBits st a pos pos (chunkBits a pos.toNat stop.toNat ++ F) := by
  rw [stateBits_eq, stateBits_eq, chunkBits_self, List.nil_append]

/-- A move from one place to another, taken without the chunk: the next state's place, the same future, the bytes it
adds, and the spec's reading in order. -/
structure MoveOk {α : Type} (w k : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (a : ByteArray)
    (stop : USize) (p : Phase) (st : Cmd) (pos : USize) (p' : Phase) (r : Cmd) : Prop where
  rel : Rel w k m r p'
  posLe : pos.toNat ≤ r.pos.toNat
  posStop : r.pos.toNat ≤ stop.toNat
  restEq : ∀ F, rest w m K p (stateBits st a pos stop F) = rest w m K p' (stateBits r a r.pos stop F)
  out : OutStep p p' st r
  reach : ∀ F, Reach (cStep w m) p (stateBits st a pos stop F) p' (stateBits r a r.pos stop F)

section
variable {α : Type} {w k : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α} {a : ByteArray}
  {stop : USize} {p p' : Phase} {st r : Cmd} {pos : USize}

/-- A step that moved on with the chunk ending where it started, which reads nothing of the chunk, is a move for the real
chunk. -/
theorem StepOk.widen (h : StepOk w k m K a pos p st pos r) (hs : r.status = .next) (hr : r.pos = pos)
    (hp : pos.toNat ≤ stop.toNat) : ∃ p', MoveOk w k m K a stop p st pos p' r := by
  obtain ⟨p', hrel, _, _, h4, _, h6, h7⟩ := h.next hs
  refine ⟨p', hrel, by rw [hr]; exact Nat.le_refl _, by rw [hr]; exact hp, fun F => ?_, h6, fun F => ?_⟩
  · rw [stateBits_widen st a pos stop F, stateBits_widen r a r.pos stop F, hr]
    rw [hr] at h4
    exact h4 _
  · rw [stateBits_widen st a pos stop F, stateBits_widen r a r.pos stop F, hr]
    have := h7 (chunkBits a pos.toNat stop.toNat ++ F)
    rw [hr] at this
    exact this

/-- A move, then a run, is a run. -/
theorem MoveOk.then {r' : Cmd} (h : MoveOk w k m K a stop p st pos p' r) (h2 : RunOk w k m K a stop p' r r.pos r') :
    RunOk w k m K a stop p st pos r' :=
  RunOk.trans h.posLe h.restEq h.out h.reach h2

/-- Two moves are a move. -/
theorem MoveOk.trans {p'' : Phase} {r' : Cmd} (h1 : MoveOk w k m K a stop p st pos p' r)
    (h2 : MoveOk w k m K a stop p' r r.pos p'' r') : MoveOk w k m K a stop p st pos p'' r' :=
  ⟨h2.rel, Nat.le_trans h1.posLe h2.posLe, h2.posStop, fun F => (h1.restEq F).trans (h2.restEq F), h1.out.trans h2.out,
    fun F => (h1.reach F).trans (h2.reach F)⟩

/-- A state that moved on stands for its place: a run of nothing. -/
theorem MoveOk.toRun (h : MoveOk w k m K a stop p st pos p' r) (hs : r.status = .next) :
    RunOk w k m K a stop p st pos r :=
  ⟨fun _ => ⟨p', h.rel, h.posLe, h.posStop, h.restEq, h.out, h.reach⟩, fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e), fun e => StepStatus.noConfusion (hs.symm.trans e),
    fun e => StepStatus.noConfusion (hs.symm.trans e)⟩

/-- A move ends at any state for the same place with the same bits, position and bytes waiting. -/
theorem MoveOk.congr {r' : Cmd} (h : MoveOk w k m K a stop p st pos p' r) (hrel : Rel w k m r' p')
    (hw : r'.word = r.word) (hc : r'.count = r.count) (hp : r'.pos = r.pos) (hpe : r'.pend = r.pend) :
    MoveOk w k m K a stop p st pos p' r' := by
  have e : ∀ F, stateBits r' a r'.pos stop F = stateBits r a r.pos stop F := fun F => by
    unfold stateBits
    rw [hw, hc, hp]
  obtain ⟨l, h1, h2⟩ := h.out
  refine ⟨hrel, by rw [hp]; exact h.posLe, by rw [hp]; exact h.posStop, fun F => by rw [e F]; exact h.restEq F,
    ⟨l, h1, by rw [hpe]; exact h2⟩, fun F => by rw [e F]; exact h.reach F⟩

/-- A refill under the margin keeps the state's place and future: the bits are the same, held differently. -/
theorem fill_move {w' c' : UInt64} {pos' : USize} {thr : Nat} (hrel : Rel w k m st p)
    (hf : FillOk a stop st.word st.count pos thr w' c' pos') :
    MoveOk w k m K a stop p st pos p { st with word := w', count := c', pos := pos' } := by
  refine ⟨(hrel.withBits hf.wf).mark pos' st.status, hf.posLe, hf.posStop, fun F => ?_, ⟨[], rfl, rfl⟩, fun F => ?_⟩
  · show rest w m K p ((BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F)) =
      rest w m K p ((BitBuffer.mk w' c').held ++ (chunkBits a pos'.toNat stop.toNat ++ F))
    rw [← List.append_assoc, ← List.append_assoc, hf.bits]
  · refine Reach.ofEq ?_
    show (BitBuffer.mk w' c').held ++ (chunkBits a pos'.toNat stop.toNat ++ F) =
      (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, hf.bits]

end

/-! ### The window's slack -/

/-- A ring that agrees with one holding `out` everywhere except in the 16 bytes from the next position to write holds
`out` too: those bytes are the slack, older than any distance reaches. -/
theorem RingOk.slack {ring ring' : ByteArray} {k p : Nat} {out : List Nat} (h : RingOk ring k p out)
    (hs : ring'.size = ring.size)
    (he : ∀ i, i < 2 ^ k → ¬ (p ≤ i ∧ i < p + 16) → ¬ (i + 2 ^ k < p + 16) → ring'.data[i]? = ring.data[i]?) :
    RingOk ring' k p out := by
  refine ⟨hs.trans h.size, h.pos_lt, fun d hd hdl => ?_⟩
  have hp := h.pos_lt
  have hidx := ringIdx_lt (R := 2 ^ k) hp (by omega : d < 2 ^ k)
  rw [he _ hidx ?_ ?_]
  · exact h.holds d hd hdl
  · unfold ringIdx
    split <;> omega
  · unfold ringIdx
    split <;> omega

/-! ### With the chunk ending where it starts, a refill takes nothing -/

theorem refill_self {word count : UInt64} {a : ByteArray} {pos : USize} (hs : pos.toNat ≤ a.size)
    (hp : pos.toNat ≤ pos.toNat) : refill word count a pos pos hs hp = ⟨word, count, pos⟩ := by
  unfold refill
  split
  · rfl
  · have h0 : ¬ USize.ofNat 8 ≤ pos - pos := by
      rw [USize.sub_self]
      intro h
      have := USize.le_iff_toNat_le.mp h
      rw [fastLit (by decide), show (0 : USize).toNat = 0 from rfl] at this
      omega
    rw [dite_eq_right h0, BitBuffer.fillSlow, dite_eq_right (fun h => absurd h.2 (USize.lt_irrefl _))]

/-! ### The loop's positions against the record's -/

theorem usize_add_one_comm (x b : USize) : x + b + USize.ofNat 1 = x + USize.ofNat 1 + b := by
  rw [USize.add_assoc, USize.add_comm b, ← USize.add_assoc]

/-- A position plus one, reduced modulo the window. -/
theorem usize_succ_mod {x : USize} {k : Nat} (hk : k ≤ 24) :
    (x + USize.ofNat 1).toNat % 2 ^ k = (x.toNat + 1) % 2 ^ k := by
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hd : 2 ^ k ∣ 2 ^ System.Platform.numBits := Nat.pow_dvd_pow 2 (by omega)
  rw [USize.toNat_add, fastLit (by decide), Nat.mod_mod_of_dvd _ hd]

/-- The next window position from the loop's unmasked one is `ringNext` of the masked one. -/
theorem mask_succ {x mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ringNext (x &&& mask) mask = (x + USize.ofNat 1) &&& mask := by
  apply USize.toNat_inj.mp
  unfold ringNext
  have h1 : (x &&& mask).toNat = x.toNat % 2 ^ k := by
    rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, usize_succ_mod hk, h1, USize.toNat_and, hm,
    Nat.and_two_pow_sub_one_eq_mod, usize_succ_mod hk, Nat.add_mod x.toNat 1, Nat.add_mod (x.toNat % 2 ^ k) 1,
    Nat.mod_mod]

/-- The bytes written, capped, after one more: the cap of the uncapped count plus one. -/
theorem usmin_succ {c x : USize} (hx : x.toNat + 1 < 2 ^ 32) (hc : c.toNat < 2 ^ 32) :
    usmin c (usmin c x + USize.ofNat 1) = usmin c (x + USize.ofNat 1) := by
  apply USize.toNat_inj.mp
  have hm : (usmin c x).toNat + 1 < 2 ^ 32 := by rw [usmin_toNat]; omega
  rw [usmin_toNat, usmin_toNat, fastIdx_add hm, fastIdx_add hx, usmin_toNat]
  omega

/-- What remains from one more byte on. -/
theorem rem_succ {r : UInt64} {x : USize} (hx : x.toNat + 1 < 2 ^ 32) (hr : x.toNat + 1 ≤ r.toNat) :
    r - (x + USize.ofNat 1).toUInt64 = r - x.toUInt64 - 1 := by
  apply UInt64.toNat_inj.mp
  have e1 : (x + USize.ofNat 1).toUInt64.toNat = x.toNat + 1 := by rw [USize.toNat_toUInt64, fastIdx_add hx]
  have e2 : x.toUInt64.toNat = x.toNat := USize.toNat_toUInt64 x
  have e3 : (r - x.toUInt64).toNat = r.toNat - x.toNat := by rw [u64_sub_le (by rw [e2]; omega), e2]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [u64_sub_le (by rw [e1]; exact hr), e1, u64_sub_le (by rw [e3, h1]; omega), e3, h1]
  omega

/-! ### One literal -/

/-- The literal loop for one literal, with the chunk ending where it starts and the bits at hand enough: the literal
read at the context's tree, written to the window. -/
theorem literalRun_one {nTrees : Nat} {arena litBase lMap : ByteArray} (C : LitChecked arena litBase lMap nTrees)
    {a : ByteArray} {pos : USize} (hs : pos.toNat ≤ a.size) (mapBase modeOff mask : USize) (k : Nat)
    (hmb : mapBase.toNat + 64 ≤ lMap.size) (hm : modeOff.toNat + 512 ≤ 2048) (hd : modeOff.toNat % 512 = 0)
    (hmask : mask.toNat = 2 ^ k - 1) (hk : k ≤ 24) {n : USize} (hn : n.toNat = 1) (word count : UInt64) (wpos : USize)
    (ring : ByteArray) (p1 p2 : UInt8) (hp : pos.toNat ≤ pos.toNat) (hw : (BitBuffer.mk word count).Wf)
    (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) {base : USize} (hfit : TableFits arena base.toNat)
    (hbase : u32At litBase (lMap.data[mapBase.toNat + (cidFast modeOff p1 p2 hm).toNat]?.getD 0).toNat = base.toNat)
    (hl : lookup arena base word hfit C.arena32 &&& 15 ≤ count) :
    literalRun C a pos hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp =
      ⟨word >>> (lookup arena base word hfit C.arena32 &&& 15), count - (lookup arena base word hfit C.arena32 &&& 15),
        pos, ringNext wpos mask,
        ringWrite ring wpos (lookup arena base word hfit C.arena32 >>> 4).toUInt8 (by omega),
        (lookup arena base word hfit C.arena32 >>> 4).toUInt8, p1, 0⟩ := by
  have hn0 : n ≠ 0 := fun e => by rw [e, show (0 : USize).toNat = 0 from rfl] at hn; exact absurd hn (by decide)
  have hn1 : n - USize.ofNat 1 = 0 := usize_zero (by rw [usize_pred hn0]; omega)
  have hcid := cid_lt (p1 := p1) (p2 := p2) hm hd
  have hidx : (mapIndex mapBase (cidFast modeOff p1 p2 hm)).toNat = mapBase.toNat + (cidFast modeOff p1 p2 hm).toNat :=
    mapIndex_toNat (by have := C.map32; omega)
  have hi : (mapIndex mapBase (cidFast modeOff p1 p2 hm)).toNat < lMap.size := by
    rw [hidx]
    omega
  have e : u32At litBase (lMap.uget (mapIndex mapBase (cidFast modeOff p1 p2 hm)) hi).toNat = base.toNat := by
    rw [uget_lit, hidx]
    exact hbase
  rw [literalRun, dite_eq_right hn0]
  simp only [refill_self, lookup_treeBase hfit e]
  rw [dite_eq_left hl, literalRun, dite_eq_left hn1]
  rfl

/-- A literal at the state's buffer, as a move: the step machine's literal with the chunk ending where it starts, for
the real chunk. The table base is the context's tree's, and the bits at hand cover the code word. -/
theorem lit_move {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState}
    {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st (.literals s ic c ilen clen n lit out)) (hn0 : 1 ≤ st.left.toNat)
    (hc0 : 1 ≤ st.lCount.toNat) (hroom : st.pend.toNat + 1 + 16 ≤ 2 ^ k.toNat) (hp : pos.toNat ≤ stop.toNat)
    (hs : stop.toNat ≤ a.size) (hlt : st.lCur.toNat < H.nL.toNat) {modeOff : USize}
    (hmode : modeOff.toNat = 512 * (H.modes.data[st.lCur.toNat]?.getD 0).toNat) (hmo : modeOff.toNat + 512 ≤ 2048)
    (hmd : modeOff.toNat % 512 = 0) {base : USize} (hfit : TableFits H.arena base.toNat)
    (hbase : u32At H.litBase (byteN H.lMap (64 * st.lCur.toNat + (cidFast modeOff st.p1 st.p2 hmo).toNat)) = base.toNat)
    (hl : lookup H.arena base st.word hfit H.lit.arena32 &&& 15 ≤ st.count)
    (hsz : st.ring.size = 2 ^ k.toNat) (hwp : st.wpos.toNat < 2 ^ k.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out) st pos p'
      { st with
        word := st.word >>> (lookup H.arena base st.word hfit H.lit.arena32 &&& 15)
        count := st.count - (lookup H.arena base st.word hfit H.lit.arena32 &&& 15)
        ring := ringWrite st.ring st.wpos (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8 (by omega)
        wpos := ringNext st.wpos (ringMask k)
        p1 := (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8
        p2 := st.p1
        left := st.left - 1
        lCount := st.lCount - 1
        remaining := st.remaining - 1
        pend := st.pend + USize.ofNat 1
        written := usmin (ringSize k - USize.ofNat 16) (st.written + USize.ofNat 1)
        pos := pos
        status := .next } := by
  obtain ⟨hC, htag, hprod, hcode, hilen, hclen, hleft, hnle, hirem, hlen⟩ := hrel
  have hk := hC.k24
  have hps : pos.toNat ≤ a.size := Nat.le_trans hp hs
  have hmodeSpec : m.contextModes[st.lCur.toNat]? = some (modeOff.toNat / 512) := by
    have hu : (USize.ofNat st.lCur.toNat).toNat = st.lCur.toNat := fastLit (by have := cur_small hlt; omega)
    have hmz : (USize.ofNat st.lCur.toNat).toNat < H.modes.size := by rw [hu, H.modesSize]; exact hlt
    have := hH.modes _ hmz
    rw [uget_toNat, hu] at this
    rw [this, hmode]
    congr 1
    omega
  have h1 : (USize.ofNat 1).toNat = 1 := fastLit (by decide)
  have hspec := literalRun_spec H.lit (stop := pos) hps (mapBase := (st.lCur <<< 6).toUSize) (modeOff := modeOff)
    (mask := ringMask k) (k := k.toNat) (mapBase_le hlt) hmo hmd (ringMask_toNat hk) hk (w := w) (K := K) hH.lit
    (t := st.lCur.toNat) (mapBase_toNat hlt) hmodeSpec s ic c ilen clen (USize.ofNat 1).toNat (USize.ofNat 1) st.word
    st.count pos st.wpos st.ring st.p1 st.p2 (Nat.le_refl _) hC.wf hC.ring.size hC.ring.pos_lt n lit out rfl
    (by rw [h1]; omega) (by rw [h1, hC.lRel.count]; omega) hC.lRel.cur hC.ctx hC.ring hC.bytes
  dsimp only at hspec
  have hstep := literals_after (stop := pos) (K := K) hC htag hprod hcode hilen hclen hleft hnle hirem hlen
    (Nat.le_refl _) _ (run := USize.ofNat 1) (by rw [h1]; decide) (by rw [h1]; omega) (by rw [h1]; exact hc0)
    (by rw [h1]; omega) hspec
  have hone := literalRun_one H.lit hps (st.lCur <<< 6).toUSize modeOff (ringMask k) k.toNat (mapBase_le hlt) hmo hmd
    (ringMask_toNat hk) hk h1 st.word st.count st.wpos st.ring st.p1 st.p2 (Nat.le_refl _) hC.wf hC.ring.size
    hC.ring.pos_lt hfit (by rw [mapBase_toNat hlt]; exact hbase) hl
  rw [hone] at hstep
  have hsub1 : (USize.ofNat 1).toUInt64 = 1 := by
    apply UInt64.toNat_inj.mp
    rw [USize.toNat_toUInt64, h1]
    rfl
  have hrec : finishLiterals (clearRing st)
      ⟨st.word >>> (lookup H.arena base st.word hfit H.lit.arena32 &&& 15),
        st.count - (lookup H.arena base st.word hfit H.lit.arena32 &&& 15), pos, ringNext st.wpos (ringMask k),
        ringWrite st.ring st.wpos (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8 (by omega),
        (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8, st.p1, 0⟩ (USize.ofNat 1) (ringSize k) =
      { st with
        word := st.word >>> (lookup H.arena base st.word hfit H.lit.arena32 &&& 15)
        count := st.count - (lookup H.arena base st.word hfit H.lit.arena32 &&& 15)
        ring := ringWrite st.ring st.wpos (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8 (by omega)
        wpos := ringNext st.wpos (ringMask k)
        p1 := (lookup H.arena base st.word hfit H.lit.arena32 >>> 4).toUInt8
        p2 := st.p1
        left := st.left - 1
        lCount := st.lCount - 1
        remaining := st.remaining - 1
        pend := st.pend + USize.ofNat 1
        written := usmin (ringSize k - USize.ofNat 16) (st.written + USize.ofNat 1)
        pos := pos
        status := .next } := by
    unfold finishLiterals clearRing
    simp only [USize.sub_zero, hsub1, ↓reduceIte]
  rw [hrec] at hstep
  exact hstep.widen rfl rfl hp

/-- The fast loop's literal read is the lookup at the context's tree: through the resolved literal map, or at the block
type's shared base. -/
theorem FCtx.litT_lookup {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (p1 p2 : UInt8) (w : UInt64) :
    ∃ (base : USize) (hfit : TableFits H.arena base.toNat),
      u32At H.litBase (byteN H.lMap (64 * lCur.toNat + (cidFast modeOff p1 p2 C.hm).toNat)) = base.toNat ∧
      litT C p1 p2 w = lookup H.arena base w hfit H.lit.arena32 := by
  have hT := C.arena
  subst hT
  have hc := cid_lt (p1 := p1) (p2 := p2) C.hm C.hm512
  unfold litT
  split
  · rename_i h
    refine ⟨_, (C.rowIn p1 p2).fits (by have := C.lim; omega), ?_, lookupT_eq _ _ _⟩
    unfold litRowBase
    rw [word_toUSize (by rw [load32_toNat]; exact Nat.lt_of_lt_of_le (leAt_lt _ _ 4) (by decide)), load32_toNat,
      (C.litIdx _ hc).1, (C.litIn hc).1]
  · rename_i h
    refine ⟨_, (C.tbIn h).fits (by have := C.lim; omega), ?_, lookupT_eq _ _ _⟩
    have hv : tb.toNat = u32At H.lTriv lCur.toNat := by rw [C.tbEq, trivBase_toNat]
    have hne : u32At H.lTriv lCur.toNat ≠ 4294967295 := fun e => h (UInt64.toNat_inj.mp (by rw [hv, e]; rfl))
    rw [word_toUSize (by rw [hv]; exact u32At_lt _ _), hv]
    exact H.trivOk _ C.hl hne _ hc

/-! ### The loop's numbers -/

/-- What keeps the loop's unmasked positions from wrapping: the bytes the current command still writes (`ahead`) fit
before `bEnd`, which is within the meta-block; the bytes waiting and written, as the loop computes them from `opos`, stay
within the window up to `bEnd`. -/
structure FNum (opos pB wB : USize) (rEnd bEnd : UInt64) (k ahead : Nat) : Prop where
  ahead : opos.toNat + ahead ≤ bEnd.toNat
  bEndLe : bEnd.toNat ≤ rEnd.toNat
  small : bEnd.toNat < 2 ^ 30
  pend : (opos + pB).toNat + (bEnd.toNat - opos.toNat) + 16 ≤ 2 ^ k
  wr : (opos + wB).toNat + (bEnd.toNat - opos.toNat) < 2 ^ 30

theorem u64_add_sub_one {a b : UInt64} (h : 1 ≤ b.toNat) (h' : a.toNat + b.toNat < 2 ^ 64) :
    a + b - 1 = a + (b - 1) := by
  apply UInt64.toNat_inj.mp
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have e : (b - 1).toNat = b.toNat - 1 := by rw [u64_sub_le (by rw [h1]; exact h), h1]
  rw [u64_sub_le (by rw [u64_add_small h', h1]; omega), u64_add_small h', h1,
    u64_add_small (by rw [e]; omega), e]
  omega

/-- The record a fast state stands for, after the step machine's literal, is the fast state's one byte on: the window
position, the bytes waiting and written and what remains, from `opos + 1`. -/
theorem fexit_succ {word count word' count' : UInt64} {ring ring' : ByteArray} {opos mask pB cap cap16 wB : USize}
    {rEnd bEnd : UInt64} {iCount lc dCount : UInt64} {flags : Flags} {x : CmdExt} {d01 d23 code ilen clen : UInt64}
    {p1 p2 q1 q2 : UInt8} {tag : Tag} {lf : UInt64} {pos pos' : USize} {k : USize} (hk : k.toNat ≤ 24)
    (h16 : 16 ≤ 2 ^ k.toNat) (hmk : mask = ringMask k) (hcap : cap16 = ringSize k - USize.ofNat 16)
    {ahead : Nat} (N : FNum opos pB wB rEnd bEnd k.toNat ahead) (ha : 1 ≤ ahead) :
    { fexit word count ring opos mask pB cap cap16 wB rEnd iCount lc dCount flags x d01 d23 code ilen clen p1 p2 tag lf
        pos with
      word := word', count := count', ring := ring', wpos := ringNext (opos &&& mask) (ringMask k), p1 := q1, p2 := q2,
      left := lf - 1, lCount := lc - 1, remaining := rEnd - opos.toUInt64 - 1, pend := opos + pB + USize.ofNat 1,
      written := usmin (ringSize k - USize.ofNat 16) (usmin cap16 (opos + wB) + USize.ofNat 1), pos := pos',
      status := .next } =
      fexit word' count' ring' (opos + USize.ofNat 1) mask pB cap cap16 wB rEnd iCount (lc - 1) dCount flags x d01 d23 code
        ilen clen q1 q2 tag (lf - 1) pos' := by
  subst hmk
  subst hcap
  have hR : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hc : (ringSize k - USize.ofNat 16).toNat < 2 ^ 32 := by
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by rw [fastLit (by decide), ringSize_toNat hk]; exact h16)),
      fastLit (by decide), ringSize_toNat hk]
    omega
  have hpos := N.ahead
  have hsm := N.small
  have hwr := N.wr
  have hbe := N.bEndLe
  have e1 : ringNext (opos &&& ringMask k) (ringMask k) = (opos + USize.ofNat 1) &&& ringMask k :=
    mask_succ hk (ringMask_toNat hk)
  have e2 : opos + pB + USize.ofNat 1 = opos + USize.ofNat 1 + pB := usize_add_one_comm _ _
  have e3 : usmin (ringSize k - USize.ofNat 16) (usmin (ringSize k - USize.ofNat 16) (opos + wB) + USize.ofNat 1) =
      usmin (ringSize k - USize.ofNat 16) (opos + USize.ofNat 1 + wB) := by
    rw [← usize_add_one_comm]
    exact usmin_succ (by omega) hc
  have e4 : rEnd - opos.toUInt64 - 1 = rEnd - (opos + USize.ofNat 1).toUInt64 :=
    (rem_succ (by omega) (by omega)).symm
  unfold fexit
  rw [e1, e2, e3, e4]

/-! ### The masked byte loop is the step machine's copy -/

theorem uset_congr {t : ByteArray} {i j : USize} {v v' : UInt8} {hi : i.toNat < t.size} {hj : j.toNat < t.size}
    (h : i = j) (hv : v = v') : t.uset i v hi = t.uset j v' hj := by
  subst h
  subst hv
  rfl

theorem ringBack_mod {k : Nat} {pos d mask size : USize} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : size.toNat = 2 ^ k) (hp : pos.toNat < 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    (ringBack pos d mask size).toNat = (pos.toNat + 2 ^ k - d.toNat) % 2 ^ k := by
  rw [ringBack_toNat hk hm hs hp hd1 hd2]
  unfold ringIdx
  split
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem copyMasked_run {d mask size : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hsz : size.toNat = 2 ^ k) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) :
    ∀ (N : Nat) (n : USize) (ring : ByteArray) (wpos dp sp : USize) (p1 p2 : UInt8) (hs : ring.size = 2 ^ k)
      (hwp : wpos.toNat < 2 ^ k), n.toNat = N → dp.toNat % 2 ^ k = wpos.toNat →
      sp.toNat % 2 ^ k = (wpos.toNat + 2 ^ k - d.toNat) % 2 ^ k →
      copyMasked ring dp sp n mask hk hm hs = (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hwp).ring := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hRpos : 0 < 2 ^ k := Nat.two_pow_pos _
  intro N
  induction N with
  | zero =>
    intro n ring wpos dp sp p1 p2 hs hwp hN _ _
    rw [copyMasked, copyRun, dite_eq_left (usize_zero hN), dite_eq_left (usize_zero hN)]
  | succ N ih =>
    intro n ring wpos dp sp p1 p2 hs hwp hN hdp hsp
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyMasked, copyRun, dite_eq_right hn, dite_eq_right hn]
    have hdm : (dp &&& mask).toNat = wpos.toNat := by
      rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, hdp]
    have hsm : (sp &&& mask).toNat = (ringBack wpos d mask size).toNat := by
      rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, hsp, ringBack_mod hk hm hsz hwp hd1 hd2]
    have hw1 : wix (dp &&& mask) = wpos := USize.toNat_inj.mp (by rw [wix_toNat (by omega), hdm])
    have hs1 : sp &&& mask = ringBack wpos d mask size := USize.toNat_inj.mp hsm
    have hnext : (ringNext wpos mask).toNat = (wpos.toNat + 1) % 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, usize_succ_mod hk]
    have hstep : wput ring dp mask hk hm hs (wget ring sp mask hm hs) =
        ringWrite ring wpos (ring.uget (ringBack wpos d mask size) (by
          rw [ringBack_toNat hk hm hsz hwp hd1 hd2, hs]; exact ringIdx_lt hwp (by omega))) (by omega) := by
      unfold wput wget ringWrite
      exact uset_congr hw1 (uget_congr hs1 _ _)
    have key : ∀ (r1 r2 : ByteArray) (h1 : r1.size = 2 ^ k) (h2 : r2.size = 2 ^ k), r1 = r2 → ∀ dp' sp' n',
        copyMasked r1 dp' sp' n' mask hk hm h1 = copyMasked r2 dp' sp' n' mask hk hm h2 := by
      intro r1 r2 h1 h2 e
      subst e
      intros
      rfl
    rw [key _ _ _ ((size_ringWrite ring wpos _ _).trans hs) hstep]
    refine ih _ _ _ (dp + USize.ofNat 1) (sp + USize.ofNat 1) _ _ _ _ (by rw [usize_pred hn]; omega) ?_ ?_
    · rw [usize_succ_mod hk, hnext, Nat.add_mod dp.toNat 1, hdp, Nat.add_mod wpos.toNat 1, Nat.mod_eq_of_lt hwp]
    · rw [usize_succ_mod hk, hnext, Nat.add_mod sp.toNat 1, hsp, ← Nat.add_mod]
      by_cases hw1 : wpos.toNat + 1 < 2 ^ k
      · rw [Nat.mod_eq_of_lt hw1]
        congr 1
        omega
      · have : wpos.toNat + 1 = 2 ^ k := by omega
        rw [this, Nat.mod_self, show wpos.toNat + 2 ^ k - d.toNat + 1 = (0 + 2 ^ k - d.toNat) + 2 ^ k by omega,
          Nat.add_mod_right]

/-! ### Distances -/

theorem shl_add_distrib (a b s : UInt64) : (a + b) <<< s = (a <<< s) + (b <<< s) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.add_mul, Nat.add_mod]

/-- A distance symbol from 16 on: its distance is the one with no extra bits, plus the extra bits shifted by NPOSTFIX
(direct codes take none). -/
theorem distFast_split {np nd d0 d1 d2 d3 dc extra : UInt64} (h16 : ¬ dc < 16) :
    distFast np nd d0 d1 d2 d3 dc extra =
      distFast np nd 0 0 0 0 dc 0 + (if dc < 16 + nd then 0 else extra <<< np) := by
  unfold distFast
  rw [ite_eq_right h16, ite_eq_right h16]
  split
  · rw [UInt64.add_zero]
  · dsimp only
    rw [UInt64.add_zero, shl_add_distrib]
    rw [UInt64.add_assoc, UInt64.add_assoc, UInt64.add_assoc, UInt64.add_assoc, UInt64.add_assoc, UInt64.add_assoc]
    congr 1
    rw [UInt64.add_comm (extra <<< np), UInt64.add_assoc, UInt64.add_assoc]

/-- A distance symbol from 16 on, within the alphabet, gives a distance below `2 ^ 30` with its extra bits. -/
theorem distFast_lt {np nd d0 d1 d2 d3 dc extra : UInt64} (hnp : np.toNat ≤ 3) (hnd : nd.toNat ≤ 120)
    (hd : dc.toNat < 2 ^ 16) (h16 : ¬ dc < 16) (hbits : (extraBitsFast np nd dc).toNat ≤ 24)
    (hx : extra.toNat < 2 ^ (extraBitsFast np nd dc).toNat) :
    (distFast np nd d0 d1 d2 d3 dc extra).toNat < 2 ^ 30 := by
  have h16' : (16 : UInt64).toNat = 16 := rfl
  have hadd : (16 + nd).toNat = 16 + nd.toNat := u64_add_small (by rw [h16']; omega)
  have h16N : 16 ≤ dc.toNat :=
    Nat.le_of_not_lt fun h => h16 (UInt64.lt_iff_toNat_lt.mpr (by rw [h16']; exact h))
  unfold distFast
  rw [ite_eq_right h16]
  split
  · rename_i hlt
    have := UInt64.lt_iff_toNat_lt.mp hlt
    rw [hadd] at this
    rw [u64_sub_le (by show 15 ≤ _; omega)]
    show dc.toNat - 15 < _
    omega
  · rename_i hge
    have hge' : 16 + nd.toNat ≤ dc.toNat :=
      Nat.le_of_not_lt fun h => hge (UInt64.lt_iff_toNat_lt.mpr (by rw [hadd]; exact h))
    dsimp only
    rw [far_toNat hnp hnd hd hge' hbits hx]
    have hb := (extraBitsFast_toNat hnp hnd hd).symm
    rw [← hb] at hbits hx
    generalize distanceExtraBits np.toNat nd.toNat dc.toNat = nb at hbits hx ⊢
    generalize dc.toNat - nd.toNat - 16 = X
    have hbit : (X >>> np.toNat) &&& 1 ≤ 1 := Nat.and_le_right
    have hpow : 2 ^ nb ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hbits
    have hpow8 : 2 ^ np.toNat ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hnp
    have hA : (2 + ((X >>> np.toNat) &&& 1)) <<< nb ≤ 3 * 2 ^ 24 := by
      rw [Nat.shiftLeft_eq]
      exact Nat.mul_le_mul (by omega) hpow
    have hB : ((2 + ((X >>> np.toNat) &&& 1)) <<< nb) - 4 + extra.toNat < 2 ^ 26 := by
      have : (2 : Nat) ^ 26 = 67108864 := by decide
      have : (2 : Nat) ^ 24 = 16777216 := by decide
      omega
    have hC : (((2 + ((X >>> np.toNat) &&& 1)) <<< nb) - 4 + extra.toNat) <<< np.toNat < 2 ^ 29 := by
      rw [Nat.shiftLeft_eq]
      have := Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hB (Nat.two_pow_pos np.toNat))
        (Nat.mul_le_mul_left (2 ^ 26) hpow8)
      have : (2 : Nat) ^ 26 * 2 ^ 3 = 2 ^ 29 := by decide
      omega
    have hm : X &&& postfixMask np.toNat ≤ 7 := by
      refine Nat.le_trans Nat.and_le_right ?_
      unfold postfixMask
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      have : (2 : Nat) ^ 3 = 8 := by decide
      omega
    have : (2 : Nat) ^ 29 = 536870912 := by decide
    have : (2 : Nat) ^ 30 = 1073741824 := by decide
    omega

/-- A shared distance table's entry, for a symbol from 16 on within the alphabet: its extra bits in the low bits, and its
distance with no extra bits from bit 32. -/
theorem dEntry_split {np nd dc : UInt64} (hnp : np.toNat ≤ 3) (hnd : nd.toNat ≤ 120) (hd : dc.toNat < 2 ^ 16)
    (h16 : ¬ dc < 16) (hbits : (extraBitsFast np nd dc).toNat ≤ 24) :
    dEntry np nd dc &&& 31 = extraBitsFast np nd dc ∧ dEntry np nd dc >>> 32 = distFast np nd 0 0 0 0 dc 0 := by
  have hD := distFast_lt (d0 := 0) (d1 := 0) (d2 := 0) (d3 := 0) (extra := 0) hnp hnd hd h16 hbits
    (by show 0 < _; exact Nat.two_pow_pos _)
  unfold dEntry
  rw [ite_eq_right h16]
  generalize distFast np nd 0 0 0 0 dc 0 = D at hD ⊢
  generalize extraBitsFast np nd dc = e at hbits ⊢
  have hsh : (D <<< 32).toNat = 2 ^ 32 * D.toNat := by
    rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by have : (2 : Nat) ^ 30 * 2 ^ 32 < 2 ^ 64 := by decide
                               have : 2 ^ 32 * D.toNat < 2 ^ 32 * 2 ^ 30 := Nat.mul_lt_mul_of_pos_left hD (by decide)
                               omega)
  have hor : (e ||| (D <<< 32)).toNat = 2 ^ 32 * D.toNat + e.toNat := by
    rw [UInt64.toNat_or, hsh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (by
      have : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
      omega)]
  constructor
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hor, show (31 : UInt64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show 2 ^ 32 * D.toNat + e.toNat = e.toNat + 2 ^ 5 * (2 ^ 27 * D.toNat) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hor, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow,
      Nat.mul_add_div (by decide), Nat.div_eq_of_lt (by have : (2 : Nat) ^ 24 < 2 ^ 32 := by decide
                                                        omega), Nat.add_zero]

/-- A base plus an offset less 3, as the branch-free short codes compute it, against the step machine's: where it is
not 0 and doesn't wrap past `2 ^ 32`, it is the spec's. -/
theorem short_off {b : UInt64} {o : Nat} (hb : b.toNat < 2 ^ 32) (ho : o ≤ 6)
    (hne : b + UInt64.ofNat o - 3 ≠ 0) (hlt : (b + UInt64.ofNat o - 3).toNat < 2 ^ 32) :
    (b + UInt64.ofNat o - 3).toNat = b.toNat + o - 3 ∧ 3 ≤ b.toNat + o ∧ b.toNat + o ≠ 3 := by
  have ho' : (UInt64.ofNat o).toNat = o := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hadd : (b + UInt64.ofNat o).toNat = b.toNat + o := by rw [u64_add_small (by rw [ho']; omega), ho']
  have h3 : (3 : UInt64).toNat = 3 := rfl
  have hne' : (b + UInt64.ofNat o - 3).toNat ≠ 0 := fun e => hne (UInt64.toNat_inj.mp (by rw [e]; rfl))
  by_cases hge : 3 ≤ b.toNat + o
  · rw [u64_sub_le (by rw [hadd, h3]; exact hge), hadd, h3] at hne' hlt ⊢
    exact ⟨rfl, hge, by omega⟩
  · exfalso
    rw [UInt64.toNat_sub, hadd, h3] at hlt
    have : (2 ^ 64 - 3 + (b.toNat + o)) % 2 ^ 64 = 2 ^ 64 - 3 + (b.toNat + o) := Nat.mod_eq_of_lt (by omega)
    rw [this] at hlt
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega

theorem short_sub_case {b : UInt64} {x : Nat} (hx : 1 ≤ x ∧ x ≤ 3) (hb : b.toNat < 2 ^ 32)
    (hne : b + UInt64.ofNat (3 - x) - 3 ≠ 0) (hlt : (b + UInt64.ofNat (3 - x) - 3).toNat < 2 ^ 32) :
    b + UInt64.ofNat (3 - x) - 3 = shortSub b (UInt64.ofNat x) := by
  obtain ⟨e, h3, hn3⟩ := short_off hb (by omega) hne hlt
  have hx' : (UInt64.ofNat x).toNat = x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  unfold shortSub
  have hgt : ¬ b ≤ UInt64.ofNat x := fun h => by
    have := UInt64.le_iff_toNat_le.mp h
    rw [hx'] at this
    omega
  rw [ite_eq_right hgt]
  apply UInt64.toNat_inj.mp
  rw [e, u64_sub_le (by rw [hx']; omega), hx']
  omega

theorem short_add_case {b : UInt64} {x : Nat} (hx : x ≤ 3) (hb : b.toNat < 2 ^ 32) :
    b + UInt64.ofNat (3 + x) - 3 = b + UInt64.ofNat x := by
  apply UInt64.toNat_inj.mp
  have hx' : (UInt64.ofNat x).toNat = x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hx3 : (UInt64.ofNat (3 + x)).toNat = 3 + x := by rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have h3 : (3 : UInt64).toNat = 3 := rfl
  rw [u64_sub_le (by rw [u64_add_small (by rw [hx3]; omega), hx3, h3]; omega), u64_add_small (by rw [hx3]; omega), hx3,
    h3, u64_add_small (by rw [hx']; omega), hx']
  omega

/-- The branch-free short codes are the step machine's wherever the fast loop goes on with them: a distance not 0 and
below `2 ^ 32`. -/
theorem shortFast_eq {d0 d1 d2 d3 dc : UInt64} (h0 : d0.toNat < 2 ^ 32) (h1 : d1.toNat < 2 ^ 32) (hd : dc.toNat < 16)
    (hne : shortFast d0 d1 d2 d3 dc ≠ 0) (hlt : (shortFast d0 d1 d2 d3 dc).toNat < 2 ^ 32) :
    shortFast d0 d1 d2 d3 dc = shortDist d0 d1 d2 d3 dc := by
  have hid : dc = UInt64.ofNat dc.toNat := by simp
  generalize hn : dc.toNat = n at hd
  rw [hn] at hid
  subst hid
  have hA : ∀ b : UInt64, b + 3 - 3 = b := fun b => by
    apply UInt64.toNat_inj.mp
    have h3 : (3 : UInt64).toNat = 3 := rfl
    have hb := b.toNat_lt
    rw [UInt64.toNat_sub, UInt64.toNat_add, h3]
    have : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
    omega
  -- each code's offset plus 3 (which last distance the code takes, `decide` settles in place)
  have tab : ∀ j, j < 16 →
      ((6940401482202231603 : UInt64) >>> (UInt64.ofNat j <<< 2) &&& 15) =
        UInt64.ofNat ([3, 3, 3, 3, 2, 4, 1, 5, 0, 6, 2, 4, 1, 5, 0, 6].getD j 0) := by decide
  match n, hd with
  | 0, _ =>
    have e2 := tab 0 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, e2, List.getD, ↓reduceIte]
    exact hA _
  | 1, _ =>
    have e2 := tab 1 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, e2, List.getD, ↓reduceIte]
    exact hA _
  | 2, _ =>
    have e2 := tab 2 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, e2, List.getD, ↓reduceIte]
    exact hA _
  | 3, _ =>
    have e2 := tab 3 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, e2, List.getD, ↓reduceIte]
    exact hA _
  | 4, _ =>
    have e2 := tab 4 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 1) (by decide) h0 hne hlt
  | 5, _ =>
    have e2 := tab 5 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 1) (by decide) h0
  | 6, _ =>
    have e2 := tab 6 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 2) (by decide) h0 hne hlt
  | 7, _ =>
    have e2 := tab 7 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 2) (by decide) h0
  | 8, _ =>
    have e2 := tab 8 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 3) (by decide) h0 hne hlt
  | 9, _ =>
    have e2 := tab 9 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 3) (by decide) h0
  | 10, _ =>
    have e2 := tab 10 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 1) (by decide) h1 hne hlt
  | 11, _ =>
    have e2 := tab 11 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 1) (by decide) h1
  | 12, _ =>
    have e2 := tab 12 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 2) (by decide) h1 hne hlt
  | 13, _ =>
    have e2 := tab 13 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 2) (by decide) h1
  | 14, _ =>
    have e2 := tab 14 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte] at hne hlt ⊢
    exact short_sub_case (x := 3) (by decide) h1 hne hlt
  | 15, _ =>
    have e2 := tab 15 (by decide)
    simp (config := { decide := true }) only [shortFast, shortDist, shortAdjust, e2, List.getD, ↓reduceIte]
    exact short_add_case (x := 3) (by decide) h1
  | _ + 16, h => exact absurd h (by omega)

/-! ### Forward copies -/

/-- A forward copy of `a + b` bytes is one of `a` bytes and then one of `b` from where it ended. -/
theorem fwdCopy_add (w : ByteArray) (d s a : Nat) :
    ∀ b, fwdCopy w d s (a + b) = fwdCopy (fwdCopy w d s a) (d + a) (s + a) b
  | 0 => rfl
  | b + 1 => by
    show (⟨(fwdCopy w d s (a + b)).data.setIfInBounds (d + (a + b))
        ((fwdCopy w d s (a + b)).data[s + (a + b)]?.getD 0)⟩ : ByteArray) =
      ⟨(fwdCopy (fwdCopy w d s a) (d + a) (s + a) b).data.setIfInBounds (d + a + b)
        ((fwdCopy (fwdCopy w d s a) (d + a) (s + a) b).data[s + a + b]?.getD 0)⟩
    rw [fwdCopy_add w d s a b, Nat.add_assoc, Nat.add_assoc]

/-- A forward copy writes only its destination. -/
theorem fwdCopy_out (w : ByteArray) (d s : Nat) : ∀ k i, ¬ (d ≤ i ∧ i < d + k) →
    (fwdCopy w d s k).data[i]? = w.data[i]?
  | 0, _, _ => rfl
  | k + 1, i, h => by
    show ((fwdCopy w d s k).data.setIfInBounds (d + k) _)[i]? = _
    rw [Array.getElem?_setIfInBounds, ite_eq_right (by omega), fwdCopy_out w d s k i (by omega)]

/-- With the source never in the part of the destination already written (it starts at or after the destination, or ends
before it), a forward copy reads only bytes it hasn't written. -/
theorem fwdCopy_get' (w : ByteArray) (d s : Nat) :
    ∀ k, (d ≤ s ∨ s + k ≤ d) → d + k ≤ w.size → s + k ≤ w.size → ∀ i,
      (fwdCopy w d s k).data[i]? = if d ≤ i ∧ i < d + k then w.data[s + (i - d)]? else w.data[i]?
  | 0, _, _, _, i => by
    rw [ite_eq_right (by omega)]
    rfl
  | k + 1, hs, hd, hs', i => by
    have ih := fwdCopy_get' w d s k (by omega) (by omega) (by omega)
    have hsz := fwdCopy_size w d s k
    have hsz' : (fwdCopy w d s k).data.size = w.data.size := hsz
    have hwsz : w.size = w.data.size := rfl
    have hread : (fwdCopy w d s k).data[s + k]? = w.data[s + k]? := by
      rw [ih (s + k), ite_eq_right (by omega)]
    show ((fwdCopy w d s k).data.setIfInBounds (d + k) ((fwdCopy w d s k).data[s + k]?.getD 0))[i]? = _
    rw [hread, Array.getElem?_setIfInBounds]
    by_cases hi : d + k = i
    · subst hi
      have hlt : d + k < (fwdCopy w d s k).data.size := by omega
      rw [ite_eq_left rfl, ite_eq_left hlt, ite_eq_left (by omega)]
      have : s + (d + k - d) = s + k := by omega
      rw [this]
      rw [Array.getElem?_eq_getElem (by omega : s + k < w.data.size)]
      rfl
    · rw [ite_eq_right hi, ih i]
      by_cases hr : d ≤ i ∧ i < d + k
      · rw [ite_eq_left hr, ite_eq_left (by omega)]
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

/-- With the source never in the part of the destination already written, the forward copy is the snapshot copy: what
`winMove` and `winCopy16` compute. -/
theorem fwdCopy_snap (w : ByteArray) (d s n : Nat) (hd : d + n ≤ w.size) (hs : s + n ≤ w.size)
    (hsep : d ≤ s ∨ s + n ≤ d) : fwdCopy w d s n = w.copySlice s w d n := by
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro i
  rw [fwdCopy_get' w d s n hsep hd hs i]
  exact (copySlice_self_get w d s n i hd hs).symm

/-- A byte of the window, as the masked byte loop reads and writes it: the masks are no change where the copy doesn't
wrap. -/
theorem copyMasked_fwd {mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (ring : ByteArray) (d s n : USize) (hs : ring.size = 2 ^ k), n.toNat = N →
      d.toNat + N ≤ 2 ^ k → s.toNat + N ≤ 2 ^ k →
      copyMasked ring d s n mask hk hm hs = fwdCopy ring d.toNat s.toNat N := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  intro N
  induction N with
  | zero =>
    intro ring d s n hs hN _ _
    rw [copyMasked, dite_eq_left (usize_zero hN)]
    rfl
  | succ N ih =>
    intro ring d s n hs hN hd hs'
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    rw [copyMasked, dite_eq_right hn]
    have hd1 : (d + USize.ofNat 1).toNat = d.toNat + 1 := fastIdx_add (by omega)
    have hs1 : (s + USize.ofNat 1).toNat = s.toNat + 1 := fastIdx_add (by omega)
    have hdm : (d &&& mask).toNat = d.toNat := by
      rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    have hsm : (s &&& mask).toNat = s.toNat := by
      rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
    rw [ih _ _ _ _ _ (by rw [usize_pred hn]; omega) (by rw [hd1]; omega) (by rw [hs1]; omega), hd1, hs1,
      show N + 1 = 1 + N by omega, fwdCopy_add ring d.toNat s.toNat 1 N]
    have hix : (wix (d &&& mask)).toNat = d.toNat := by rw [wix_toNat (by omega), hdm]
    have hget : (wget ring s mask hm hs).toNat = (ring.data[s.toNat]?.getD 0).toNat := by
      unfold wget
      rw [uget_toNat, hsm]
    congr 1
    unfold wput
    rw [uset_eq, hix, show wget ring s mask hm hs = ring.data[s.toNat]?.getD 0 from UInt8.toNat_inj.mp hget]
    rfl

/-- One byte copied, its store masked (`wix`), is one step of the forward copy. -/
theorem cp1_fwd {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat < n) (hs : s.toNat < n) (h24 : n ≤ 2 ^ 24) :
    (cp1 w d s hd hs h24).1 = fwdCopy w.1 d.toNat s.toNat 1 := by
  unfold cp1 wst wld
  dsimp only
  rw [uset_eq, wix_toNat (by omega), show w.1.uget s _ = w.1.data[s.toNat]?.getD 0 from
    UInt8.toNat_inj.mp (by rw [uget_toNat])]
  rfl

theorem cp1_size {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat < n) (hs : s.toNat < n) (h24 : n ≤ 2 ^ 24) :
    (cp1 w d s hd hs h24).1.size = n := (cp1 w d s hd hs h24).2

/-- Eight bytes copied one at a time are eight steps of the forward copy. -/
theorem cp8_fwd {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat + 8 ≤ n) (hs : s.toNat + 8 ≤ n) (h24 : n ≤ 2 ^ 24) :
    (cp8 w d s hd hs h24).1 = fwdCopy w.1 d.toNat s.toNat 8 := by
  have h32 : n < 2 ^ 32 := by omega
  have e : ∀ j, j < 8 → (d + USize.ofNat j).toNat = d.toNat + j ∧ (s + USize.ofNat j).toNat = s.toNat + j :=
    fun j _ => ⟨fastIdx_add (by omega), fastIdx_add (by omega)⟩
  unfold cp8
  dsimp only
  simp only [cp1_fwd]
  rw [(e 1 (by decide)).1, (e 1 (by decide)).2, (e 2 (by decide)).1, (e 2 (by decide)).2, (e 3 (by decide)).1,
    (e 3 (by decide)).2, (e 4 (by decide)).1, (e 4 (by decide)).2, (e 5 (by decide)).1, (e 5 (by decide)).2,
    (e 6 (by decide)).1, (e 6 (by decide)).2, (e 7 (by decide)).1, (e 7 (by decide)).2]
  simp only [← fwdCopy_add, Nat.add_assoc]

/-- Byte `j` of the little-endian number of `n` bytes from `i`. -/
theorem leAt_byte (t : ByteArray) : ∀ (n i j : Nat), j < n → (leAt t i n / 256 ^ j) % 256 = byteN t (i + j)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, i, 0, _ => by
    rw [leAt, Nat.pow_zero, Nat.div_one]
    show _ = byteN t i
    have := byteN_lt t i
    omega
  | n + 1, i, j + 1, h => by
    rw [leAt, Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul]
    have hb := byteN_lt t i
    have : (byteN t i + 256 * leAt t (i + 1) n) / 256 = leAt t (i + 1) n := by omega
    rw [this, leAt_byte t n (i + 1) j (by omega)]
    congr 1
    omega

/-- A store at a window position: the byte there now, the rest unchanged. -/
theorem wst_get {n : Nat} (w : Win n) (i : USize) (v : UInt8) (h : i.toNat < n) (j : Nat) :
    (wst w i v h).1.data[j]? = if i.toNat = j then some v else w.1.data[j]? := by
  unfold wst
  dsimp only
  rw [uset_eq]
  show (w.1.data.setIfInBounds i.toNat v)[j]? = _
  rw [Array.getElem?_setIfInBounds]
  split
  · rename_i he
    have h1 : w.1.size = w.1.data.size := rfl
    have h2 := w.2
    rw [ite_eq_left (by omega)]
  · rfl

/-- Byte `k` of an 8-byte load is the array's byte `k` from the load's position. -/
theorem load64_byte (t : ByteArray) (i : USize) (h : i.toNat + 8 ≤ t.size) (h32 : t.size < 2 ^ 32) (k : Nat) (hk : k < 8)
    (sh : UInt64) (hs : sh.toNat = 8 * k) :
    (load64 t i h h32 >>> sh).toUInt8 = t.data[i.toNat + k]?.getD 0 := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs, Nat.mod_eq_of_lt (show 8 * k < 64 by omega),
    Nat.shiftRight_eq_div_pow,
    load64_toNat, show 2 ^ (8 * k) = 256 ^ k by rw [Nat.pow_mul], leAt_byte t 8 i.toNat k hk]
  rfl

/-- The 8 stores of an 8-byte load are the snapshot copy of those 8 bytes. -/
theorem put8At_snap {n : Nat} (w : Win n) (d s : USize) (hd : d.toNat + 8 ≤ n) (hs : s.toNat + 8 ≤ w.1.size)
    (h32 : n < 2 ^ 32) :
    (put8At w d (load64 w.1 s hs (by rw [w.2]; exact h32)) hd h32).1 = w.1.copySlice s.toNat w.1 d.toNat 8 := by
  have hsz := w.2
  have e : ∀ j, j < 8 → (d + USize.ofNat j).toNat = d.toNat + j := fun j _ => fastIdx_add (by omega)
  have b : ∀ k, k < 8 → ∀ sh : UInt64, sh.toNat = 8 * k →
      (load64 w.1 s hs (by rw [w.2]; exact h32) >>> sh).toUInt8 = w.1.data[s.toNat + k]?.getD 0 :=
    fun k hk sh hsh => load64_byte w.1 s hs _ k hk sh hsh
  have b0 : (load64 w.1 s hs (by rw [w.2]; exact h32)).toUInt8 = w.1.data[s.toNat + 0]?.getD 0 := by
    rw [← b 0 (by decide) 0 rfl]
    congr 1
  apply ByteArray.ext
  apply Array.ext_getElem?
  intro j
  rw [copySlice_self_get w.1 d.toNat s.toNat 8 j (by omega) hs]
  unfold put8At
  simp only [wst_get, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide), e 5 (by decide),
    e 6 (by decide), e 7 (by decide), b0, b 1 (by decide) 8 rfl, b 2 (by decide) 16 rfl, b 3 (by decide) 24 rfl,
    b 4 (by decide) 32 rfl, b 5 (by decide) 40 rfl, b 6 (by decide) 48 rfl, b 7 (by decide) 56 rfl]
  have hget : ∀ q, q < w.1.data.size → w.1.data[q]? = some (w.1.data[q]?.getD 0) := fun q hq => by
    rw [Array.getElem?_eq_getElem hq]
    rfl
  have h1 : w.1.size = w.1.data.size := rfl
  by_cases hin : d.toNat ≤ j ∧ j < d.toNat + 8
  · rw [ite_eq_left hin]
    obtain ⟨k, hk, rfl⟩ : ∃ k, k < 8 ∧ j = d.toNat + k := ⟨j - d.toNat, by omega, by omega⟩
    rw [show d.toNat + k - d.toNat = k by omega]
    conv => rhs; rw [hget (s.toNat + k) (by omega)]
    match k, hk with
    | 0, _ => simp
    | 1, _ => simp
    | 2, _ => simp
    | 3, _ => simp
    | 4, _ => simp
    | 5, _ => simp
    | 6, _ => simp
    | 7, _ => simp
  · rw [ite_eq_right hin]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A block of 8 is 8 bytes of the forward copy: byte by byte, or by one load where the distance keeps the source out of
the block. -/
theorem blk8_fwd {n : Nat} (w : Win n) (d s dist : USize) (hd : d.toNat + 8 ≤ n) (hs : s.toNat + 8 ≤ n)
    (h24 : n ≤ 2 ^ 24) (hsep : ¬ dist < USize.ofNat 8 → d.toNat ≤ s.toNat ∨ s.toNat + 8 ≤ d.toNat) :
    (blk8 w d s dist hd hs h24).1 = fwdCopy w.1 d.toNat s.toNat 8 := by
  unfold blk8
  split
  · exact cp8_fwd w d s hd hs h24
  · rename_i h
    unfold put8
    have hw := w.2
    have hix : (wix d).toNat = d.toNat := wix_toNat (by omega)
    have key : ∀ (e : USize) (he : e.toNat = d.toNat) (h1 : e.toNat + 8 ≤ n),
        (put8At w e (load64 w.1 s (by rw [w.2]; exact hs) (by rw [w.2]; omega)) h1 (by omega)).1 =
          fwdCopy w.1 d.toNat s.toNat 8 := by
      intro e he h1
      rw [put8At_snap w e s h1 (by rw [w.2]; exact hs) (by omega), he,
        fwdCopy_snap w.1 d.toNat s.toNat 8 (by omega) (by omega) (hsep h)]
    exact key (wix d) hix _

/-- A copy's source in the window: `d` bytes before the destination, or, where that wraps, after it. -/
theorem src_cases {wpos d mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hw : wpos.toNat < 2 ^ k) (hd : d.toNat + 16 ≤ 2 ^ k) :
    ((wpos - d) &&& mask).toNat + d.toNat = wpos.toNat ∨
      ((wpos - d) &&& mask).toNat = wpos.toNat + 2 ^ k - d.toNat := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hP : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) hb
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hle : d.toNat ≤ wpos.toNat
  · left
    rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hle), Nat.mod_eq_of_lt (by omega)]
    omega
  · right
    have hsub : (wpos - d).toNat = 2 ^ System.Platform.numBits - (d.toNat - wpos.toNat) := by
      rw [USize.toNat_sub, Nat.mod_eq_of_lt (by omega)]
      omega
    have h1 : 2 ^ System.Platform.numBits = 2 ^ k * 2 ^ (System.Platform.numBits - k) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
    have h2 : 1 ≤ 2 ^ (System.Platform.numBits - k) := Nat.one_le_two_pow
    rw [hsub, h1]
    have e2 : 2 ^ k * 2 ^ (System.Platform.numBits - k) - (d.toNat - wpos.toNat) =
        (2 ^ k - (d.toNat - wpos.toNat)) + 2 ^ k * (2 ^ (System.Platform.numBits - k) - 1) := by
      rw [Nat.mul_sub, Nat.mul_one]
      have : 2 ^ k ≤ 2 ^ k * 2 ^ (System.Platform.numBits - k) := Nat.le_mul_of_pos_right _ h2
      omega
    rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- A 16-byte snapshot copy between separate ranges is the forward copy of those 16 bytes. -/
theorem winCopy16_fwd (w : ByteArray) (d s : USize)
    (h : d.toNat + 16 ≤ w.size ∧ s.toNat + 16 ≤ w.size ∧ (s.toNat + 16 ≤ d.toNat ∨ d.toNat + 16 ≤ s.toNat)) :
    winCopy16 w d s h = fwdCopy w d.toNat s.toNat 16 :=
  (fwdCopy_snap w _ _ 16 h.1 h.2.1 (by omega)).symm

/-- The fast copy is the forward copy of at least its length and at most 15 bytes more, within the window, or the masked
byte loop. -/
theorem copyF_cases (ring : ByteArray) (wpos d n mask size : USize) {k : Nat} (hk : k ≤ 24)
    (hm : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k) (hs : ring.size = 2 ^ k) (hw : wpos.toNat < 2 ^ k)
    (hd : d.toNat + 16 ≤ 2 ^ k) (hn1 : 1 ≤ n.toNat) :
    (∃ N, n.toNat ≤ N ∧ N ≤ n.toNat + 15 ∧ wpos.toNat + N ≤ 2 ^ k ∧ ((wpos - d) &&& mask).toNat + N ≤ 2 ^ k ∧
      copyF ring wpos d n mask size hk hm hsz hs hw hd = fwdCopy ring wpos.toNat ((wpos - d) &&& mask).toNat N) ∨
    copyF ring wpos d n mask size hk hm hsz hs hw hd = copyMasked ring wpos ((wpos - d) &&& mask) n mask hk hm hs := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hsrc := src_cases hk hm hw hd
  have hSl : ((wpos - d) &&& mask).toNat < 2 ^ k := mask_lt hm
  have h8 : (USize.ofNat 8).toNat = 8 := fastLit (by decide)
  have h16 : (USize.ofNat 16).toNat = 16 := fastLit (by decide)
  have h24 : (USize.ofNat 24).toNat = 24 := fastLit (by decide)
  have h32 : (USize.ofNat 32).toNat = 32 := fastLit (by decide)
  unfold copyF
  dsimp only
  split
  · rename_i h
    have hd16 : 16 ≤ d.toNat := by have := USize.le_iff_toNat_le.mp h.1; rwa [h16] at this
    have hn32 : n.toNat ≤ 32 := by have := USize.le_iff_toNat_le.mp h.2.1; rwa [h32] at this
    have hs32 : ((wpos - d) &&& mask).toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h.2.2.1; rwa [fastIdx_add (by omega), hsz] at this
    have hw32 : wpos.toNat + 32 ≤ 2 ^ k := by
      have := USize.le_iff_toNat_le.mp h.2.2.2; rwa [fastIdx_add (by omega), hsz] at this
    have sep : ∀ j, j ≤ 16 → wpos.toNat + j ≤ ((wpos - d) &&& mask).toNat + j ∨
        ((wpos - d) &&& mask).toNat + j + 16 ≤ wpos.toNat + j := fun j _ => by rcases hsrc with e | e <;> omega
    left
    split
    · rename_i hn16
      have hn16' : n.toNat ≤ 16 := by have := USize.le_iff_toNat_le.mp hn16; rwa [h16] at this
      refine ⟨16, by omega, by omega, by omega, by omega, ?_⟩
      exact (fwdCopy_snap ring _ _ 16 (by omega) (by omega) (by have := sep 0 (by decide); omega)).symm
    · rename_i hn16
      have hn16' : ¬ n.toNat ≤ 16 := fun e => hn16 (USize.le_iff_toNat_le.mpr (by rw [h16]; exact e))
      refine ⟨32, by omega, by omega, by omega, by omega, ?_⟩
      rw [winCopy16_fwd, winCopy16_fwd, fastIdx_add (by omega), fastIdx_add (by omega),
        show (32 : Nat) = 16 + 16 from rfl, fwdCopy_add]
  · split
    · rename_i _ h2
      have hnd := USize.le_iff_toNat_le.mp h2.2.1
      have e1 := USize.le_iff_toNat_le.mp h2.2.2.1
      have e2 := USize.le_iff_toNat_le.mp h2.2.2.2
      rw [fastAdd (by omega), hsz] at e1
      rw [fastAdd (by omega), hsz] at e2
      left
      refine ⟨n.toNat, Nat.le_refl _, by omega, by omega, by omega, ?_⟩
      exact (fwdCopy_snap ring _ _ _ (by omega) (by omega) (by rcases hsrc with e | e <;> omega)).symm
    · split
      · rename_i _ _ h3
        have hn32 : n.toNat ≤ 32 := by have := USize.le_iff_toNat_le.mp h3.1; rwa [h32] at this
        have hs32 : ((wpos - d) &&& mask).toNat + 32 ≤ 2 ^ k := by
          have := USize.le_iff_toNat_le.mp h3.2.1; rwa [fastIdx_add (by omega), hsz] at this
        have hw32 : wpos.toNat + 32 ≤ 2 ^ k := by
          have := USize.le_iff_toNat_le.mp h3.2.2; rwa [fastIdx_add (by omega), hsz] at this
        have sep : ∀ j, j ≤ 24 → ¬ d < USize.ofNat 8 → wpos.toNat + j ≤ ((wpos - d) &&& mask).toNat + j ∨
            ((wpos - d) &&& mask).toNat + j + 8 ≤ wpos.toNat + j := fun j _ hd8 => by
          have : 8 ≤ d.toNat := Nat.le_of_not_lt fun e => hd8 (USize.lt_iff_toNat_lt.mpr (by rw [h8]; exact e))
          rcases hsrc with e | e <;> omega
        have b1 := blk8_fwd ⟨ring, hs⟩ wpos ((wpos - d) &&& mask) d (by omega) (by omega) hR
          (fun hd8 => by have := sep 0 (by decide) hd8; omega)
        have bj : ∀ (j : Nat) (w : Win (2 ^ k)) (hj : j ≤ 24) (hjd : (wpos + USize.ofNat j).toNat + 8 ≤ 2 ^ k)
            (hjs : (((wpos - d) &&& mask) + USize.ofNat j).toNat + 8 ≤ 2 ^ k),
            (blk8 w (wpos + USize.ofNat j) (((wpos - d) &&& mask) + USize.ofNat j) d hjd hjs hR).1 =
              fwdCopy w.1 (wpos.toNat + j) (((wpos - d) &&& mask).toNat + j) 8 := by
          intro j w hj hjd hjs
          rw [blk8_fwd w _ _ d hjd hjs hR (fun hd8 => by
            rw [fastIdx_add (by omega), fastIdx_add (by omega)]
            exact sep j hj hd8), fastIdx_add (by omega), fastIdx_add (by omega)]
        have le : ∀ c, c < 2 ^ 32 → (n ≤ USize.ofNat c ↔ n.toNat ≤ c) := fun c hc => by
          rw [USize.le_iff_toNat_le, fastLit hc]
        left
        split
        · rename_i hb
          have := (le 8 (by decide)).mp hb
          refine ⟨8, by omega, by omega, by omega, by omega, b1⟩
        · rename_i hb
          have := mt (le 8 (by decide)).mpr hb
          split
          · rename_i hb'
            have := (le 16 (by decide)).mp hb'
            refine ⟨16, by omega, by omega, by omega, by omega, ?_⟩
            rw [bj 8 _ (by decide) _ _, b1, show (16 : Nat) = 8 + 8 from rfl, fwdCopy_add]
          · rename_i hb'
            have := mt (le 16 (by decide)).mpr hb'
            split
            · rename_i hb''
              have := (le 24 (by decide)).mp hb''
              refine ⟨24, by omega, by omega, by omega, by omega, ?_⟩
              rw [bj 16 _ (by decide) _ _, bj 8 _ (by decide) _ _, b1, show (24 : Nat) = 8 + 8 + 8 from rfl,
                fwdCopy_add, fwdCopy_add]
            · rename_i hb''
              have := mt (le 24 (by decide)).mpr hb''
              refine ⟨32, by omega, by omega, by omega, by omega, ?_⟩
              rw [bj 24 _ (by decide) _ _, bj 16 _ (by decide) _ _, bj 8 _ (by decide) _ _, b1,
                show (32 : Nat) = 8 + 8 + 8 + 8 from rfl, fwdCopy_add, fwdCopy_add, fwdCopy_add]
      · right
        rfl

/-- The fast copy leaves the window as the step machine's byte-by-byte copy does, but for bytes in the 16 of slack past
the copy's end. -/
theorem copyF_run (ring : ByteArray) (wpos d n mask size : USize) {k : Nat} (hk : k ≤ 24)
    (hm : mask.toNat = 2 ^ k - 1) (hsz : size.toNat = 2 ^ k) (hs : ring.size = 2 ^ k) (hw : wpos.toNat < 2 ^ k)
    (hd : d.toNat + 16 ≤ 2 ^ k) (hn1 : 1 ≤ n.toNat) (hd1 : 1 ≤ d.toNat) (hd2 : d.toNat ≤ 2 ^ k) (p1 p2 : UInt8)
    {out : List Nat}
    (h : RingOk (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hw).ring k
      (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hw).wpos.toNat out) :
    RingOk (copyF ring wpos d n mask size hk hm hsz hs hw hd) k
      (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hw).wpos.toNat out := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hSl : ((wpos - d) &&& mask).toNat < 2 ^ k := mask_lt hm
  have hsp : ((wpos - d) &&& mask).toNat % 2 ^ k = (wpos.toNat + 2 ^ k - d.toNat) % 2 ^ k := by
    rcases src_cases hk hm hw hd with e | e
    · rw [show wpos.toNat + 2 ^ k - d.toNat = ((wpos - d) &&& mask).toNat + 2 ^ k by omega, Nat.add_mod_right]
    · rw [← e]
  have hrun := copyMasked_run hk hm hsz hd1 hd2 n.toNat n ring wpos wpos ((wpos - d) &&& mask) p1 p2 hs hw rfl
    (Nat.mod_eq_of_lt hw) hsp
  rcases copyF_cases ring wpos d n mask size hk hm hsz hs hw hd hn1 with ⟨N, hN1, hN2, hwN, hsN, e⟩ | e
  · rw [e]
    have hfn : fwdCopy ring wpos.toNat ((wpos - d) &&& mask).toNat n.toNat =
        (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hw).ring := by
      rw [← hrun, copyMasked_fwd hk hm n.toNat ring wpos _ n hs rfl (by omega) (by omega)]
    rw [show N = n.toNat + (N - n.toNat) by omega, fwdCopy_add, hfn]
    refine h.slack (fwdCopy_size _ _ _ _) fun i _ hi _ => fwdCopy_out _ _ _ _ i fun hin => hi ?_
    have hp : (copyRun d mask size k hk hm hsz hd1 hd2 n ring wpos p1 p2 hs hw).wpos.toNat =
        wpos.toNat + n.toNat := by
      rw [copyRun_wpos hk hm hsz hd1 hd2 _ n ring wpos p1 p2 hs hw rfl, USize.toNat_and, hm,
        Nat.and_two_pow_sub_one_eq_mod, fastAdd (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hp]
    omega
  · rw [e, hrun]
    exact h

/-! ### The context bytes after a copy -/

/-- The position `d + 1` before `x`, reduced modulo the window, is where the ring next written at `x`'s place holds the
byte `d` back. -/
theorem ringIdx_mod {x R d : Nat} (hR : 0 < R) (hd : d < R) :
    (x + R - 1 - d) % R = ringIdx R (x % R) d := by
  have hq := Nat.div_add_mod x R
  have hr := Nat.mod_lt x hR
  unfold ringIdx
  split
  · rw [show x + R - 1 - d = (x % R - 1 - d) + R * (x / R + 1) by rw [Nat.mul_add, Nat.mul_one]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rw [show x + R - 1 - d = (x % R + R - 1 - d) + R * (x / R) by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]

/-- A position less `c`, masked to the window: the difference modulo the window, even where the subtraction wraps. -/
theorem sub_mask {x c mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) (hc : c.toNat ≤ 2 ^ k) :
    ((x - c) &&& mask).toNat = (x.toNat + 2 ^ k - c.toNat) % 2 ^ k := by
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hP : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := Nat.pow_le_pow_right (by decide) hb
  have hdv : 2 ^ k ∣ 2 ^ System.Platform.numBits := Nat.pow_dvd_pow 2 (by omega)
  rw [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, USize.toNat_sub, Nat.mod_mod_of_dvd _ hdv]
  obtain ⟨q, hq⟩ := hdv
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with e | e
    · rw [e, Nat.mul_zero] at hq
      have := Nat.two_pow_pos System.Platform.numBits
      omega
    · exact e
  have e1 : 2 ^ k * (q - 1) = 2 ^ k * q - 2 ^ k := by rw [Nat.mul_sub, Nat.mul_one]
  have e2 : 2 ^ k ≤ 2 ^ k * q := Nat.le_mul_of_pos_right _ hq1
  rw [hq, show 2 ^ k * q - c.toNat + x.toNat = (x.toNat + 2 ^ k - c.toNat) + 2 ^ k * (q - 1) by omega,
    Nat.add_mul_mod_self_left]

/-- The byte `d + 1` before the loop's unmasked position, read through the mask, is the output's byte `d` back. -/
theorem wget_back {ring : ByteArray} {x mask c : USize} {k d : Nat} {out : List Nat} (hk : k ≤ 24)
    (hm : mask.toNat = 2 ^ k - 1) (hs : ring.size = 2 ^ k) (h : RingOk ring k (x &&& mask).toNat out)
    (hc : c.toNat = d + 1) (hd : d + 1 + 16 ≤ 2 ^ k) (hdl : d < out.length) :
    (wget ring (x - c) mask hm hs).toNat = out.getD d 0 := by
  unfold wget
  have e := h.read (d := d + 1) (by omega) hd (by omega) (p := (x - c) &&& mask) ?_
    (by have := mask_lt (i := x - c) hm; omega)
  · rw [Nat.add_sub_cancel] at e
    exact e
  · rw [sub_mask hk hm (by omega), hc, Nat.add_sub_cancel, USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod,
      show x.toNat + 2 ^ k - (d + 1) = x.toNat + 2 ^ k - 1 - d by omega]
    exact ringIdx_mod (Nat.two_pow_pos _) (by omega)

/-- The two bytes before the loop's unmasked position, read through the mask, are the output's context bytes. -/
theorem wget_ctx {ring : ByteArray} {x mask : USize} {k : Nat} {out : List Nat} (hk : k ≤ 24)
    (hm : mask.toNat = 2 ^ k - 1) (h18 : 18 ≤ 2 ^ k) (hs : ring.size = 2 ^ k) (h : RingOk ring k (x &&& mask).toNat out)
    (hl : 2 ≤ out.length) :
    contextBytes out =
      ((wget ring (x - USize.ofNat 1) mask hm hs).toNat, (wget ring (x - USize.ofNat 2) mask hm hs).toNat) := by
  rw [wget_back (d := 0) hk hm hs h (fastLit (by decide)) (by omega) (by omega),
    wget_back (d := 1) hk hm hs h (fastLit (by decide)) (by omega) (by omega)]
  match out, hl with
  | _ :: _ :: _, _ => rfl

/-! ### A copy -/

/-- A whole copy, as a move: the step machine's copy with the chunk ending where it starts and room for all of it, with
the fast copy's window and the context bytes read back from it. -/
theorem copy_move {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd} {pos : USize}
    (hrel : Rel w k.toNat m st (.copy s d n)) (hn1 : 1 ≤ n) (hroom : st.pend.toNat + n + 16 ≤ 2 ^ k.toNat)
    (hp : pos.toNat ≤ stop.toNat) (hk : k.toNat ≤ 24) (hsz : st.ring.size = 2 ^ k.toNat)
    (hwp : st.wpos.toNat < 2 ^ k.toNat) (hd : st.dist.toUSize.toNat + 16 ≤ 2 ^ k.toNat) {ring' : ByteArray}
    (hR : ring' = copyF st.ring st.wpos st.dist.toUSize st.left.toUSize (ringMask k) (ringSize k) hk
      (ringMask_toNat hk) (ringSize_toNat hk) hsz hwp hd) (hs' : ring'.size = 2 ^ k.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.copy s d n) st pos p'
      { st with
        ring := ring', wpos := (st.wpos + st.left.toUSize) &&& ringMask k
        p1 := wget ring' (st.wpos + st.left.toUSize - USize.ofNat 1) (ringMask k) (ringMask_toNat hk) hs'
        p2 := wget ring' (st.wpos + st.left.toUSize - USize.ofNat 2) (ringMask k) (ringMask_toNat hk) hs'
        left := 0, pend := st.pend + st.left.toUSize
        written := usmin (ringSize k - USize.ofNat 16) (st.written + st.left.toUSize), pos := pos
        status := .next } := by
  obtain ⟨hC, htag, hprod, hdist, hleft, hd1, hdw, hdo⟩ := hrel
  have hR24 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have hR10 : 2 ^ 10 ≤ 2 ^ k.toNat := Nat.pow_le_pow_right (by decide) hC.k10
  have h1024 : (2 : Nat) ^ 10 = 1024 := rfl
  have hpL := hC.pendLe
  have hwin := hC.win
  have hrunN : st.left.toUSize.toNat = n := by rw [word_toUSize (by omega), hleft]
  have hdU : st.dist.toUSize.toNat = d := by rw [word_toUSize (by omega), hdist]
  have hd1' : 1 ≤ st.dist.toUSize.toNat := by omega
  have hd2' : st.dist.toUSize.toNat ≤ 2 ^ k.toNat := by omega
  have hspec := copyRun_spec hk (ringMask_toNat hk) (ringSize_toNat hk) hd1' hd2' hd n st.left.toUSize st.ring st.wpos
    st.p1 st.p2 hsz hwp s.output hrunN (by omega) hC.ring hC.ctx hC.bytes
  dsimp only at hspec
  rw [hdU] at hspec
  obtain ⟨h1, _, h3, h4⟩ := hspec
  have h1' := copyF_run st.ring st.wpos st.dist.toUSize st.left.toUSize (ringMask k) (ringSize k) hk
    (ringMask_toNat hk) (ringSize_toNat hk) hsz hwp hd (by omega) hd1' hd2' st.p1 st.p2 h1
  rw [← hR, copyRun_wpos hk (ringMask_toNat hk) (ringSize_toNat hk) hd1' hd2' _ st.left.toUSize st.ring st.wpos st.p1
    st.p2 hsz hwp rfl] at h1'
  rw [← hrunN] at h1' h3 h4
  have h2' := wget_ctx (x := st.wpos + st.left.toUSize) hk (ringMask_toNat hk) (by omega) hs' h1' (by omega)
  have hstep := copy_after (stop := pos) (K := K) (a := a) hC htag hprod hdist hleft hd1 hdw hdo (Nat.le_refl _)
    (run := st.left.toUSize)
    (r := ⟨ring', (st.wpos + st.left.toUSize) &&& ringMask k,
      wget ring' (st.wpos + st.left.toUSize - USize.ofNat 1) (ringMask k) (ringMask_toNat hk) hs',
      wget ring' (st.wpos + st.left.toUSize - USize.ofNat 2) (ringMask k) (ringMask_toNat hk) hs'⟩)
    (by omega) (by omega) (by omega) h1' h2' h3 h4
  obtain ⟨p', hmv⟩ := hstep.widen rfl rfl hp
  refine ⟨p', ?_⟩
  have e0 : st.left.toUSize.toUInt64 = st.left :=
    UInt64.toNat_inj.mp (by rw [USize.toNat_toUInt64, word_toUSize (by omega)])
  dsimp only [finishCopy, clearRing] at hmv
  rw [e0, UInt64.sub_self] at hmv
  exact hmv

/-! ### The steps between the fast loop's reads, as moves -/

/-- The end of a copy: the next command. -/
theorem copyEnd_move {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd} {pos : USize}
    (hrel : Rel w k.toNat m st (.copy s d n)) (h0 : st.left = 0) (hp : pos.toNat ≤ stop.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.copy s d n) st pos p'
      { st with tag := .command, pos := pos, status := .next } := by
  have h := stepCopy_ok (K := K) (a := a) (stop := pos) (pos := pos) hrel (Nat.le_refl _)
  have e : stepCopy k st pos = { st with tag := .command, pos := pos, status := .next } := by
    unfold stepCopy
    rw [ite_eq_left h0]
  rw [e] at h
  exact h.widen rfl rfl hp

/-- The end of a command's literals: its distance. -/
theorem litEnd_move {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState}
    {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {st : Cmd} {pos : USize} (hH : HdrRel H m)
    (hrel : Rel w k.toNat m st (.literals s ic c ilen clen n lit out)) (h0 : st.left = 0) (hp : pos.toNat ≤ stop.toNat)
    (hs : stop.toNat ≤ a.size) :
    ∃ p', MoveOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out) st pos p'
      { st with tag := .distance, pos := pos, status := .next } := by
  have h := stepLiterals_ok (K := K) (stop := pos) (hs := Nat.le_trans hp hs) hH hrel (Nat.le_refl _) (Or.inr rfl)
  have e : stepLiterals H k a pos (Nat.le_trans hp hs) st pos =
      { st with tag := .distance, pos := pos, status := .next } := by
    unfold stepLiterals
    rw [ite_eq_left h0]
  rw [e] at h
  exact h.widen rfl rfl hp

/-- The start of a command within its block: the insert-and-copy element. -/
theorem cmd_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {st : Cmd} {pos : USize}
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    (hrel : Rel w k m st (.command s)) (hr : st.remaining ≠ 0) (hi : st.iCount ≠ 0) (hp : pos.toNat ≤ stop.toNat) :
    ∃ p', MoveOk w k m K a stop (.command s) st pos p'
      { st with iCount := st.iCount - 1, tag := .insertCopy, pos := pos, status := .next } := by
  have h := stepCommand_ok (a := a) (stop := pos) hK hH hrel (Nat.le_refl _) (Or.inr rfl)
  have e : stepCommand H st pos =
      { st with iCount := st.iCount - 1, tag := .insertCopy, pos := pos, status := .next } := by
    unfold stepCommand
    rw [ite_eq_right hr, ite_eq_right hi]
  rw [e] at h
  exact h.widen rfl rfl hp

/-- The start of a distance implied 0 (the last distance), within the window and the meta-block: the copy. -/
theorem distImplicit_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {s : CommandState} {c clen : Nat} {st : Cmd}
    {pos : USize} (hH : HdrRel H m) (hrel : Rel w k m st (.distance s c clen)) (hr : st.remaining ≠ 0)
    (hc : st.code < 128) (hd : st.d0 ≠ 0) (hw : ¬ st.written.toUInt64 < st.d0) (hrc : ¬ st.remaining < st.clen)
    (hp : pos.toNat ≤ stop.toNat) :
    ∃ p', MoveOk w k m K a stop (.distance s c clen) st pos p'
      { st with
        remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
        ext := { st.ext with dist := st.d0 } } := by
  have h := stepDistance_ok (K := K) (a := a) (stop := pos) hH hrel (Nat.le_refl _) (Or.inr rfl)
  have e : stepDistance H st pos =
      { st with
        remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
        ext := { st.ext with dist := st.d0 } } := by
    unfold stepDistance applyDistance
    rw [ite_eq_right hr, ite_eq_left hc, ite_eq_right hd, ite_eq_right hw, ite_eq_right hrc, ite_eq_left rfl]
  rw [e] at h
  exact h.widen rfl rfl hp

/-- The start of a distance read within its block: the distance's symbol. -/
theorem distCount_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {s : CommandState} {c clen : Nat} {st : Cmd}
    {pos : USize} (hH : HdrRel H m) (hrel : Rel w k m st (.distance s c clen)) (hr : st.remaining ≠ 0)
    (hc : ¬ st.code < 128) (hd : st.dCount ≠ 0) (hp : pos.toNat ≤ stop.toNat) :
    ∃ p', MoveOk w k m K a stop (.distance s c clen) st pos p'
      { st with dCount := st.dCount - 1, tag := .distanceSymbol, pos := pos, status := .next } := by
  have h := stepDistance_ok (K := K) (a := a) (stop := pos) hH hrel (Nat.le_refl _) (Or.inr rfl)
  have e : stepDistance H st pos =
      { st with dCount := st.dCount - 1, tag := .distanceSymbol, pos := pos, status := .next } := by
    unfold stepDistance
    rw [ite_eq_right hr, ite_eq_right hc, ite_eq_right hd]
  rw [e] at h
  exact h.widen rfl rfl hp

/-! ### A literal round -/

theorem ringWrite_wput {ring : ByteArray} {opos mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1)
    (hs : ring.size = 2 ^ k) (v : UInt8) (h : (opos &&& mask).toNat < ring.size) :
    ringWrite ring (opos &&& mask) v h = wput ring opos mask hk hm hs v := by
  unfold ringWrite wput
  have := wix_lt (i := opos) hk hm
  exact uset_congr (USize.toNat_inj.mp (wix_toNat this).symm) rfl

/-- One literal of the fast loop (a refill to 15 bits, then the read at the context's tree) is a move from the record a
fast state stands for to the record one byte on. -/
theorem lit_round {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
    {K : CommandState → List Bool → Option α} {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState}
    {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {word count : UInt64} {ring : ByteArray}
    {opos mask pB cap cap16 wB : USize} {rEnd bEnd : UInt64} {iCount LC dCount : UInt64} {flags : Flags} {x : CmdExt}
    {d01 d23 code ilen' clen' : UInt64} {p1 p2 : UInt8} {L : UInt64} {pos : USize} {T : ByteArray} {tb : UInt64}
    {modeOff lRow iRow iFb dRow s0 : USize} (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0)
    (hH : HdrRel H m)
    (hrel : Rel w k.toNat m (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen' clen' p1 p2 .literals L pos) (.literals s ic c ilen clen n lit out))
    (hk : k.toNat ≤ 24) (h16 : 16 ≤ 2 ^ k.toNat) (hmk : mask = ringMask k) (hmN : mask.toNat = 2 ^ k.toNat - 1)
    (hcap : cap16 = ringSize k - USize.ofNat 16) {ahead : Nat} (N : FNum opos pB wB rEnd bEnd k.toNat ahead)
    (ha : 1 ≤ ahead) (hL : 1 ≤ L.toNat) (hLC : 1 ≤ LC.toNat) {word' count' : UInt64} {pos' : USize}
    (hf : FillOk a stop word count pos 15 word' count' pos') (hs : stop.toNat ≤ a.size)
    (hsz : ring.size = 2 ^ k.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen' clen' p1 p2
        .literals L pos) pos p'
      (fexit (word' >>> (litT C p1 p2 word' &&& 15)) (count' - (litT C p1 p2 word' &&& 15))
        (wput ring opos mask hk hmN hsz (litT C p1 p2 word' >>> 4).toUInt8) (opos + USize.ofNat 1) mask pB cap cap16
        wB rEnd iCount (LC - 1) dCount flags x d01 d23 code ilen' clen' (litT C p1 p2 word' >>> 4).toUInt8 p1 .literals
        (L - 1) pos') := by
  have m1 := fill_move (K := K) hrel hf
  obtain ⟨base, hfit, hb, he⟩ := C.litT_lookup p1 p2 word'
  have hpend := N.pend
  have hah := N.ahead
  have hwp : (opos &&& mask).toNat < 2 ^ k.toNat := mask_lt hmN
  obtain ⟨p', m2⟩ := lit_move (K := K) (stop := stop) (pos := pos') hH m1.rel (by exact hL) (by exact hLC)
    (by show (opos + pB).toNat + 1 + 16 ≤ _; omega) hf.posStop hs C.hl C.mode C.hm C.hm512 hfit hb
    (by
      show lookup H.arena base word' hfit H.lit.arena32 &&& 15 ≤ count'
      have := and15_lt (lookup H.arena base word' hfit H.lit.arena32)
      have := hf.enough
      exact UInt64.le_iff_toNat_le.mpr (by omega)) hsz hwp
  refine ⟨p', ?_⟩
  have e := fexit_succ (word := word) (count := count) (ring := ring)
    (word' := word' >>> (lookup H.arena base word' hfit H.lit.arena32 &&& 15))
    (count' := count' - (lookup H.arena base word' hfit H.lit.arena32 &&& 15))
    (ring' := ringWrite ring (opos &&& mask) (lookup H.arena base word' hfit H.lit.arena32 >>> 4).toUInt8 (by omega))
    (q1 := (lookup H.arena base word' hfit H.lit.arena32 >>> 4).toUInt8) (q2 := p1) (pos := pos) (pos' := pos')
    (iCount := iCount) (lc := LC) (dCount := dCount) (flags := flags) (x := x) (d01 := d01) (d23 := d23) (code := code)
    (ilen := ilen') (clen := clen') (p1 := p1) (p2 := p2) (tag := .literals) (lf := L) (cap := cap) hk h16 hmk hcap N ha
  have e' := m1.trans m2
  rw [he, ← ringWrite_wput hk hmN hsz _ (by omega), ← e]
  exact e'

end Brotli.Decoder
