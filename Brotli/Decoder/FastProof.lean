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
