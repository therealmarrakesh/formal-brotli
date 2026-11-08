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

/-! The place a state stands for has the form its tag names. -/

theorem Rel.copyLength_of (h : Rel w k m r p) (ht : r.tag = .copyLength) :
    ∃ s ic c ilen cb cbase, p = .copyLength s ic c ilen cb cbase := by
  cases p with
  | copyLength s ic c ilen cb cbase => exact ⟨s, ic, c, ilen, cb, cbase, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.copy_of (h : Rel w k m r p) (ht : r.tag = .copy) : ∃ s d n, p = .copy s d n := by
  cases p with
  | copy s d n => exact ⟨s, d, n, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.distanceSymbol_of (h : Rel w k m r p) (ht : r.tag = .distanceSymbol) :
    ∃ s clen dist, p = .distanceSymbol s clen dist := by
  cases p with
  | distanceSymbol s clen dist => exact ⟨s, clen, dist, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.literals_of (h : Rel w k m r p) (ht : r.tag = .literals) :
    ∃ s ic c ilen clen n lit out, p = .literals s ic c ilen clen n lit out := by
  cases p with
  | literals s ic c ilen clen n lit out => exact ⟨s, ic, c, ilen, clen, n, lit, out, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.distance_of (h : Rel w k m r p) (ht : r.tag = .distance) : ∃ s c clen, p = .distance s c clen := by
  cases p with
  | distance s c clen => exact ⟨s, c, clen, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.command_of (h : Rel w k m r p) (ht : r.tag = .command) : ∃ s, p = .command s := by
  cases p with
  | command s => exact ⟨s, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

theorem Rel.insertCopy_of (h : Rel w k m r p) (ht : r.tag = .insertCopy) : ∃ s ic, p = .insertCopy s ic := by
  cases p with
  | insertCopy s ic => exact ⟨s, ic, rfl⟩
  | literalSymbol => exact h.elim
  | _ => exact Tag.noConfusion (h.2.1.symm.trans ht)

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

/-- Masking before an addition changes nothing once the sum is masked. -/
theorem mask_add {x y mask : USize} {k : Nat} (hk : k ≤ 24) (hm : mask.toNat = 2 ^ k - 1) :
    ((x &&& mask) + y) &&& mask = (x + y) &&& mask := by
  have hb : 32 ≤ System.Platform.numBits := by rcases System.Platform.numBits_eq with h | h <;> omega
  have hdv : 2 ^ k ∣ 2 ^ System.Platform.numBits := Nat.pow_dvd_pow 2 (by omega)
  apply USize.toNat_inj.mp
  simp only [USize.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, USize.toNat_add]
  rw [Nat.mod_mod_of_dvd _ hdv, Nat.mod_mod_of_dvd _ hdv, Nat.mod_add_mod]

/-- A whole copy, as a move: the step machine's copy with the chunk ending where it starts and room for all of it, with
the fast copy's window and the context bytes read back from it, at the loop's unmasked position `x`. -/
theorem copy_move {α : Type} {w : Nat} {k : USize} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {d n : Nat} {st : Cmd} {pos : USize}
    (hrel : Rel w k.toNat m st (.copy s d n)) (hn1 : 1 ≤ n) (hroom : st.pend.toNat + n + 16 ≤ 2 ^ k.toNat)
    (hp : pos.toNat ≤ stop.toNat) (hk : k.toNat ≤ 24) (hsz : st.ring.size = 2 ^ k.toNat)
    (hwp : st.wpos.toNat < 2 ^ k.toNat) (hd : st.dist.toUSize.toNat + 16 ≤ 2 ^ k.toNat) {ring' : ByteArray}
    (hR : ring' = copyF st.ring st.wpos st.dist.toUSize st.left.toUSize (ringMask k) (ringSize k) hk
      (ringMask_toNat hk) (ringSize_toNat hk) hsz hwp hd) (hs' : ring'.size = 2 ^ k.toNat) {x : USize}
    (hx : st.wpos = x &&& ringMask k) :
    ∃ p', MoveOk w k.toNat m K a stop (.copy s d n) st pos p'
      { st with
        ring := ring', wpos := (x + st.left.toUSize) &&& ringMask k
        p1 := wget ring' (x + st.left.toUSize - USize.ofNat 1) (ringMask k) (ringMask_toNat hk) hs'
        p2 := wget ring' (x + st.left.toUSize - USize.ofNat 2) (ringMask k) (ringMask_toNat hk) hs'
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
  rw [hx, mask_add hk (ringMask_toNat hk)] at h1'
  rw [← hrunN] at h1' h3 h4
  have h2' := wget_ctx (x := x + st.left.toUSize) hk (ringMask_toNat hk) (by omega) hs' h1' (by omega)
  have hstep := copy_after (stop := pos) (K := K) (a := a) hC htag hprod hdist hleft hd1 hdw hdo (Nat.le_refl _)
    (run := st.left.toUSize)
    (r := ⟨ring', (x + st.left.toUSize) &&& ringMask k,
      wget ring' (x + st.left.toUSize - USize.ofNat 1) (ringMask k) (ringMask_toNat hk) hs',
      wget ring' (x + st.left.toUSize - USize.ofNat 2) (ringMask k) (ringMask_toNat hk) hs'⟩)
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

/-! ### A distance's symbol -/

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}

/-- The arena's mask for `n` bits, below 32, is `2 ^ n - 1`. -/
theorem FCtx.maskT_eq (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) {n : UInt64} (hn : n.toNat < 32) :
    maskT T C.big C.size32 n = ((1 : UInt64) <<< n) - 1 := by
  have h31 : (n &&& 31).toNat = n.toNat := by
    rw [UInt64.toNat_and, show (31 : UInt64).toNat = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt hn]
  have hp : 2 ^ n.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hone : ((1 : UInt64) <<< n).toNat = 2 ^ n.toNat := by
    simp only [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (show n.toNat < 64 by omega)]
    rw [show (1 : UInt64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt hp
  apply UInt64.toNat_inj.mp
  unfold maskT
  rw [load64_toNat, u64_shl (by decide) (by rw [h31]; omega), h31, u64_sub_le (by rw [hone]; exact Nat.one_le_two_pow),
    hone, show n.toNat * 2 ^ 3 = 8 * n.toNat by rw [Nat.mul_comm], C.tab.masks _ hn]
  rfl

/-- The shared distance table's entry for a symbol is `dEntry`. -/
theorem FCtx.dshT_eq (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) {dc : UInt64} (hd : dc.toNat < 520) :
    dshT T s0 C.s0Le C.size32 dc hd = dEntry H.npostfix H.ndirect dc := by
  have := C.s0Le
  have := C.size32
  apply UInt64.toNat_inj.mp
  unfold dshT
  rw [load64_toNat, fastAdd (by rw [u64_shl (by decide) (by omega)]; omega), u64_shl (by decide) (by omega),
    show dc.toNat * 2 ^ 3 = 8 * dc.toNat by rw [Nat.mul_comm], C.s0, C.tab.dsh _ hd, UInt64.ofNat_toNat]

/-- A distance symbol from the context's tree is in the header's distance alphabet. -/
theorem FCtx.dAlpha (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) {m : MetaBlockHeader}
    (hH : HdrRel H m) (clen w : UInt64) :
    (wordSym (lookupT T (dRowBase C clen) w (C.dIn clen) C.lim C.size32)).toNat <
      distanceAlphabetSize H.npostfix.toNat H.ndirect.toNat := by
  have hc := distanceContextId_lt clen.toNat
  have hd := C.hd
  have hJ : 4 * dCur.toNat + distanceContextId clen.toNat < H.dMap.size := by rw [H.dMapSize]; omega
  obtain ⟨code, _, hok, hC, hS⟩ := hH.d _ (tree_dMap H hJ)
  rw [← C.dRowBase_toNat, ← C.arena] at hok
  rw [hH.npostfix, hH.ndirect]
  exact lookupT_sym (C.dIn clen) C.lim C.size32 hok hC hS w

end

theorem lookup_base_congr {t : ByteArray} {b1 b2 : USize} {w : UInt64} {h1 : TableFits t b1.toNat}
    {h2 : TableFits t b2.toNat} {h32 h32' : t.size < 2 ^ 32} (e : b1 = b2) :
    lookup t b1 w h1 h32 = lookup t b2 w h2 h32' := by
  subst e
  rfl

/-- The step machine's distance symbol reads at the fast loop's table base for the copy length's context. -/
theorem stepDistanceSymbol_fast {H : Hdr} {T : ByteArray} {lCur iCur tb : UInt64}
    {modeOff lRow iRow iFb dRow s0 : USize} {st : Cmd} (C : FCtx H T lCur iCur st.dCur tb modeOff lRow iRow iFb dRow s0)
    (pos : USize) :
    stepDistanceSymbol H st pos =
      distanceStep H st pos (lookupT T (dRowBase C st.clen) st.word (C.dIn st.clen) C.lim C.size32) := by
  have hd := C.hd
  have h1 := H.dMap32
  have h2 := H.dMapSize
  unfold stepDistanceSymbol distanceThrough
  rw [dite_eq_left (UInt64.lt_iff_toNat_lt.mpr hd)]
  dsimp only
  congr 1
  rw [lookupT_eq]
  have hT := C.arena
  subst hT
  apply lookup_base_congr
  apply USize.toNat_inj.mp
  rw [tableBase_toNat, UInt8.toNat_toUInt64, uget_toNat, dMapIndex_toNat (by omega), C.dRowBase_toNat]
  rfl

/-- `applyDistance` within the window and the meta-block goes on, where it is. -/
theorem applyDistance_next {st : Cmd} {pos : USize} {dcode d : UInt64} (hw : ¬ st.written.toUInt64 < d)
    (hrc : ¬ st.remaining < st.clen) :
    (applyDistance st pos dcode d).status = .next ∧ (applyDistance st pos dcode d).pos = pos := by
  unfold applyDistance
  rw [ite_eq_right hw, ite_eq_right hrc]
  split <;> exact ⟨rfl, rfl⟩

theorem u64_shr_zero (x : UInt64) : x >>> 0 = x := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight]
  rfl

theorem distFast_short {np nd d0 d1 d2 d3 dc x : UInt64} (h16 : dc < 16) :
    distFast np nd d0 d1 d2 d3 dc x = shortDist d0 d1 d2 d3 dc := by
  unfold distFast
  rw [ite_eq_left h16]

theorem u64_zero_le (x : UInt64) : 0 ≤ x := UInt64.le_iff_toNat_le.mpr (Nat.zero_le _)

/-- The distance's symbol, a short code: one of the last distances, adjusted. As a move, to `applyDistance` with the
code word's bits dropped. -/
theorem distShort_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {clen : Nat} {dist : BlockState} {st : Cmd} {pos : USize}
    {T : ByteArray} {lCur iCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T lCur iCur st.dCur tb modeOff lRow iRow iFb dRow s0) (hH : HdrRel H m)
    (hrel : Rel w k m st (.distanceSymbol s clen dist)) (hp : pos.toNat ≤ stop.toNat) {v : UInt64}
    (hv : v = lookupT T (dRowBase C st.clen) st.word (C.dIn st.clen) C.lim C.size32) (hl : wordBits v ≤ st.count)
    (h16 : wordSym v < 16) (hd0 : shortFast st.d0 st.d1 st.d2 st.d3 (wordSym v) ≠ 0)
    (hw : ¬ st.written.toUInt64 < shortFast st.d0 st.d1 st.d2 st.d3 (wordSym v)) (hrc : ¬ st.remaining < st.clen) :
    ∃ p', MoveOk w k m K a stop (.distanceSymbol s clen dist) st pos p'
      (applyDistance (setBits st (st.word >>> wordBits v) (st.count - wordBits v)) pos (wordSym v)
        (shortFast st.d0 st.d1 st.d2 st.d3 (wordSym v))) := by
  have hrel0 := hrel
  obtain ⟨hC, _, _, _⟩ := hrel
  have h0lt : st.d0.toNat < 2 ^ 32 := by rw [← hC.d0]; exact hC.dsLt.1
  have h1lt : st.d1.toNat < 2 ^ 32 := by rw [← hC.d1]; exact hC.dsLt.2.1
  have hwr := hC.written
  have hwin := hC.win
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hC.k24
  have hlt : (shortFast st.d0 st.d1 st.d2 st.d3 (wordSym v)).toNat < 2 ^ 32 := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hw)
    rw [USize.toNat_toUInt64] at this
    have : min w s.output.length ≤ w := Nat.min_le_left _ _
    omega
  have hsf := shortFast_eq h0lt h1lt (UInt64.lt_iff_toNat_lt.mp h16) hd0 hlt
  have h := stepDistanceSymbol_ok (K := K) (a := a) (stop := pos) hH hrel0 (Nat.le_refl _) (Or.inr rfl)
  rw [stepDistanceSymbol_fast C pos, ← hv] at h
  have hnd := H.ndLe
  have hx : extraBitsFast H.npostfix H.ndirect (wordSym v) = 0 := by
    have h16' := UInt64.lt_iff_toNat_lt.mp h16
    unfold extraBitsFast
    rw [ite_eq_left (UInt64.lt_iff_toNat_lt.mpr (by
      rw [u64_add_small (by rw [show (16 : UInt64).toNat = 16 from rfl]; omega)]
      exact Nat.lt_of_lt_of_le h16' (Nat.le_add_right _ _)))]
  have e : distanceStep H st pos v = applyDistance (setBits st (st.word >>> wordBits v) (st.count - wordBits v)) pos
      (wordSym v) (shortFast st.d0 st.d1 st.d2 st.d3 (wordSym v)) := by
    unfold distanceStep
    dsimp only
    rw [ite_eq_left hl, hx, ite_eq_left (show (0 : UInt64) ≤ 24 by decide), ite_eq_left (u64_zero_le _),
      distFast_short h16, ← hsf, ite_eq_right hd0]
    simp only [BitBuffer.drop, u64_shr_zero, UInt64.sub_zero]
  rw [e] at h
  obtain ⟨hs1, hs2⟩ := applyDistance_next (st := setBits st (st.word >>> wordBits v) (st.count - wordBits v))
    (pos := pos) (dcode := wordSym v) hw hrc
  exact h.widen hs1 hs2 hp

/-- The distance's symbol, from 16 on: the shared table's distance with no extra bits, plus the extra bits shifted by
NPOSTFIX. As a move, to `applyDistance` with the code word's and the extra bits dropped. -/
theorem distLong_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {clen : Nat} {dist : BlockState} {st : Cmd} {pos : USize}
    {T : ByteArray} {lCur iCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T lCur iCur st.dCur tb modeOff lRow iRow iFb dRow s0) (hH : HdrRel H m)
    (hrel : Rel w k m st (.distanceSymbol s clen dist)) (hp : pos.toNat ≤ stop.toNat) {v E D : UInt64}
    (hv : v = lookupT T (dRowBase C st.clen) st.word (C.dIn st.clen) C.lim C.size32) (h16 : ¬ wordSym v < 16)
    (hE : E = dEntry H.npostfix H.ndirect (wordSym v))
    (hD : D = (E >>> 32) + (((st.word >>> wordBits v) &&& maskT T C.big C.size32 (E &&& 31)) <<< H.npostfix))
    (hok : wordBits v + (E &&& 31) ≤ st.count) (hd0 : D ≠ 0) (hw : ¬ st.written.toUInt64 < D)
    (hrc : ¬ st.remaining < st.clen) :
    ∃ p', MoveOk w k m K a stop (.distanceSymbol s clen dist) st pos p'
      (applyDistance (setBits st ((st.word >>> wordBits v) >>> (E &&& 31)) (st.count - wordBits v - (E &&& 31))) pos
        (wordSym v) D) := by
  have hrel0 := hrel
  have hnp := H.npLe
  have hnd := H.ndLe
  have hsymA : (wordSym v).toNat < distanceAlphabetSize H.npostfix.toNat H.ndirect.toNat := by
    rw [hv]
    exact C.dAlpha hH st.clen st.word
  have hn24 := (distanceExtraBits_le_iff _ _ _).mp hsymA
  have hbitsE : (extraBitsFast H.npostfix H.ndirect (wordSym v)).toNat =
      distanceExtraBits H.npostfix.toNat H.ndirect.toNat (wordSym v).toNat :=
    extraBitsFast_toNat hnp hnd (wordValue_lt v)
  obtain ⟨eA, eB⟩ := dEntry_split hnp hnd (wordValue_lt v) h16 (by rw [hbitsE]; exact hn24)
  rw [← hE] at eA eB
  rw [eA] at hok hD
  rw [eA]
  have hlv : (wordBits v).toNat < 16 := and15_lt v
  have hok' := UInt64.le_iff_toNat_le.mp hok
  rw [u64_add_small (by omega)] at hok'
  have hl : wordBits v ≤ st.count := UInt64.le_iff_toNat_le.mpr (by omega)
  have hnbc : extraBitsFast H.npostfix H.ndirect (wordSym v) ≤ ((BitBuffer.mk st.word st.count).drop (wordBits v)).count :=
    UInt64.le_iff_toNat_le.mpr (by
      rw [drop_count (UInt64.le_iff_toNat_le.mp hl)]
      show (extraBitsFast H.npostfix H.ndirect (wordSym v)).toNat ≤ st.count.toNat - (wordBits v).toNat
      omega)
  have hDeq : distFast H.npostfix H.ndirect st.d0 st.d1 st.d2 st.d3 (wordSym v)
      (((BitBuffer.mk st.word st.count).drop (wordBits v)).peek (extraBitsFast H.npostfix H.ndirect (wordSym v))) = D := by
    rw [distFast_split h16, hD, eB]
    congr 1
    split
    · rename_i hdir
      have h0 : extraBitsFast H.npostfix H.ndirect (wordSym v) = 0 := by
        unfold extraBitsFast
        rw [ite_eq_left hdir]
      rw [h0, C.maskT_eq (by decide), show ((1 : UInt64) <<< 0) - 1 = 0 by decide, UInt64.and_zero]
      exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_shiftLeft]; simp)
    · rw [C.maskT_eq (by omega)]
      rfl
  have h := stepDistanceSymbol_ok (K := K) (a := a) (stop := pos) hH hrel0 (Nat.le_refl _) (Or.inr rfl)
  rw [stepDistanceSymbol_fast C pos, ← hv] at h
  have e : distanceStep H st pos v = applyDistance (setBits st ((st.word >>> wordBits v) >>>
      extraBitsFast H.npostfix H.ndirect (wordSym v)) (st.count - wordBits v - extraBitsFast H.npostfix H.ndirect
      (wordSym v))) pos (wordSym v) D := by
    unfold distanceStep
    dsimp only
    rw [ite_eq_left hl, ite_eq_left (UInt64.le_iff_toNat_le.mpr (by rw [hbitsE]; exact hn24)), ite_eq_left hnbc,
      hDeq, ite_eq_right hd0]
    simp only [BitBuffer.drop]
  rw [e] at h
  obtain ⟨hs1, hs2⟩ := applyDistance_next (st := setBits st ((st.word >>> wordBits v) >>>
      extraBitsFast H.npostfix H.ndirect (wordSym v)) (st.count - wordBits v - extraBitsFast H.npostfix H.ndirect
      (wordSym v))) (pos := pos) (dcode := wordSym v) hw hrc
  exact h.widen hs1 hs2 hp

/-! ### The insert-and-copy element -/

/-- The step machine's insert-and-copy symbol reads at the fast loop's tree base. -/
theorem stepInsertCopy_fast {H : Hdr} {T : ByteArray} {lCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    {st : Cmd} (C : FCtx H T lCur st.iCur dCur tb modeOff lRow iRow iFb dRow s0) (pos : USize) :
    stepInsertCopy H st pos = insertStep st pos (lookupT T (icFbBase C) st.word C.icIn C.lim C.size32) := by
  have hi := C.hi
  unfold stepInsertCopy
  rw [dite_eq_left (UInt64.lt_iff_toNat_lt.mpr hi)]
  dsimp only
  congr 1
  rw [lookupT_eq]
  have hT := C.arena
  subst hT
  apply lookup_base_congr
  apply USize.toNat_inj.mp
  rw [tableBase_toNat, C.icFbBase_toNat]

theorem insertRow_bits24 {c : UInt64} (hc : c.toNat < 704) : (rowBits (insertRow c hc)).toNat ≤ 24 := by
  have h1 := (insertRow_fields hc).1
  have h2 := (cmdRow_small hc).1
  omega

/-- The insert-and-copy element read through its tree, with the bits for its code word and both lengths' extra bits at
hand and its insert length within the meta-block: as a move, the step machine's element and copy length, to the
command's literals. -/
theorem ic_move {α : Type} {w k : Nat} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
    {a : ByteArray} {stop : USize} {s : CommandState} {ic : BlockState} {st : Cmd} {pos : USize}
    {T : ByteArray} {lCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T lCur st.iCur dCur tb modeOff lRow iRow iFb dRow s0) (hH : HdrRel H m)
    (hrel : Rel w k m st (.insertCopy s ic)) (hp : pos.toNat ≤ stop.toNat) {v ib cb ibase cbase IL : UInt64}
    (hv : v = lookupT T (icFbBase C) st.word C.icIn C.lim C.size32) (hc : (wordSym v).toNat < 704)
    (hib : ib = rowBits (insertRow (wordSym v) hc)) (hcb : cb = rowBits (copyRow (wordSym v) hc))
    (hibase : ibase = rowBase (insertRow (wordSym v) hc)) (hcbase : cbase = rowBase (copyRow (wordSym v) hc))
    (hIL : IL = ibase + ((st.word >>> wordBits v) &&& maskT T C.big C.size32 ib))
    (hok : wordBits v + ib + cb ≤ st.count) (hrem : ¬ st.remaining < IL) :
    ∃ p', MoveOk w k m K a stop (.insertCopy s ic) st pos p'
      { st with
        word := ((st.word >>> wordBits v) >>> ib) >>> cb, count := st.count - wordBits v - ib - cb, left := IL
        ext := { st.ext with
          code := wordSym v, ilen := IL, copyBits := cb, copyBase := cbase
          clen := cbase + (((st.word >>> wordBits v) >>> ib) &&& maskT T C.big C.size32 cb) }
        tag := .literals, pos := pos, status := .next } := by
  have hrel0 := hrel
  have hl16 : (wordBits v).toNat < 16 := and15_lt v
  have hib24 : ib.toNat ≤ 24 := by rw [hib]; exact insertRow_bits24 hc
  have hcb24 : cb.toNat ≤ 24 := by rw [hcb]; exact copyRow_bits hc
  have hok' := UInt64.le_iff_toNat_le.mp hok
  rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at hok'
  have hc704 : wordSym v < 704 :=
    UInt64.lt_iff_toNat_lt.mpr (by rw [show (704 : UInt64).toNat = 704 from rfl]; exact hc)
  have h1 := stepInsertCopy_ok (K := K) (a := a) (stop := pos) hH hrel0 (Nat.le_refl _) (Or.inr rfl)
  rw [stepInsertCopy_fast C pos, ← hv] at h1
  have hl : wordBits v ≤ st.count := UInt64.le_iff_toNat_le.mpr (by omega)
  have hibc : rowBits (insertRow (wordSym v) (lt704 hc704)) ≤ ((BitBuffer.mk st.word st.count).drop (wordBits v)).count :=
    UInt64.le_iff_toNat_le.mpr (by
      rw [drop_count (UInt64.le_iff_toNat_le.mp hl)]
      show (rowBits (insertRow (wordSym v) _)).toNat ≤ st.count.toNat - (wordBits v).toNat
      rw [← hib]
      omega)
  have e1 : insertStep st pos v =
      { st with
        word := (st.word >>> wordBits v) >>> ib, count := st.count - wordBits v - ib
        ext := { st.ext with code := wordSym v, ilen := IL, copyBits := cb, copyBase := cbase }
        tag := .copyLength, pos := pos, status := .next } := by
    unfold insertStep
    rw [ite_eq_left hl, dite_eq_left hc704]
    dsimp only
    rw [ite_eq_left hibc, hIL, hib, hcb, hibase, hcbase, C.maskT_eq (by rw [← hib]; omega)]
    rfl
  rw [e1] at h1
  obtain ⟨p1, m1⟩ := h1.widen rfl rfl hp
  obtain ⟨_, _, _, _, _, _, rfl⟩ := m1.rel.copyLength_of rfl
  have h2 := stepCopyLength_ok (K := K) (a := a) (stop := pos) m1.rel (Nat.le_refl _) (Or.inr rfl)
  have hcbc : cb ≤ st.count - wordBits v - ib := UInt64.le_iff_toNat_le.mpr (by
    rw [u64_sub_le (by rw [u64_sub_le (by omega)]; omega), u64_sub_le (by omega)]
    omega)
  have e2 : stepCopyLength
      { st with
        word := (st.word >>> wordBits v) >>> ib, count := st.count - wordBits v - ib
        ext := { st.ext with code := wordSym v, ilen := IL, copyBits := cb, copyBase := cbase }
        tag := .copyLength, pos := pos, status := .next } pos =
      { st with
        word := ((st.word >>> wordBits v) >>> ib) >>> cb, count := st.count - wordBits v - ib - cb, left := IL
        ext := { st.ext with
          code := wordSym v, ilen := IL, copyBits := cb, copyBase := cbase
          clen := cbase + (((st.word >>> wordBits v) >>> ib) &&& maskT T C.big C.size32 cb) }
        tag := .literals, pos := pos, status := .next } := by
    unfold stepCopyLength
    rw [ite_eq_right hrem, ite_eq_left hcbc, C.maskT_eq (by omega)]
    rfl
  rw [e2] at h2
  obtain ⟨p2, m2⟩ := h2.widen rfl rfl hp
  exact ⟨p2, m1.trans m2⟩

/-! ### The fused insert-and-copy entry is the tree's read -/

theorem or_shl_toNat {a b s : UInt64} {k P : Nat} (hs : s.toNat = k) (hk : k < 64) (hP : 2 ^ k = P)
    (ha : a.toNat < P) (hb : P * b.toNat < 18446744073709551616) : (a ||| (b <<< s)).toNat = a.toNat + P * b.toNat := by
  subst hP
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hsh : (b <<< s).toNat = 2 ^ k * b.toNat := by
    rw [UInt64.toNat_shiftLeft, hs, Nat.mod_eq_of_lt hk, Nat.shiftLeft_eq, Nat.mul_comm]
    exact Nat.mod_eq_of_lt (by omega)
  rw [UInt64.toNat_or, hsh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- Bits `l` to `l + b` of the low byte are those of the whole number, for `l + b ≤ 8`. -/
theorem low_bits {w l b : Nat} (h : l + b ≤ 8) : w % 256 / 2 ^ l % 2 ^ b = w / 2 ^ l % 2 ^ b := by
  have e : 256 = 2 ^ l * 2 ^ (8 - l) := by rw [← Nat.pow_add, Nat.add_sub_cancel' (by omega)]
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem u64_shr_shr (x a b : UInt64) (h : a.toNat + b.toNat < 64) : (x >>> a) >>> b = x >>> (a + b) := by
  apply UInt64.toNat_inj.mp
  have hab : (a + b).toNat = a.toNat + b.toNat := u64_add_small (by omega)
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, hab,
    Nat.mod_eq_of_lt (by omega : b.toNat < 64), Nat.mod_eq_of_lt (by omega : a.toNat < 64), Nat.mod_eq_of_lt h,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    ← Nat.pow_add]

theorem u64_sub3 (x a b c : UInt64) : x - (a + b + c) = x - a - b - c := by
  have hy : x - a - b - c + c + b + a = x := by
    rw [UInt64.sub_add_cancel, UInt64.sub_add_cancel, UInt64.sub_add_cancel]
  have hr : x - a - b - c + c + b + a = x - a - b - c + (a + b + c) := by
    rw [UInt64.add_assoc, UInt64.add_assoc, UInt64.add_comm c (b + a), UInt64.add_comm b a]
  conv => lhs; rw [← hy, hr, UInt64.add_sub_cancel]

theorem shr_mask_toNat (x a b : UInt64) (ha : a.toNat < 64) (hb : b.toNat < 64) :
    ((x >>> a) &&& (((1 : UInt64) <<< b) - 1)).toNat = x.toNat / 2 ^ a.toNat % 2 ^ b.toNat := by
  have := BitBuffer.peek_toNat (BitBuffer.mk (x >>> a) 0) hb
  simp only [BitBuffer.peek] at this
  rw [this, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow]

/-- An entry that isn't 255 in its low byte is the fused entry of a root slot holding a code word of at most 8 bits and
a symbol below 704. -/
theorem icEntryU_fused {v j : UInt64} (h : icEntryU v j &&& 255 ≠ 255) :
    ∃ (_ : v &&& 15 ≤ 8) (hs : ((v >>> 4) &&& 4095).toNat < 704),
      icEntryU v j = icEntryOf (v &&& 15) ((v >>> 4) &&& 4095) j hs := by
  unfold icEntryU at h ⊢
  split
  · rename_i hc
    exact ⟨hc.1, lt704 hc.2, rfl⟩
  · rename_i hc
    rw [dite_eq_right hc] at h
    exact absurd (by decide) h

/-- The fields of a fused entry: the symbol, and either the bits taken with both lengths, or the code word's bits, both
extra bits and both lengths' lowest values. -/
theorem icEntryOf_split {l sym j : UInt64} (hs : sym.toNat < 704) (hl : l.toNat ≤ 8) (hj : j.toNat < 256) :
    (icEntryOf l sym j hs >>> 8) &&& 1023 = sym ∧
    (l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ≤ 8 →
      icEntryOf l sym j hs &&& 15 = l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ∧
      (icEntryOf l sym j hs >>> 18) &&& 63 = 0 ∧ (icEntryOf l sym j hs >>> 24) &&& 63 = 0 ∧
      (icEntryOf l sym j hs >>> 32) &&& 0xFFFF =
        rowBase (insertRow sym hs) + ((j >>> l) &&& (((1 : UInt64) <<< rowBits (insertRow sym hs)) - 1)) ∧
      icEntryOf l sym j hs >>> 48 = rowBase (copyRow sym hs) +
        ((j >>> (l + rowBits (insertRow sym hs))) &&& (((1 : UInt64) <<< rowBits (copyRow sym hs)) - 1))) ∧
    (¬ l + rowBits (insertRow sym hs) + rowBits (copyRow sym hs) ≤ 8 →
      icEntryOf l sym j hs &&& 15 = l ∧ (icEntryOf l sym j hs >>> 18) &&& 63 = rowBits (insertRow sym hs) ∧
      (icEntryOf l sym j hs >>> 24) &&& 63 = rowBits (copyRow sym hs) ∧
      (icEntryOf l sym j hs >>> 32) &&& 0xFFFF = rowBase (insertRow sym hs) ∧
      icEntryOf l sym j hs >>> 48 = rowBase (copyRow sym hs)) := by
  have hib : (rowBits (insertRow sym hs)).toNat ≤ 24 := insertRow_bits24 hs
  have hcb : (rowBits (copyRow sym hs)).toNat ≤ 24 := copyRow_bits hs
  have hibase : (rowBase (insertRow sym hs)).toNat ≤ 22594 := by
    rw [(insertRow_fields hs).2]; exact (cmdRow_small hs).2.1
  have hcbase : (rowBase (copyRow sym hs)).toNat ≤ 2118 := by
    rw [(copyRow_fields hs).2]; exact (cmdRow_small hs).2.2.2
  unfold icEntryOf
  dsimp only
  generalize rowBits (insertRow sym hs) = ib at *
  generalize rowBits (copyRow sym hs) = cb at *
  generalize rowBase (insertRow sym hs) = ibase at *
  generalize rowBase (copyRow sym hs) = cbase at *
  have f8 : ∀ e : UInt64, ((e >>> 8) &&& 1023).toNat = e.toNat / 256 % 1024 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 8 &&& (2 ^ 10 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f18 : ∀ e : UInt64, ((e >>> 18) &&& 63).toNat = e.toNat / 262144 % 64 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 18 &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f24 : ∀ e : UInt64, ((e >>> 24) &&& 63).toNat = e.toNat / 16777216 % 64 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 24 &&& (2 ^ 6 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f32 : ∀ e : UInt64, ((e >>> 32) &&& 0xFFFF).toNat = e.toNat / 4294967296 % 65536 := fun e => by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
    show e.toNat >>> 32 &&& (2 ^ 16 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have f48 : ∀ e : UInt64, (e >>> 48).toNat = e.toNat / 281474976710656 := fun e => by
    rw [UInt64.toNat_shiftRight]
    show e.toNat >>> 48 = _
    rw [Nat.shiftRight_eq_div_pow]
  have f15 : ∀ e : UInt64, (e &&& 15).toNat = e.toNat % 16 := fun e => by
    rw [UInt64.toNat_and]
    show e.toNat &&& (2 ^ 4 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  by_cases hr : l + ib + cb ≤ 8
  · rw [ite_eq_left hr]
    have hA : (l + ib + cb).toNat = l.toNat + ib.toNat + cb.toNat := by
      rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)]
    have hr' : (l + ib + cb).toNat ≤ 8 := UInt64.le_iff_toNat_le.mp hr
    rw [hA] at hr'
    have hb1 : ((j >>> l) &&& (((1 : UInt64) <<< ib) - 1)).toNat < 256 := by
      rw [UInt64.toNat_and]
      refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj
    have hb2 : ((j >>> (l + ib)) &&& (((1 : UInt64) <<< cb) - 1)).toNat < 256 := by
      rw [UInt64.toNat_and]
      refine Nat.lt_of_le_of_lt Nat.and_le_left ?_
      rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hj
    generalize (j >>> l) &&& (((1 : UInt64) <<< ib) - 1) = M1 at *
    generalize (j >>> (l + ib)) &&& (((1 : UInt64) <<< cb) - 1) = M2 at *
    have hX : (ibase + M1).toNat = ibase.toNat + M1.toNat := u64_add_small (by omega)
    have hY : (cbase + M2).toNat = cbase.toNat + M2.toNat := u64_add_small (by omega)
    have e1 := or_shl_toNat (a := l + ib + cb) (b := sym) (s := 8) (P := 256) rfl (by decide) rfl (by omega)
      (by omega)
    have e2 := or_shl_toNat (a := (l + ib + cb) ||| (sym <<< 8)) (b := ibase + M1) (s := 32) (P := 4294967296) rfl
      (by decide) rfl (by rw [e1]; omega) (by omega)
    have e3 := or_shl_toNat (a := (l + ib + cb) ||| (sym <<< 8) ||| ((ibase + M1) <<< 32)) (b := cbase + M2) (s := 48)
      (P := 281474976710656) rfl (by decide) rfl (by rw [e2, e1]; omega) (by omega)
    rw [e2, e1, hA, hX, hY] at e3
    refine ⟨UInt64.toNat_inj.mp (by rw [f8, e3]; omega), fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩,
      fun h => absurd hr h⟩
    · exact UInt64.toNat_inj.mp (by rw [f15, e3]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f18, e3, h0]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f24, e3, h0]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f32, e3]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f48, e3]; omega)
  · rw [ite_eq_right hr]
    have e1 := or_shl_toNat (a := l) (b := sym) (s := 8) (P := 256) rfl (by decide) rfl (by omega) (by omega)
    have e2 := or_shl_toNat (a := l ||| (sym <<< 8)) (b := ib) (s := 18) (P := 262144) rfl (by decide) rfl
      (by rw [e1]; omega) (by omega)
    have e3 := or_shl_toNat (a := l ||| (sym <<< 8) ||| (ib <<< 18)) (b := cb) (s := 24) (P := 16777216) rfl
      (by decide) rfl (by rw [e2, e1]; omega) (by omega)
    have e4 := or_shl_toNat (a := l ||| (sym <<< 8) ||| (ib <<< 18) ||| (cb <<< 24)) (b := ibase) (s := 32)
      (P := 4294967296) rfl (by decide) rfl (by rw [e3, e2, e1]; omega) (by omega)
    have e5 := or_shl_toNat (a := l ||| (sym <<< 8) ||| (ib <<< 18) ||| (cb <<< 24) ||| (ibase <<< 32)) (b := cbase)
      (s := 48) (P := 281474976710656) rfl (by decide) rfl (by rw [e4, e3, e2, e1]; omega) (by omega)
    rw [e4, e3, e2, e1] at e5
    refine ⟨UInt64.toNat_inj.mp (by rw [f8, e5]; omega), fun h => absurd h hr, fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · exact UInt64.toNat_inj.mp (by rw [f15, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f18, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f24, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f32, e5]; omega)
    · exact UInt64.toNat_inj.mp (by rw [f48, e5]; omega)

/-- A code word of at most 8 bits is read from its root slot alone. -/
theorem lookupT_short {t : ByteArray} {base : USize} {w : UInt64} {lim : Nat} (hin : TableIn t base.toNat lim)
    (hl : lim + 6 ≤ t.size) (h32 : t.size < 2 ^ 32)
    (h8 : UInt64.ofNat (slotNum t (base.toNat + w.toNat % 256)) &&& 15 ≤ 8) :
    lookupT t base w hin hl h32 = UInt64.ofNat (slotNum t (base.toNat + w.toNat % 256)) := by
  have hroot := lookupT_root hin hl h32 w
  have e1 := (load64_slot hroot.1 hroot.2 h32).trans (by rw [rootIndex_toNat w (hin.fits (by omega)) h32])
  unfold lookupT
  simp only [e1]
  rw [dite_eq_left h8]

section
variable {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}

/-- The fused entry the loop loads is the block type's entry for the next 8 bits. -/
theorem FCtx.row64_eq (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (w : UInt64) :
    row64 T iRow C.iRowLe C.size32 w =
      icEntryU (UInt64.ofNat (slotNum T (u32At H.icBase iCur.toNat + w.toNat % 256))) (UInt64.ofNat (w.toNat % 256)) := by
  have h32 := C.size32
  have hle := C.iRowLe
  have hj : w.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have h255 : (w &&& 255).toNat = w.toNat % 256 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod w.toNat 8
  have e := C.tab.ic _ C.hi _ hj
  apply UInt64.toNat_inj.mp
  unfold row64
  rw [load64_toNat, fastAdd (by rw [u64_shl (by decide) (by rw [h255]; omega)]; rw [h255]; omega),
    u64_shl (by decide) (by rw [h255]; omega), h255, C.iRow,
    show w.toNat % 256 * 2 ^ 3 = 8 * (w.toNat % 256) by rw [Nat.mul_comm], e]

/-- The fast loop's insert-and-copy read through the tree, for any code word: `icK`'s second branch. -/
@[inline] def icFb {α : Type} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (word count : UInt64)
    (hw : (BitBuffer.mk word count).Wf)
    (k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α) : α :=
  let v := lookupT T (icFbBase C) word C.icIn C.lim C.size32
  let l := v &&& 15
  let code := wordSym v
  have hc : code.toNat < 704 := C.icSym word
  let row := insertRow code hc
  let cr := copyRow code hc
  let ib := rowBits row
  let cb := rowBits cr
  let w1 := word >>> l
  let ilen := rowBase row + (w1 &&& maskT T C.big C.size32 ib)
  let w2 := w1 >>> ib
  let clen := rowBase cr + (w2 &&& maskT T C.big C.size32 cb)
  have hl : l.toNat < 16 := and15_lt v
  have hib : ib.toNat < 64 := insertRow_bits hc
  have hcb : cb.toNat ≤ 24 := copyRow_bits hc
  k (decide (l + ib + cb ≤ count)) (w2 >>> cb) (count - l - ib - cb) code ilen clen
    (fun h => by
      have h1 := UInt64.le_iff_toNat_le.mp (of_decide_eq_true h)
      rw [u64_add_small (by rw [u64_add_small (by omega)]; omega), u64_add_small (by omega)] at h1
      exact drop3_wf hw (by omega) (by omega) (by omega) h1)

end

theorem k_congr {α : Type} {P : UInt64 → UInt64 → Prop}
    (k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → P w c) → α) {ok ok' : Bool}
    {w w' c c' code code' il il' cl cl' : UInt64} {h : ok = true → P w c} {h' : ok' = true → P w' c'}
    (e1 : ok = ok') (e2 : w = w') (e3 : c = c') (e4 : code = code') (e5 : il = il') (e6 : cl = cl') :
    k ok w c code il cl h = k ok' w' c' code' il' cl' h' := by
  subst e1 e2 e3 e4 e5 e6
  rfl

theorem insertRow_congr {c c' : UInt64} {h : c.toNat < 704} {h' : c'.toNat < 704} (e : c = c') :
    insertRow c h = insertRow c' h' := by
  subst e
  rfl

theorem copyRow_congr {c c' : UInt64} {h : c.toNat < 704} {h' : c'.toNat < 704} (e : c = c') :
    copyRow c h = copyRow c' h' := by
  subst e
  rfl

/-- The fused entries give what the tree gives: `icK` is its read through the tree. -/
theorem icK_fb {H : Hdr} {T : ByteArray} {lCur iCur dCur tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    {α : Type} (C : FCtx H T lCur iCur dCur tb modeOff lRow iRow iFb dRow s0) (word count : UInt64)
    (hw : (BitBuffer.mk word count).Wf)
    (k : (ok : Bool) → (w c code ilen clen : UInt64) → (ok = true → (BitBuffer.mk w c).Wf) → α) :
    icK C word count hw k = icFb C word count hw k := by
  unfold icK icFb
  dsimp only
  split
  · rfl
  · rename_i hne
    have hE := C.row64_eq word
    rw [hE] at hne
    obtain ⟨hl8, hs, hEo⟩ := icEntryU_fused hne
    generalize hv0 : UInt64.ofNat (slotNum T (u32At H.icBase iCur.toNat + word.toNat % 256)) = v0 at hE hl8 hs hEo
    have hv : lookupT T (icFbBase C) word C.icIn C.lim C.size32 = v0 := by
      have := lookupT_short C.icIn C.lim C.size32 (w := word) (by rw [C.icFbBase_toNat, hv0]; exact hl8)
      rw [C.icFbBase_toNat, hv0] at this
      exact this
    have hl : (v0 &&& 15).toNat ≤ 8 := UInt64.le_iff_toNat_le.mp hl8
    have hw256 : word.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
    have hjv : (UInt64.ofNat (word.toNat % 256)).toNat = word.toNat % 256 := by
      rw [UInt64.toNat_ofNat']
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨hsym, hres, hunres⟩ := icEntryOf_split hs hl (by rw [hjv]; exact hw256)
    have hib : (rowBits (insertRow ((v0 >>> 4) &&& 4095) hs)).toNat ≤ 24 := insertRow_bits24 hs
    have hcb : (rowBits (copyRow ((v0 >>> 4) &&& 4095) hs)).toNat ≤ 24 := copyRow_bits hs
    have h0 : ((1 : UInt64) <<< 0) - 1 = 0 := by decide
    by_cases hr : (v0 &&& (15 : UInt64)) + rowBits (insertRow ((v0 >>> 4) &&& 4095) hs) +
        rowBits (copyRow ((v0 >>> 4) &&& 4095) hs) ≤ 8
    · obtain ⟨f1, f2, f3, f4, f5⟩ := hres hr
      have hli : ((v0 &&& (15 : UInt64)) + rowBits (insertRow ((v0 >>> 4) &&& 4095) hs)).toNat =
          (v0 &&& (15 : UInt64)).toNat + (rowBits (insertRow ((v0 >>> 4) &&& 4095) hs)).toNat :=
        u64_add_small (by omega)
      have hr' : ((v0 &&& (15 : UInt64)) + rowBits (insertRow ((v0 >>> 4) &&& 4095) hs) +
          rowBits (copyRow ((v0 >>> 4) &&& 4095) hs)).toNat ≤ 8 := UInt64.le_iff_toNat_le.mp hr
      rw [u64_add_small (by rw [hli]; omega), hli] at hr'
      apply k_congr (P := fun w c => (BitBuffer.mk w c).Wf)
      · simp only [hE, hEo, hv, f1, f2, f3, UInt64.add_zero, wordSym]
      · simp only [hE, hEo, hv, f1, f2, f3, u64_shr_zero, wordSym]
        rw [u64_shr_shr word _ _ (by omega), u64_shr_shr word _ _ (by rw [hli]; omega)]
      · simp only [hE, hEo, hv, f1, f2, f3, UInt64.sub_zero, wordSym]
        rw [u64_sub3]
      · simp only [hE, hEo, hv, hsym, wordSym]
      · simp only [hE, hEo, hv, f1, f2, f4, wordSym]
        rw [C.maskT_eq (n := 0) (by decide), C.maskT_eq (by omega), h0, UInt64.and_zero, UInt64.add_zero]
        congr 1
        apply UInt64.toNat_inj.mp
        rw [shr_mask_toNat _ _ _ (by omega) (by omega), shr_mask_toNat _ _ _ (by omega) (by omega), hjv]
        exact low_bits (by omega)
      · simp only [hE, hEo, hv, f1, f2, f3, f5, wordSym]
        rw [C.maskT_eq (n := 0) (by decide), C.maskT_eq (by omega), h0, UInt64.and_zero, UInt64.add_zero,
          u64_shr_shr word _ _ (by omega)]
        congr 1
        apply UInt64.toNat_inj.mp
        rw [shr_mask_toNat _ _ _ (by rw [hli]; omega) (by omega), shr_mask_toNat _ _ _ (by rw [hli]; omega) (by omega),
          hjv]
        exact low_bits (by rw [hli]; omega)
    · obtain ⟨f1, f2, f3, f4, f5⟩ := hunres hr
      apply k_congr (P := fun w c => (BitBuffer.mk w c).Wf)
      all_goals simp only [hE, hEo, hv, hsym, f1, f2, f3, f4, f5, wordSym]

/-! ### The records of a command's round -/

/-- A copy's distance taken as it is (an implied 0 or a code 0): the copy, the last distances unchanged. -/
theorem applyDistance_zero {st : Cmd} {pos : USize} {d : UInt64} (hw : ¬ st.written.toUInt64 < d)
    (hrc : ¬ st.remaining < st.clen) :
    applyDistance st pos 0 d =
      { st with
        remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
        ext := { st.ext with dist := d } } := by
  unfold applyDistance
  rw [ite_eq_right hw, ite_eq_right hrc, ite_eq_left rfl]

/-- A copy's distance from any other code: the copy, the distance pushed onto the last distances. -/
theorem applyDistance_push {st : Cmd} {pos : USize} {dcode d : UInt64} (hw : ¬ st.written.toUInt64 < d)
    (hrc : ¬ st.remaining < st.clen) (h0 : dcode ≠ 0) :
    applyDistance st pos dcode d =
      { st with
        remaining := st.remaining - st.clen, left := st.clen, tag := .copy, pos := pos, status := .next
        ext := { st.ext with dist := d, d0 := d, d1 := st.d0, d2 := st.d1, d3 := st.d2 } } := by
  unfold applyDistance
  rw [ite_eq_right hw, ite_eq_right hrc, ite_eq_right h0]

/-- The bytes written, capped, after `n` more: the cap of the uncapped count plus `n`. -/
theorem usmin_add {c x n : USize} (hx : x.toNat + n.toNat < 2 ^ 32) :
    usmin c (usmin c x + n) = usmin c (x + n) := by
  apply USize.toNat_inj.mp
  have hm : (usmin c x).toNat + n.toNat < 2 ^ 32 := by rw [usmin_toNat]; omega
  rw [usmin_toNat, usmin_toNat, fastAdd hm, fastAdd hx, usmin_toNat]
  omega

/-- What remains from `n` more bytes on. -/
theorem rem_add {r : UInt64} {x n : USize} (hx : x.toNat + n.toNat < 2 ^ 32) (hr : x.toNat + n.toNat ≤ r.toNat) :
    r - (x + n).toUInt64 = r - x.toUInt64 - n.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have e1 : (x + n).toUInt64.toNat = x.toNat + n.toNat := by rw [USize.toNat_toUInt64, fastAdd hx]
  have e2 : x.toUInt64.toNat = x.toNat := USize.toNat_toUInt64 x
  have e3 : n.toUInt64.toNat = n.toNat := USize.toNat_toUInt64 n
  have e4 : (r - x.toUInt64).toNat = r.toNat - x.toNat := by rw [u64_sub_le (by rw [e2]; omega), e2]
  rw [u64_sub_le (by rw [e1]; exact hr), e1, u64_sub_le (by rw [e4, e3]; omega), e4, e3]
  omega

/-- Two 32-bit halves packed in one word: the low half `a`, the high half the low 32 bits of `b`. -/
theorem or_shl32 {a b : UInt64} (ha : a.toNat < 2 ^ 32) :
    ((a ||| (b <<< 32)) &&& 0xFFFFFFFF) = a ∧ (a ||| (b <<< 32)) >>> 32 = b &&& 0xFFFFFFFF := by
  have hsh : (b <<< 32).toNat = 2 ^ 32 * (b.toNat % 2 ^ 32) := by
    rw [UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftLeft_eq, Nat.mul_comm,
      show (2 : Nat) ^ 64 = 2 ^ 32 * 2 ^ 32 from rfl, Nat.mul_mod_mul_left]
  have hv : (a ||| (b <<< 32)).toNat = a.toNat + 2 ^ 32 * (b.toNat % 2 ^ 32) := by
    rw [UInt64.toNat_or, hsh, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]
  constructor
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, hv, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.reducePow] at ha ⊢
    omega
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hv, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow,
      UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.reducePow] at ha ⊢
    omega

theorem shr32_lt (x : UInt64) : (x >>> 32).toNat < 2 ^ 32 := by
  rw [UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
  have := x.toNat_lt
  simp only [Nat.reducePow] at this ⊢
  omega

section
variable {w k : Nat} {m : MetaBlockHeader} {st : Cmd}

/-- The copy's fields (`copyBits`, `copyBase`, `dist`) don't matter to the places among a command's literals, at its
distance or at a command's start, as long as the copy base stays at least 1. -/
theorem Rel.literals_ext {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState}
    {out : List Nat} (h : Rel w k m st (.literals s ic c ilen clen n lit out)) {cbits cb d : UInt64}
    (hcb : 1 ≤ cb.toNat) :
    Rel w k m { st with ext := { st.ext with copyBits := cbits, copyBase := cb, dist := d } }
      (.literals s ic c ilen clen n lit out) := by
  obtain ⟨hC, hr⟩ := h
  exact ⟨{ hC with cbase1 := hcb }, hr⟩

theorem Rel.distance_ext {s : CommandState} {c clen : Nat} (h : Rel w k m st (.distance s c clen))
    {cbits cb d : UInt64} (hcb : 1 ≤ cb.toNat) :
    Rel w k m { st with ext := { st.ext with copyBits := cbits, copyBase := cb, dist := d } } (.distance s c clen) := by
  obtain ⟨hC, hr⟩ := h
  exact ⟨{ hC with cbase1 := hcb }, hr⟩

theorem Rel.command_ext {s : CommandState} (h : Rel w k m st (.command s)) {cbits cb d : UInt64} (hcb : 1 ≤ cb.toNat) :
    Rel w k m { st with ext := { st.ext with copyBits := cbits, copyBase := cb, dist := d } } (.command s) := by
  obtain ⟨hC, hr⟩ := h
  exact ⟨{ hC with cbase1 := hcb }, hr⟩

end

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
    (ha : 1 ≤ ahead) (hL : 1 ≤ L.toNat) (hLC : 1 ≤ LC.toNat) {word' count' : UInt64} {pos' : USize} {thr : Nat}
    (hf : FillOk a stop word count pos thr word' count' pos') (hbits : litT C p1 p2 word' &&& 15 ≤ count')
    (hs : stop.toNat ≤ a.size) (hsz : ring.size = 2 ^ k.toNat) :
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
      rw [← he]
      exact hbits) hsz hwp
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

/-! ### Two literals -/

/-- A refill that finds the bits at hand enough takes nothing. -/
theorem FillOk.self {a : ByteArray} {stop : USize} {word count : UInt64} {pos : USize} {thr : Nat}
    (hw : (BitBuffer.mk word count).Wf) (ht : thr ≤ count.toNat) (hp : pos.toNat ≤ stop.toNat) :
    FillOk a stop word count pos thr word count pos :=
  ⟨hw, ht, Nat.le_refl _, hp, rfl, rfl⟩

/-- The loop's numbers one byte on. -/
theorem FNum.succ {opos pB wB : USize} {rEnd bEnd : UInt64} {k ahead : Nat} (N : FNum opos pB wB rEnd bEnd k ahead)
    (hk : k ≤ 24) (ha : 1 ≤ ahead) : FNum (opos + USize.ofNat 1) pB wB rEnd bEnd k (ahead - 1) := by
  have hR : 2 ^ k ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk
  have h1 := N.ahead
  have h2 := N.small
  have h3 := N.pend
  have h4 := N.wr
  have e1 : (opos + USize.ofNat 1).toNat = opos.toNat + 1 := fastIdx_add (by omega)
  have e2 : (opos + USize.ofNat 1 + pB).toNat = (opos + pB).toNat + 1 := by
    rw [← usize_add_one_comm, fastIdx_add (by omega)]
  have e3 : (opos + USize.ofNat 1 + wB).toNat = (opos + wB).toNat + 1 := by
    rw [← usize_add_one_comm, fastIdx_add (by omega)]
  exact ⟨by rw [e1]; omega, N.bEndLe, h2, by rw [e2, e1]; omega, by rw [e3, e1]; omega⟩

theorem u64_sub2 (x a b : UInt64) : x - (a + b) = x - a - b := by
  have hy : x - a - b + b + a = x := by rw [UInt64.sub_add_cancel, UInt64.sub_add_cancel]
  have hr : x - a - b + b + a = x - a - b + (a + b) := by rw [UInt64.add_assoc, UInt64.add_comm b a]
  conv => lhs; rw [← hy, hr, UInt64.add_sub_cancel]

theorem usize_add_two (x : USize) : x + USize.ofNat 1 + USize.ofNat 1 = x + USize.ofNat 2 := by
  rw [USize.add_assoc]
  congr 1
  exact USize.toNat_inj.mp (by rw [fastIdx_add (by rw [fastLit (by decide)]; decide), fastLit (by decide),
    fastLit (by decide)])

/-- Two literals of the fast loop after one refill to 30 bits: the first read at the context's tree, the second at the
tree for the context it makes. -/
theorem lit2_round {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader}
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
    (ha : 2 ≤ ahead) (hL : 2 ≤ L.toNat) (hLC : 2 ≤ LC.toNat) {word' count' : UInt64} {pos' : USize}
    (hf : FillOk a stop word count pos 30 word' count' pos') (hs : stop.toNat ≤ a.size)
    (hsz : ring.size = 2 ^ k.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.literals s ic c ilen clen n lit out)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen' clen' p1 p2
        .literals L pos) pos p'
      (fexit ((word' >>> (litT C p1 p2 word' &&& 15)) >>>
          (litT C (litT C p1 p2 word' >>> 4).toUInt8 p1 (word' >>> (litT C p1 p2 word' &&& 15)) &&& 15))
        (count' - (litT C p1 p2 word' &&& (15 : UInt64)) -
          (litT C (litT C p1 p2 word' >>> 4).toUInt8 p1 (word' >>> (litT C p1 p2 word' &&& 15)) &&& (15 : UInt64)))
        (wput (wput ring opos mask hk hmN hsz (litT C p1 p2 word' >>> 4).toUInt8) (opos + USize.ofNat 1) mask hk hmN
          (wput_size _ _ _ hk hmN hsz _)
          (litT C (litT C p1 p2 word' >>> 4).toUInt8 p1 (word' >>> (litT C p1 p2 word' &&& 15)) >>> 4).toUInt8)
        (opos + USize.ofNat 2) mask pB cap cap16 wB rEnd iCount (LC - 2) dCount flags x d01 d23 code ilen' clen'
        (litT C (litT C p1 p2 word' >>> 4).toUInt8 p1 (word' >>> (litT C p1 p2 word' &&& 15)) >>> 4).toUInt8
        (litT C p1 p2 word' >>> 4).toUInt8 .literals (L - 2) pos') := by
  have hl1 := and15_lt (litT C p1 p2 word')
  have hc30 := hf.enough
  obtain ⟨p', m1⟩ := lit_round (K := K) C hH hrel hk h16 hmk hmN hcap N (by omega) (by omega) (by omega) hf
    (UInt64.le_iff_toNat_le.mpr (by omega)) hs hsz
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := m1.rel.literals_of rfl
  have e1 : (count' - (litT C p1 p2 word' &&& (15 : UInt64))).toNat =
      count'.toNat - (litT C p1 p2 word' &&& (15 : UInt64)).toNat := u64_sub_le (by omega)
  have h1 : (1 : UInt64).toNat = 1 := rfl
  obtain ⟨p'', m2⟩ := lit_round (K := K) (stop := stop) C hH m1.rel hk h16 hmk hmN hcap (N.succ hk (by omega))
    (by omega) (by rw [u64_sub_le (by rw [h1]; omega), h1]; omega) (by rw [u64_sub_le (by rw [h1]; omega), h1]; omega)
    (FillOk.self (thr := 0) (drop1_wf hf.wf (by omega) (by omega)) (Nat.zero_le _) hf.posStop)
    (UInt64.le_iff_toNat_le.mpr (by rw [e1]; have := and15_lt (litT C (litT C p1 p2 word' >>> 4).toUInt8 p1
      (word' >>> (litT C p1 p2 word' &&& 15))); omega)) hs (wput_size _ _ _ hk hmN hsz _)
  refine ⟨p'', ?_⟩
  have e2 : LC - 1 - 1 = LC - 2 := by rw [← u64_sub2]; rfl
  have e3 : L - 1 - 1 = L - 2 := by rw [← u64_sub2]; rfl
  have m := m1.trans m2
  rw [usize_add_two, e2, e3] at m
  exact m

/-! ### A command's distance -/

/-- The state at a command's copy, in the loop's terms: what remains less the copy, and the copy's length and distance.
-/
@[inline] def fcopy (word count : UInt64) (ring : ByteArray) (opos mask pB cap cap16 wB : USize) (rEnd : UInt64)
    (iCount lCount dCount : UInt64) (flags : Flags) (x : CmdExt) (d01 d23 code ilen clen : UInt64) (p1 p2 : UInt8)
    (d : UInt64) (pos : USize) : Cmd :=
  ⟨word, count, ring, opos &&& mask, opos + pB, cap, usmin cap16 (opos + wB), p1, p2, rEnd - opos.toUInt64 - clen,
    iCount, lCount, dCount, flags,
    ⟨x.iCur, x.iPrev, x.lCur, x.lPrev, x.dCur, x.dPrev, d01 &&& 0xFFFFFFFF, d01 >>> 32, d23 &&& 0xFFFFFFFF, d23 >>> 32,
      code, ilen, clen, x.copyBits, x.copyBase, d, x.wordBuf, x.wordPos⟩,
    .copy, clen, pos, .next⟩

/-- With the copy within the meta-block, something remains, and at least the copy. -/
theorem rem_facts {rEnd clen : UInt64} {opos : USize} (h : opos.toNat + clen.toNat ≤ rEnd.toNat)
    (h1 : 1 ≤ clen.toNat) : rEnd - opos.toUInt64 ≠ 0 ∧ ¬ rEnd - opos.toUInt64 < clen := by
  have e : (rEnd - opos.toUInt64).toNat = rEnd.toNat - opos.toNat := by
    rw [u64_sub_le (by rw [USize.toNat_toUInt64]; omega), USize.toNat_toUInt64]
  refine ⟨fun h0 => ?_, fun hl => ?_⟩
  · have h0' := congrArg UInt64.toNat h0
    rw [e] at h0'
    have : (0 : UInt64).toNat = 0 := rfl
    omega
  · have := UInt64.lt_iff_toNat_lt.mp hl
    rw [e] at this
    omega

section
variable {α : Type} {w : Nat} {k : USize} {H : Hdr} {m : MetaBlockHeader} {K : CommandState → List Bool → Option α}
  {a : ByteArray} {stop : USize} {s : CommandState} {c cl : Nat} {word count : UInt64} {ring : ByteArray}
  {opos mask pB cap cap16 wB : USize} {rEnd : UInt64} {iCount LC dCount : UInt64} {flags : Flags} {x : CmdExt}
  {d01 d23 code ilen clen : UInt64} {p1 p2 : UInt8} {pos : USize}

/-- A distance implied 0 (the last distance): from the distance, a refill to 40 bits, then the copy. -/
theorem dImpl_move (hH : HdrRel H m)
    (hrel : Rel w k.toNat m (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen clen p1 p2 .distance 0 pos) (.distance s c cl))
    {word1 count1 : UInt64} {pos1 : USize} (hf : FillOk a stop word count pos 40 word1 count1 pos1)
    (hrem : opos.toNat + clen.toNat ≤ rEnd.toNat) (hc : code < 128) (hd0 : d01 &&& 0xFFFFFFFF ≠ 0)
    (hw : ¬ (usmin cap16 (opos + wB)).toUInt64 < d01 &&& 0xFFFFFFFF) :
    ∃ p', MoveOk w k.toNat m K a stop (.distance s c cl)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2
        .distance 0 pos) pos p'
      (fcopy word1 count1 ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2
        (d01 &&& 0xFFFFFFFF) pos1) := by
  have m1 := fill_move (K := K) hrel hf
  have hcl : 1 ≤ clen.toNat := hrel.1.clen1
  obtain ⟨hr0, hrc⟩ := rem_facts hrem hcl
  obtain ⟨p', m2⟩ := distImplicit_move (K := K) (a := a) (stop := stop) (pos := pos1) hH m1.rel hr0 hc hd0 hw hrc
    hf.posStop
  exact ⟨p', m1.trans m2⟩

/-- `applyDistance` after a distance's symbol, as the state at the copy: the last distances as the loop packs them,
the distance pushed or not. -/
theorem applyDistance_fcopy {word1 count1 w' c' dcode d n01 n23 : UInt64} {pos1 : USize}
    (hw : ¬ (usmin cap16 (opos + wB)).toUInt64 < d) (hrc : ¬ rEnd - opos.toUInt64 < clen) (hd : d.toNat < 2 ^ 32)
    (hn : (dcode = 0 ∧ n01 = d01 ∧ n23 = d23) ∨
      (dcode ≠ 0 ∧ n01 = d ||| (d01 <<< 32) ∧ n23 = (d01 >>> 32) ||| (d23 <<< 32))) :
    applyDistance (setBits { { fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
        ilen clen p1 p2 .distance 0 pos with word := word1, count := count1, pos := pos1 } with
        dCount := dCount - 1, tag := .distanceSymbol, pos := pos1, status := .next } w' c') pos1 dcode d =
      fcopy w' c' ring opos mask pB cap cap16 wB rEnd iCount LC (dCount - 1) flags x n01 n23 code ilen clen p1 p2 d
        pos1 := by
  rcases hn with ⟨h0, rfl, rfl⟩ | ⟨h0, rfl, rfl⟩
  · rw [h0, applyDistance_zero hw hrc]
    rfl
  · rw [applyDistance_push hw hrc h0]
    obtain ⟨e1, e2⟩ := or_shl32 (b := d01) hd
    obtain ⟨e3, e4⟩ := or_shl32 (a := d01 >>> 32) (b := d23) (shr32_lt d01)
    simp only [fcopy, e1, e2, e3, e4]
    rfl

/-- A distance the copy reads is below `2 ^ 32`: it is at most the bytes written. -/
theorem dist_small {st : Cmd} {out : List Nat} {rem : Nat} {ds : Distances} {ic lit dist : BlockState} {d : UInt64}
    (hC : Core w k.toNat m st out rem ds ic lit dist) (hw : ¬ st.written.toUInt64 < d) : d.toNat < 2 ^ 32 := by
  have h1 := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp hw)
  rw [USize.toNat_toUInt64] at h1
  have h2 := hC.written
  have h3 := hC.win
  have h4 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hC.k24
  have : min w out.length ≤ w := Nat.min_le_left _ _
  omega

/-- A distance's short code (one of the last distances, adjusted): from the distance, a refill to 40 bits, the block
count, the symbol, then the copy. -/
theorem dShort_move {T : ByteArray} {tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen clen p1 p2 .distance 0 pos) (.distance s c cl))
    {word1 count1 : UInt64} {pos1 : USize} (hf : FillOk a stop word count pos 40 word1 count1 pos1)
    (hrem : opos.toNat + clen.toNat ≤ rEnd.toNat) (hc : ¬ code < 128) (hdc : dCount ≠ 0) {v n01 n23 : UInt64}
    (hv : v = lookupT T (dRowBase C clen) word1 (C.dIn clen) C.lim C.size32) (hl : wordBits v ≤ count1)
    (h16 : wordSym v < 16)
    (hd0 : shortFast (d01 &&& 0xFFFFFFFF) (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) (wordSym v) ≠ 0)
    (hw : ¬ (usmin cap16 (opos + wB)).toUInt64 <
      shortFast (d01 &&& 0xFFFFFFFF) (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) (wordSym v))
    (hn : (wordSym v = 0 ∧ n01 = d01 ∧ n23 = d23) ∨ (wordSym v ≠ 0 ∧
      n01 = shortFast (d01 &&& 0xFFFFFFFF) (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) (wordSym v) ||| (d01 <<< 32) ∧
      n23 = (d01 >>> 32) ||| (d23 <<< 32))) :
    ∃ p', MoveOk w k.toNat m K a stop (.distance s c cl)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2
        .distance 0 pos) pos p'
      (fcopy (word1 >>> wordBits v) (count1 - wordBits v) ring opos mask pB cap cap16 wB rEnd iCount LC (dCount - 1)
        flags x n01 n23 code ilen clen p1 p2
        (shortFast (d01 &&& 0xFFFFFFFF) (d01 >>> 32) (d23 &&& 0xFFFFFFFF) (d23 >>> 32) (wordSym v)) pos1) := by
  have m1 := fill_move (K := K) hrel hf
  have hC := hrel.1
  obtain ⟨hr0, hrc⟩ := rem_facts hrem hC.clen1
  obtain ⟨p2, m2⟩ := distCount_move (K := K) (a := a) (stop := stop) (pos := pos1) hH m1.rel hr0 hc hdc hf.posStop
  obtain ⟨_, _, _, rfl⟩ := m2.rel.distanceSymbol_of rfl
  obtain ⟨p3, m3⟩ := distShort_move C hH m2.rel hf.posStop hv hl h16 hd0 hw hrc
  exact ⟨p3, (applyDistance_fcopy hw hrc (dist_small hC hw) hn) ▸ (m1.trans m2).trans m3⟩

/-- A distance's code from 16 on: from the distance, a refill to 40 bits, the block count, the symbol and its extra
bits, then the copy. -/
theorem dLong_move {T : ByteArray} {tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0) (hH : HdrRel H m)
    (hrel : Rel w k.toNat m (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen clen p1 p2 .distance 0 pos) (.distance s c cl))
    {word1 count1 : UInt64} {pos1 : USize} (hf : FillOk a stop word count pos 40 word1 count1 pos1)
    (hrem : opos.toNat + clen.toNat ≤ rEnd.toNat) (hc : ¬ code < 128) (hdc : dCount ≠ 0) {v E D n01 n23 : UInt64}
    (hv : v = lookupT T (dRowBase C clen) word1 (C.dIn clen) C.lim C.size32) (h16 : ¬ wordSym v < 16)
    (hE : E = dEntry H.npostfix H.ndirect (wordSym v))
    (hD : D = (E >>> 32) + (((word1 >>> wordBits v) &&& maskT T C.big C.size32 (E &&& 31)) <<< H.npostfix))
    (hok : wordBits v + (E &&& 31) ≤ count1) (hd0 : D ≠ 0) (hw : ¬ (usmin cap16 (opos + wB)).toUInt64 < D)
    (hn : (wordSym v = 0 ∧ n01 = d01 ∧ n23 = d23) ∨
      (wordSym v ≠ 0 ∧ n01 = D ||| (d01 <<< 32) ∧ n23 = (d01 >>> 32) ||| (d23 <<< 32))) :
    ∃ p', MoveOk w k.toNat m K a stop (.distance s c cl)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2
        .distance 0 pos) pos p'
      (fcopy ((word1 >>> wordBits v) >>> (E &&& 31)) (count1 - wordBits v - (E &&& 31)) ring opos mask pB cap cap16 wB
        rEnd iCount LC (dCount - 1) flags x n01 n23 code ilen clen p1 p2 D pos1) := by
  have m1 := fill_move (K := K) hrel hf
  have hC := hrel.1
  obtain ⟨hr0, hrc⟩ := rem_facts hrem hC.clen1
  obtain ⟨p2, m2⟩ := distCount_move (K := K) (a := a) (stop := stop) (pos := pos1) hH m1.rel hr0 hc hdc hf.posStop
  obtain ⟨_, _, _, rfl⟩ := m2.rel.distanceSymbol_of rfl
  obtain ⟨p3, m3⟩ := distLong_move C hH m2.rel hf.posStop hv h16 hE hD hok hd0 hw hrc
  exact ⟨p3, (applyDistance_fcopy hw hrc (dist_small hC hw) hn) ▸ (m1.trans m2).trans m3⟩

/-- The copy at a command, then the next command: the fast copy's window, the context bytes read back from it, all at
the loop's unmasked position. -/
theorem fcopy_move {s : CommandState} {dd nn : Nat} {d : UInt64}
    (hrel : Rel w k.toNat m (fcopy word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen clen p1 p2 d pos) (.copy s dd nn))
    (hk : k.toNat ≤ 24) (hmk : mask = ringMask k) (hmN : mask.toNat = 2 ^ k.toNat - 1) {size : USize}
    (hsize : size.toNat = 2 ^ k.toNat) (hcap : cap16 = ringSize k - USize.ofNat 16) {bEnd : UInt64}
    (N : FNum opos pB wB rEnd bEnd k.toNat clen.toNat) (hsz : ring.size = 2 ^ k.toNat)
    (hd : d.toUSize.toNat + 16 ≤ 2 ^ k.toNat) (hp : pos.toNat ≤ stop.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.copy s dd nn)
      (fcopy word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2 d pos)
      pos p'
      (fexit word count (copyF ring (opos &&& mask) d.toUSize clen.toUSize mask size hk hmN hsize hsz (mask_lt hmN) hd)
        (opos + clen.toUSize) mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen
        (wget (copyF ring (opos &&& mask) d.toUSize clen.toUSize mask size hk hmN hsize hsz (mask_lt hmN) hd)
          (opos + clen.toUSize - USize.ofNat 1) mask hmN (copyF_size _ _ _ _ _ _ hk hmN hsize hsz _ hd))
        (wget (copyF ring (opos &&& mask) d.toUSize clen.toUSize mask size hk hmN hsize hsz (mask_lt hmN) hd)
          (opos + clen.toUSize - USize.ofNat 2) mask hmN (copyF_size _ _ _ _ _ _ hk hmN hsize hsz _ hd))
        .command 0 pos) := by
  have hC := hrel.1
  have hcl : 1 ≤ clen.toNat := hC.clen1
  have hcb : 1 ≤ x.copyBase.toNat := hC.cbase1
  have hleft : clen.toNat = nn := hrel.2.2.2.2.1
  subst hmk
  have hsk : size = ringSize k := USize.toNat_inj.mp (by rw [hsize, ringSize_toNat hk])
  subst hsk
  have hah := N.ahead
  have hpend := N.pend
  have hsm := N.small
  have hwr := N.wr
  have hbe := N.bEndLe
  have hcU : clen.toUSize.toNat = clen.toNat := word_toUSize (by omega)
  obtain ⟨p1', m1⟩ := copy_move (K := K) (a := a) (stop := stop) (pos := pos) (x := opos) hrel (by omega)
    (by show (opos + pB).toNat + nn + 16 ≤ _; omega) hp hk hsz (mask_lt hmN) hd
    (ring' := copyF ring (opos &&& ringMask k) d.toUSize clen.toUSize (ringMask k) (ringSize k) hk hmN hsize hsz
      (mask_lt hmN) hd) rfl (copyF_size _ _ _ _ _ _ hk hmN hsize hsz _ hd) rfl
  obtain ⟨_, _, _, rfl⟩ := m1.rel.copy_of rfl
  obtain ⟨p2', m2⟩ := copyEnd_move (K := K) (a := a) m1.rel rfl hp
  obtain ⟨_, rfl⟩ := m2.rel.command_of rfl
  have m3 := (m1.trans m2).congr (m2.rel.command_ext (cbits := x.copyBits) (cb := x.copyBase) (d := x.dist) hcb) rfl
    rfl rfl rfl
  have ep : opos + clen.toUSize + pB = opos + pB + clen.toUSize := by
    rw [USize.add_assoc, USize.add_comm clen.toUSize pB, ← USize.add_assoc]
  have ew : usmin cap16 (opos + clen.toUSize + wB) =
      usmin (ringSize k - USize.ofNat 16) (usmin cap16 (opos + wB) + clen.toUSize) := by
    rw [← hcap, usmin_add (by omega), USize.add_assoc opos clen.toUSize wB, USize.add_comm clen.toUSize wB,
      ← USize.add_assoc]
  have er : rEnd - (opos + clen.toUSize).toUInt64 = rEnd - opos.toUInt64 - clen := by
    rw [rem_add (by omega) (by omega)]
    congr 1
    exact UInt64.toNat_inj.mp (by rw [USize.toNat_toUInt64, hcU])
  exact ⟨_, by unfold fexit; rw [ep, ew, er]; exact m3⟩

/-- A command's start within its block, then its insert-and-copy element read through the tree (`icFb`, which the
fused entries equal): from a refill to 40 bits, the command's literals, in the loop's record. -/
theorem ic_round {T : ByteArray} {tb : UInt64} {modeOff lRow iRow iFb dRow s0 : USize}
    (C : FCtx H T x.lCur x.iCur x.dCur tb modeOff lRow iRow iFb dRow s0)
    (hK : ∀ s bs, s.remaining ≠ 0 → K s bs = readCommand w m s bs >>= fun (s1, b) => K s1 b) (hH : HdrRel H m)
    {s : CommandState}
    (hrel : Rel w k.toNat m (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code
      ilen clen p1 p2 .command 0 pos) (.command s))
    {word3 count3 : UInt64} {pos3 : USize} (hf : FillOk a stop word count pos 40 word3 count3 pos3)
    (hi : iCount ≠ 0) {v : UInt64} (hv : v = lookupT T (icFbBase C) word3 C.icIn C.lim C.size32)
    (hc : (wordSym v).toNat < 704)
    (hok : wordBits v + rowBits (insertRow (wordSym v) hc) + rowBits (copyRow (wordSym v) hc) ≤ count3)
    (hrem : opos.toNat + (rowBase (insertRow (wordSym v) hc) +
        ((word3 >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc)))).toNat +
      (rowBase (copyRow (wordSym v) hc) + (((word3 >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
        maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc)))).toNat ≤ rEnd.toNat) :
    ∃ p', MoveOk w k.toNat m K a stop (.command s)
      (fexit word count ring opos mask pB cap cap16 wB rEnd iCount LC dCount flags x d01 d23 code ilen clen p1 p2
        .command 0 pos) pos p'
      (fexit (((word3 >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) >>> rowBits (copyRow (wordSym v) hc))
        (count3 - wordBits v - rowBits (insertRow (wordSym v) hc) - rowBits (copyRow (wordSym v) hc)) ring opos mask pB
        cap cap16 wB rEnd (iCount - 1) LC dCount flags x d01 d23 (wordSym v)
        (rowBase (insertRow (wordSym v) hc) +
          ((word3 >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc))))
        (rowBase (copyRow (wordSym v) hc) + (((word3 >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
          maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc))))
        p1 p2 .literals
        (rowBase (insertRow (wordSym v) hc) +
          ((word3 >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc)))) pos3) := by
  have hC := hrel.1
  have hcb : 1 ≤ x.copyBase.toNat := hC.cbase1
  have m1 := fill_move (K := K) hrel hf
  have hcl : 1 ≤ (rowBase (copyRow (wordSym v) hc) + (((word3 >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
      maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc)))).toNat := by
    have h2 := cmdRow_copy2 hc
    rw [← (copyRow_fields hc).2] at h2
    have h3 : (rowBase (copyRow (wordSym v) hc)).toNat ≤ 2118 := by
      rw [(copyRow_fields hc).2]; exact (cmdRow_small hc).2.2.2
    have hcb24 := copyRow_bits hc
    have hX : (((word3 >>> wordBits v) >>> rowBits (insertRow (wordSym v) hc)) &&&
        maskT T C.big C.size32 (rowBits (copyRow (wordSym v) hc))).toNat < 16777216 := by
      rw [C.maskT_eq (by omega), shr_mask_toNat _ _ _ (by have := insertRow_bits hc; omega) (by omega)]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by decide) hcb24)
    rw [u64_add_small (by omega)]
    omega
  have e : (rEnd - opos.toUInt64).toNat = rEnd.toNat - opos.toNat := by
    rw [u64_sub_le (by rw [USize.toNat_toUInt64]; omega), USize.toNat_toUInt64]
  have hr0 : rEnd - opos.toUInt64 ≠ 0 := fun h0 => by
    have h0' := congrArg UInt64.toNat h0
    rw [e] at h0'
    have : (0 : UInt64).toNat = 0 := rfl
    omega
  have hrc : ¬ rEnd - opos.toUInt64 < rowBase (insertRow (wordSym v) hc) +
      ((word3 >>> wordBits v) &&& maskT T C.big C.size32 (rowBits (insertRow (wordSym v) hc))) := fun hl => by
    have := UInt64.lt_iff_toNat_lt.mp hl
    rw [e] at this
    omega
  obtain ⟨p2, m2⟩ := cmd_move (a := a) (stop := stop) (pos := pos3) hK hH m1.rel hr0 hi hf.posStop
  obtain ⟨_, _, rfl⟩ := m2.rel.insertCopy_of rfl
  obtain ⟨p3, m3⟩ := ic_move C hH m2.rel hf.posStop hv hc rfl rfl rfl rfl rfl hok hrc
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := m3.rel.literals_of rfl
  exact ⟨_, ((m1.trans m2).trans m3).congr
    (m3.rel.literals_ext (cbits := x.copyBits) (cb := x.copyBase) (d := x.dist) hcb) rfl rfl rfl rfl⟩

end

end Brotli.Decoder
