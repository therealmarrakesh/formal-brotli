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

end Brotli.Decoder
