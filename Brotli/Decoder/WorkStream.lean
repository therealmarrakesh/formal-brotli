import Brotli.Decoder.WorkCmd

/-!
# The work of the stream's steps and of a call

Each function here mirrors the stream's step, loop or call function of the same name without its `W`, branch by branch,
and counts the rounds of its loops. A loop that can stop early counts all the rounds it could take.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### The steps -/

/-- The work of `stepDWbits`: the refill, and the window's zeros. -/
def stepDWbitsW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  if hp : pos ≤ stop then
    let rf := refill D.cmd.word D.cmd.count a pos stop hs (USize.le_iff_toNat_le.mp hp)
    let r := wbitsFast ⟨rf.word, rf.count⟩
    refillW D.cmd.word D.cmd.count a pos stop hs + match r.status with
      | .ok => if (1 : UInt64) <<< r.a ≤ D.limit then zbW ((1 : UInt64) <<< r.a).toNat + 1 else 1
      | _ => 1
  else 1

/-- The work of `stepDMeta`: the refill, the start's read, and the header's first state. -/
def stepDMetaW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  if D.cmd.pend = 0 then
    if pos ≤ stop then refillW D.cmd.word D.cmd.count a pos stop hs + 2 else 1
  else 1

/-- The work of `rawRun`: a round for each byte, with a refill when the buffer runs low, and one for the round that
stops it. -/
def rawRunW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize) (p1 _p2 : UInt8)
    (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : Nat :=
  if hn : n = 0 then 1
  else
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hr : wpos.toNat < ring.size := by omega
    if 8 ≤ count then
      let byte := word.toUInt8
      1 + rawRunW a stop hs mask k hk hmask (n - USize.ofNat 1) (word >>> 8) (count - 8) pos (ringWrite ring wpos byte hr)
        (ringNext wpos mask) byte p1 hp ((size_ringWrite ring wpos byte hr).trans hsize) hnext
    else
      let r := refill word count a pos stop hs hp
      if h8 : 8 ≤ r.count ∧ r.pos ≤ stop then
        let byte := r.word.toUInt8
        refillW word count a pos stop hs + 1 + rawRunW a stop hs mask k hk hmask (n - USize.ofNat 1) (r.word >>> 8) (r.count - 8) r.pos
          (ringWrite ring wpos byte hr) (ringNext wpos mask) byte p1 (USize.le_iff_toNat_le.mp h8.2)
          ((size_ringWrite ring wpos byte hr).trans hsize) hnext
      else refillW word count a pos stop hs + 1
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred hn
    have := usize_ne hn
    omega

/-- The work of `stepDRaw`. -/
def stepDRawW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  let left := D.left
  if left = 0 then 1
  else
    let k := D.k
    let c := D.cmd
    if h : winCheck k c.wpos c.ring = true ∧ pos ≤ stop then
      if room k c.cap ≤ c.pend then 1
      else
        let n := usmin left.toUSize (room k c.cap - c.pend)
        have hsize := winCheck_size h.1
        have hwp := winCheck_pos h.1
        rawRunW a stop hs (ringMask k) k.toNat (winCheck_k h.1) (ringMask_toNat (winCheck_k h.1)) n c.word c.count pos c.ring c.wpos c.p1 c.p2
          (USize.le_iff_toNat_le.mp h.2) hsize hwp + 1
    else 1

/-- The work of `stepDHdr`: the header step, and at a header's end the command loop's header, made with no check, and
its first state, its block type flags copied from the shared ones. -/
def stepDHdrW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  stepHW a stop hs D.hd pos +
    if (stepH a stop hs D.hd pos).status = .ready then 770 else 0

/-- The work of `stepDCmds`: the command loop, and at the commands' end the check that every block type occurred. -/
def stepDCmdsW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) : Nat :=
  runCmdW D.H D.k a stop hs cmdBudget D.cmd pos +
    if (runCmd D.H D.k a stop hs cmdBudget D.cmd pos).status = .done then 772 else 0

/-- The work of a step of the whole decoder. -/
def stepDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) : Nat :=
  match D.tag with
  | .wbits => stepDWbitsW a stop hs D D.pos
  | .mblock => stepDMetaW a stop hs D D.pos
  | .skip => 1
  | .raw => stepDRawW a stop hs D D.pos
  | .hdr => stepDHdrW a stop hs D D.pos
  | .cmds => stepDCmdsW a stop hs D D.pos
  | .ended => 1

/-- The work of the decoder's loop: its rounds and their steps. -/
def runDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Nat :=
  if he : D.tag = .ended then 1
  else
    let r := stepD a stop hs D h
    stepDW a stop hs D + 1 + if hn : r.status = .next then runDW a stop hs r (h.step he hn) else 0
termination_by (RunArg.mk D h : RunArg a stop hs)
decreasing_by exact ⟨he, hn, rfl⟩

/-- The work of `flushAll`: a round for each byte it hands out, and two for each of its rounds. -/
def flushAllW (k : USize) (st : Cmd) (buf : ByteArray) (space : Nat) : Nat :=
  let p0 := st.pend
  if p0 = 0 ∨ space = 0 then 1
  else
    let r := flushCmd k st buf (USize.ofNat (min space 16777216))
    (p0 - r.st.pend).toNat + 2 +
      if _h : r.st.pend < p0 then flushAllW k r.st r.buf (space - (p0 - r.st.pend).toNat) else 0
termination_by st.pend.toNat
decreasing_by exact USize.lt_iff_toNat_lt.mp _h

/-- The work of `afterRun`: the bytes it hands out, and the end's check. -/
def afterRunW (r : Dec) (buf : ByteArray) (space : Nat) : Nat :=
  match r.status with
  | .needsInput => flushAllW r.k r.cmd buf space + 1
  | .next => flushAllW r.k r.cmd buf space + 2
  | .bad => flushAllW r.k r.cmd buf space + 1
  | _ => 1

/-- The work of a call: its rounds of the loop and of handing bytes out. -/
def callDW (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (final : Bool) (D : Dec) (h : DInv stop D) (buf : ByteArray)
    (space : Nat) : Nat :=
  runDW a stop hs (withCap D space) (h.withCap space) + 1 +
    if hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput then
      flushAllW (runD a stop hs (withCap D space) (h.withCap space)).k (runD a stop hs (withCap D space) (h.withCap space)).cmd buf space +
        if (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0 then
          if _hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space then
            callDW a stop hs final (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D
              (flushD_inv (runD_full hO) buf space) (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).buf
              (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space
          else 1
        else 1
    else afterRunW (runD a stop hs (withCap D space) (h.withCap space)) buf space
termination_by space
decreasing_by exact _hlt

/-! ### What the stream's reads take -/

private theorem obind {β γ : Type} {x : Option β} {f : β → Option γ} {z : γ} (h : (x >>= f) = some z) :
    ∃ v, x = some v ∧ f v = some z :=
  Option.bind_eq_some_iff.mp h

theorem msUnc_le {last : Bool} {mlen : Nat} {bs b : List Bool} {v : MetaStart} (h : msUnc last mlen bs = some (v, b)) :
    b.length ≤ bs.length := by
  unfold msUnc at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact Nat.le_refl _
  · obtain ⟨u, hu, h2⟩ := obind h
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    rw [← h2.2]
    have := readInt_length _ _ _ _ hu
    omega

theorem msLen_le {last : Bool} {mn : Nat} {bs b : List Bool} {v : MetaStart} (h : msLen last mn bs = some (v, b)) :
    b.length + mn * 4 ≤ bs.length := by
  unfold msLen at h
  obtain ⟨u, hu, h2⟩ := obind h
  have := readInt_length _ _ _ _ hu
  split at h2
  · cases h2
  · have := msUnc_le h2
    omega

theorem msBody_data {last l : Bool} {mlen : Nat} {unc : Bool} {bs b : List Bool}
    (h : msBody last bs = some (.data l mlen unc, b)) : b.length + 18 ≤ bs.length := by
  unfold msBody at h
  obtain ⟨u, hu, h2⟩ := obind h
  have := readInt_length _ _ _ _ hu
  split at h2
  · obtain ⟨r, -, h3⟩ := obind h2
    split at h3
    · cases h3
    · obtain ⟨n, -, h4⟩ := obind h3
      unfold msSkip at h4
      obtain ⟨x, -, h5⟩ := obind h4
      split at h5
      · cases h5
      · simp only [Option.some.injEq, Prod.mk.injEq] at h5
        exact absurd h5.1 (fun e => MetaStart.noConfusion e)
  · have := msLen_le h2
    omega

/-- A meta-block of data takes at least 19 bits to start: ISLAST, MNIBBLES and at least four nibbles of MLEN. -/
theorem metaStart_data {l : Bool} {mlen : Nat} {unc : Bool} {bs b : List Bool}
    (h : metaStart bs = some (.data l mlen unc, b)) : b.length + 19 ≤ bs.length := by
  unfold metaStart at h
  obtain ⟨u, hu, h2⟩ := obind h
  have := readInt_length _ _ _ _ hu
  split at h2
  · have := msBody_data h2
    omega
  · obtain ⟨e, he, h3⟩ := obind h2
    have := readInt_length _ _ _ _ he
    split at h3
    · simp only [Option.some.injEq, Prod.mk.injEq] at h3
      exact absurd h3.1 (fun e => MetaStart.noConfusion e)
    · have := msBody_data h3
      omega

/-- The loop for uncompressed bytes: ten for each byte it moves, and ten. -/
theorem rawRunW_le (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray)
    (wpos : USize) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k),
    n.toNat = N → rawRunW a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp +
      10 * (rawRun a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp).left.toNat ≤ 10 * N + 10 := by
  intro N
  induction N with
  | zero =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp hN
    have hz : n = 0 := usize_zero hN
    rw [rawRunW, dite_eq_left hz, rawRun, dite_eq_left hz]
    show 1 + 10 * n.toNat ≤ _
    omega
  | succ N ih =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    have hR := refillW_le (word := word) (count := count) hs hp
    rw [rawRunW, dite_eq_right hn, rawRun, dite_eq_right hn]
    dsimp only
    split
    · rw [Nat.add_assoc]
      refine Nat.le_trans (Nat.add_le_add_left (ih _ _ _ _ _ _ _ _ _ _ _ ?_) _) ?_
      · rw [hpred]
        omega
      · omega
    · split
      · rw [Nat.add_assoc]
        refine Nat.le_trans (Nat.add_le_add_left (ih _ _ _ _ _ _ _ _ _ _ _ ?_) _) ?_
        · rw [hpred]
          omega
        · omega
      · show refillW word count a pos stop hs + 1 + 10 * n.toNat ≤ _
        omega

end Brotli.Decoder
