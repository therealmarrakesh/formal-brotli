import Brotli.Decoder.Layout

/-!
# The bytes left waiting

A step keeps the cap on waiting bytes, and leaves no more bytes waiting than were waiting before it or the cap allows.
-/

namespace Brotli.Decoder

/-- The most bytes a cap lets wait. -/
def capE (c : USize) : Nat := max c.toNat 1

theorem room_capE (k c : USize) : (room k c).toNat ≤ capE c := by
  unfold room capE
  rw [usmin_toNat]
  by_cases hc : c = 0
  · rw [ite_eq_left hc, usize_ofNat' (by decide)]
    omega
  · rw [ite_eq_right hc]
    omega

/-- A step keeps the cap, and leaves no more bytes waiting than were waiting or the cap allows. -/
def PendLe (st r : Cmd) : Prop := r.cap = st.cap ∧ r.pend.toNat ≤ max st.pend.toNat (capE st.cap)

theorem PendLe.keep {st r : Cmd} (h1 : r.pend = st.pend) (h2 : r.cap = st.cap) : PendLe st r :=
  ⟨h2, by rw [h1]; exact Nat.le_max_left _ _⟩

theorem PendLe.rfl' (st : Cmd) : PendLe st st := PendLe.keep rfl rfl

theorem PendLe.trans {s1 s2 s3 : Cmd} (h1 : PendLe s1 s2) (h2 : PendLe s2 s3) : PendLe s1 s3 := by
  obtain ⟨c1, p1⟩ := h1
  obtain ⟨c2, p2⟩ := h2
  rw [c1] at p2
  exact ⟨c2.trans c1, by omega⟩

/-- More bytes waiting, within the room. -/
theorem add_run_le {pend run rm : USize} (hlt : pend.toNat < rm.toNat) (hr : run.toNat ≤ rm.toNat - pend.toNat) :
    (pend + run).toNat ≤ rm.toNat := by
  have := rm.toNat_lt_size
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by rw [← USize.size_eq_two_pow]; omega)]
  omega

/-- A run within the room left. -/
theorem umin_run_le (l : UInt64) (x : USize) : (umin l x.toUInt64).toUSize.toNat ≤ x.toNat := by
  rw [UInt64.toNat_toUSize, umin_toNat, USize.toNat_toUInt64]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.min_le_right _ _)

/-- A step whose bytes fit the room left. -/
theorem PendLe.ofRun {st r : Cmd} {k run : USize} (hc : r.cap = st.cap) (hroom : ¬ room k st.cap ≤ st.pend)
    (hp : r.pend = st.pend + run) (hr : run.toNat ≤ (room k st.cap - st.pend).toNat) : PendLe st r := by
  have hlt := room_lt hroom
  rw [room_sub' (by omega)] at hr
  refine ⟨hc, ?_⟩
  rw [hp]
  have := add_run_le hlt hr
  have := room_capE k st.cap
  omega

/-! ### The command loop -/

/-- Closes the goals a step that keeps its waiting bytes leaves. -/
macro "keep_tac" : tactic => `(tactic| ((try dsimp only) <;> repeat' (first | split_all | exact PendLe.keep rfl rfl)))

theorem stepCommand_pendLe (H : Hdr) (st : Cmd) (p : USize) : PendLe st (stepCommand H st p) := by
  unfold stepCommand markStep clearSeen
  keep_tac

theorem stepInsertCopy_pendLe (H : Hdr) (st : Cmd) (p : USize) : PendLe st (stepInsertCopy H st p) := by
  unfold stepInsertCopy insertStep markStep
  keep_tac

theorem stepCopyLength_pendLe (st : Cmd) (p : USize) : PendLe st (stepCopyLength st p) := by
  unfold stepCopyLength markStep
  keep_tac

theorem applyBuilt_pendLe (st : Cmd) (p : USize) (word : ByteArray) : PendLe st (applyBuilt st p word) := by
  unfold applyBuilt markStep
  keep_tac

theorem applyWord_pendLe (st : Cmd) (p : USize) (wordId : UInt64) : PendLe st (applyWord st p wordId) := by
  unfold applyWord markStep
  try dsimp only
  repeat' (first | split_all | exact applyBuilt_pendLe _ _ _ | exact PendLe.keep rfl rfl)

theorem applyDistance_pendLe (st : Cmd) (p : USize) (dcode d : UInt64) : PendLe st (applyDistance st p dcode d) := by
  unfold applyDistance markStep
  try dsimp only
  repeat' (first | split_all | exact applyWord_pendLe _ _ _ | exact PendLe.keep rfl rfl)

set_option maxRecDepth 65536 in
theorem distanceStep_pendLe (H : Hdr) (st : Cmd) (p : USize) (v : UInt64) : PendLe st (distanceStep H st p v) := by
  unfold distanceStep markStep
  try dsimp only
  repeat' (first | split_all | exact (PendLe.keep (r := setBits st _ _) rfl rfl).trans (applyDistance_pendLe _ _ _ _) | exact PendLe.keep rfl rfl)

theorem stepDistance_pendLe (H : Hdr) (st : Cmd) (p : USize) : PendLe st (stepDistance H st p) := by
  unfold stepDistance markStep clearSeen
  try dsimp only
  repeat' (first | split_all | exact applyDistance_pendLe _ _ _ _ | exact PendLe.keep rfl rfl)

theorem stepDistanceSymbol_pendLe (H : Hdr) (st : Cmd) (p : USize) : PendLe st (stepDistanceSymbol H st p) := by
  unfold stepDistanceSymbol distanceThrough markStep
  try dsimp only
  repeat' (first | split_all | exact distanceStep_pendLe _ _ _ _ | exact PendLe.keep rfl rfl)

theorem stepCopy_pendLe (k : USize) (st : Cmd) (p : USize) : PendLe st (stepCopy k st p) := by
  unfold stepCopy markStep finishCopy clearRing
  dsimp only
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    exact PendLe.keep rfl rfl
  · rw [ite_eq_right h0]
    by_cases hf : room k st.cap ≤ st.pend
    · rw [ite_eq_left hf]
      exact PendLe.keep rfl rfl
    · rw [ite_eq_right hf]
      split
      · exact PendLe.ofRun rfl hf rfl (umin_run_le _ _)
      · exact PendLe.keep rfl rfl

theorem stepWord_pendLe (k : USize) (st : Cmd) (p : USize) : PendLe st (stepWord k st p) := by
  unfold stepWord markStep finishWord clearRing
  dsimp only
  by_cases h0 : st.wordBuf.usize - st.wordPos = 0
  · rw [ite_eq_left h0]
    exact PendLe.keep rfl rfl
  · rw [ite_eq_right h0]
    by_cases hf : room k st.cap ≤ st.pend
    · rw [ite_eq_left hf]
      exact PendLe.keep rfl rfl
    · rw [ite_eq_right hf]
      split
      · exact PendLe.ofRun rfl hf rfl (by rw [usmin_toNat]; exact Nat.min_le_right _ _)
      · exact PendLe.keep rfl rfl

/-- The literal loop leaves at most as many literals as it was asked for. -/
theorem literalRun_left {nTrees : Nat} {arena litBase lMap : ByteArray} {C : LitChecked arena litBase lMap nTrees}
    {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {mapBase modeOff mask : USize} {k : Nat}
    {hmb : mapBase.toNat + 64 ≤ lMap.size} {hm : modeOff.toNat + 512 ≤ 2048} {hd : modeOff.toNat % 512 = 0}
    {hmask : mask.toNat = 2 ^ k - 1} {hk : k ≤ 24} :
    ∀ (N : Nat) {n : USize} {word count : UInt64} {pos wpos : USize} {ring : ByteArray} {p1 p2 : UInt8}
      {hp : pos.toNat ≤ stop.toNat} {hw : (BitBuffer.mk word count).Wf} {hsize : ring.size = 2 ^ k}
      {hwp : wpos.toNat < 2 ^ k}, n.toNat = N →
      (literalRun C a stop hs mapBase modeOff mask k hmb hm hd hmask hk n word count pos wpos ring p1 p2 hp hw hsize hwp).left.toNat ≤
        n.toNat := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n word count pos wpos ring p1 p2 hp hw hsize hwp hN
    rw [literalRun]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]
      show (0 : USize).toNat ≤ _
      exact Nat.zero_le _
    · rw [dite_eq_right hn]
      dsimp only
      have hpred := usize_pred hn
      have hne := usize_ne hn
      split
      · exact Nat.le_trans (ih _ (by omega) (n := n - USize.ofNat 1) rfl) (by omega)
      · exact Nat.le_refl _

/-- The uncompressed bytes' loop leaves at most as many bytes as it was asked for. -/
theorem rawRun_left {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {mask : USize} {k : Nat} {hk : k ≤ 24}
    {hmask : mask.toNat = 2 ^ k - 1} :
    ∀ (N : Nat) {n : USize} {word count : UInt64} {pos : USize} {ring : ByteArray} {wpos : USize} {p1 p2 : UInt8}
      {hp : pos.toNat ≤ stop.toNat} {hsize : ring.size = 2 ^ k} {hwp : wpos.toNat < 2 ^ k}, n.toNat = N →
      (rawRun a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp).left.toNat ≤ n.toNat := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp hN
    rw [rawRun]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]
      exact Nat.le_refl _
    · rw [dite_eq_right hn]
      dsimp only
      have hpred := usize_pred hn
      have hne := usize_ne hn
      split
      · exact Nat.le_trans (ih _ (by omega) (n := n - USize.ofNat 1) rfl) (by omega)
      · split
        · exact Nat.le_trans (ih _ (by omega) (n := n - USize.ofNat 1) rfl) (by omega)
        · exact Nat.le_refl _

/-- What is left of a run, taken from it. -/
theorem sub_left_le {run left : USize} (h : left.toNat ≤ run.toNat) : (run - left).toNat ≤ run.toNat := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr h)]
  omega

/-- A literal run within the room left. -/
theorem umin2_run_le (l c : UInt64) (x : USize) : (umin l (umin c x.toUInt64)).toUSize.toNat ≤ x.toNat := by
  rw [UInt64.toNat_toUSize, umin_toNat, umin_toNat, USize.toNat_toUInt64]
  exact Nat.le_trans (Nat.mod_le _ _) (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))

theorem literalsRun_pendLe (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd)
    (p : USize) (hroom : ¬ room k st.cap ≤ st.pend) : PendLe st (literalsRun H k a stop hs st p) := by
  unfold literalsRun markStep
  try dsimp only
  split
  · split
    · exact PendLe.ofRun rfl hroom rfl (Nat.le_trans (sub_left_le (literalRun_left _ rfl)) (umin2_run_le _ _ _))
    · exact PendLe.keep rfl rfl
  · exact PendLe.keep rfl rfl

theorem stepLiterals_pendLe (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd)
    (p : USize) : PendLe st (stepLiterals H k a stop hs st p) := by
  unfold stepLiterals markStep clearSeen
  try dsimp only
  by_cases h0 : st.left = 0
  · rw [ite_eq_left h0]
    exact PendLe.keep rfl rfl
  · rw [ite_eq_right h0]
    by_cases hc : st.lCount = 0
    · rw [ite_eq_left hc]
      repeat' (first | split_all | exact PendLe.keep rfl rfl)
    · rw [ite_eq_right hc]
      by_cases hf : room k st.cap ≤ st.pend
      · rw [ite_eq_left hf]
        exact PendLe.keep rfl rfl
      · rw [ite_eq_right hf]
        exact literalsRun_pendLe H k a stop hs st p hf

theorem stepAt_pendLe (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (p : USize) :
    PendLe st (stepAt H k a stop hs st p) := by
  unfold stepAt
  cases st.tag
  · exact stepCommand_pendLe H st p
  · exact stepInsertCopy_pendLe H st p
  · exact stepCopyLength_pendLe st p
  · exact stepLiterals_pendLe H k a stop hs st p
  · exact stepDistance_pendLe H st p
  · exact stepDistanceSymbol_pendLe H st p
  · exact stepCopy_pendLe k st p
  · exact stepWord_pendLe k st p

theorem stepCmd_pendLe (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (st : Cmd) (p : USize) :
    PendLe st (stepCmd H k a stop hs st p) := by
  unfold stepCmd markStep
  split
  · exact (PendLe.keep (r := { st with word := _, count := _ }) rfl rfl).trans (stepAt_pendLe H k a stop hs _ _)
  · exact PendLe.keep rfl rfl

theorem runCmd_pendLe (H : Hdr) (k : USize) (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (N : Nat) (n : USize) (st : Cmd) (p : USize), n.toNat = N → PendLe st (runCmd H k a stop hs n st p) := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n st p hN
    rw [runCmd]
    by_cases hn : n = 0
    · rw [dite_eq_left hn]
      exact PendLe.keep rfl rfl
    · rw [dite_eq_right hn]
      dsimp only
      have hpred := usize_pred hn
      have hne := usize_ne hn
      have h1 := stepCmd_pendLe H k a stop hs st p
      split
      · exact h1.trans (ih _ (by omega) _ _ _ rfl)
      · exact h1

/-- A command's start writes nothing. -/
theorem stepCommand_pend (H : Hdr) (st : Cmd) (p : USize) : (stepCommand H st p).pend = st.pend := by
  unfold stepCommand markStep clearSeen
  try dsimp only
  repeat' (first | split_all | rfl)

theorem stepCmd_pend_command {H : Hdr} {k : USize} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Cmd}
    {pos : USize} (ht : st.tag = .command) : (stepCmd H k a stop hs st pos).pend = st.pend := by
  unfold stepCmd
  split
  · unfold stepAt
    dsimp only
    rw [ht]
    exact stepCommand_pend _ _ _
  · rfl

/-! ### The stream's steps -/

/-- A stream step keeps the cap, and leaves no more bytes waiting than were waiting or the cap allows. -/
def PendLeD (D r : Dec) : Prop := PendLe D.cmd r.cmd

theorem PendLeD.trans {D1 D2 D3 : Dec} (h1 : PendLeD D1 D2) (h2 : PendLeD D2 D3) : PendLeD D1 D3 := PendLe.trans h1 h2

/-- Closes the goals a stream step that keeps its waiting bytes leaves. -/
macro "keepD_tac" : tactic => `(tactic| ((try dsimp only) <;> repeat' (first | split_all | exact PendLe.keep rfl rfl | exact ⟨rfl, Nat.zero_le _⟩)))

theorem stepDWbits_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    PendLeD D (stepDWbits a stop hs D pos) := by
  unfold PendLeD stepDWbits winStart
  keepD_tac

theorem stepDMeta_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    PendLeD D (stepDMeta a stop hs D pos) := by
  unfold PendLeD stepDMeta metaGo
  keepD_tac

theorem stepDSkip_pendLe (stop : USize) (D : Dec) (pos : USize) : PendLeD D (stepDSkip stop D pos) := by
  unfold PendLeD stepDSkip moveOn
  keepD_tac

theorem stepDRaw_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    PendLeD D (stepDRaw a stop hs D pos) := by
  unfold PendLeD stepDRaw takeRing moveOn rawFinish clearCmd clearRing
  try dsimp only
  by_cases h0 : D.left = 0
  · rw [ite_eq_left h0]
    exact PendLe.keep rfl rfl
  · rw [ite_eq_right h0]
    split
    · by_cases hf : room D.k D.cmd.cap ≤ D.cmd.pend
      · rw [ite_eq_left hf]
        exact PendLe.keep rfl rfl
      · rw [ite_eq_right hf]
        exact PendLe.ofRun rfl hf rfl (Nat.le_trans (sub_left_le (rawRun_left _ rfl)) (by rw [usmin_toNat]; exact Nat.min_le_right _ _))
    · exact PendLe.keep rfl rfl

theorem stepDHdr_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    PendLeD D (stepDHdr a stop hs D pos) := by
  unfold PendLeD stepDHdr takeHd clearHd cmdStart
  keepD_tac

theorem stepDCmds_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    PendLeD D (stepDCmds a stop hs D pos) := by
  have h := runCmd_pendLe D.H D.k a stop hs _ cmdBudget D.cmd pos rfl
  unfold PendLeD stepDCmds takeCmd clearCmd
  try dsimp only
  repeat' (first | split_all | exact h)

theorem stepD_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) : PendLeD D (stepD a stop hs D) := by
  unfold stepD
  cases D.tag
  · exact stepDWbits_pendLe a stop hs D D.pos
  · exact stepDMeta_pendLe a stop hs D D.pos
  · exact stepDSkip_pendLe stop D D.pos
  · exact stepDRaw_pendLe a stop hs D D.pos
  · exact stepDHdr_pendLe a stop hs D D.pos
  · exact stepDCmds_pendLe a stop hs D D.pos
  · exact PendLe.rfl' _

theorem runD_pendLe (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ x : RunArg a stop hs, PendLeD x.D (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    obtain ⟨D, hinv⟩ := x
    dsimp only at ih ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      exact PendLe.keep rfl rfl
    · rw [dite_eq_right he]
      dsimp only
      have h1 := stepD_pendLe a stop hs D
      by_cases hn : (stepD a stop hs D).status = .next
      · rw [dite_eq_left hn]
        exact h1.trans (ih ⟨_, hinv.step he hn⟩ ⟨he, hn, rfl⟩)
      · rw [dite_eq_right hn]
        exact h1

end Brotli.Decoder
