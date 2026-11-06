module

public import Brotli.Decoder.StreamRun

@[expose] public section

/-!
# Header steps without the stream state

`runDF` is `runD` with a faster way to the same result: at a header, `runD` takes one header step per stream step, and
each one takes the header machine's state out of the stream state (`takeHd`), steps it, and builds the stream state again
(`hdrNext`). `runDF` takes the state out once, repeats `stepH` on it while each step moves on (`hdrRun`, up to
`hdrFuel` steps), and builds the stream state once. The header steps are the same, read the same bits and write the same
tables in the same order; only the stream state between them is no longer built. `runD_eq_runDF` proves the two loops
equal, and `@[csimp]` makes the compiled code use `runDF`, so every proof about `runD` stands for what runs.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- A header step that moved on leaves a state in a header, with its position in the chunk. -/
theorem stepH_in {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} (h : HIn st)
    (hp : pos.toNat ≤ stop.toNat) (hn : (stepH a stop hs st pos h hp).status = .next) :
    HIn (stepH a stop hs st pos h hp) ∧ (stepH a stop hs st pos h hp).pos.toNat ≤ stop.toNat := by
  obtain ⟨g, p, hrel, hb⟩ := id h
  obtain ⟨g', p', _, hR', _, h2, _, _, hmv, _⟩ :=
    (stepH_ok (K := (⟨fun _ _ => none, fun _ x => x⟩ : HK Unit)) (hs := hs) hrel hp hb (h := h)).next hn
  exact ⟨⟨g', p', hR', hmv.bud hb⟩, h2⟩

/-- How many header steps `hdrRun` takes at most before the stream state is built again. -/
def hdrFuel : Nat := 65536

/-- Up to `fuel + 1` header steps on the header machine's state alone, while each moves on; then the stream state is
built once, as `hdrNext` builds it after one. -/
def hdrRun (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (c : Cmd) (left : UInt64) (D0 : Dec) :
    (fuel : Nat) → (st : Hd) → (pos : USize) → HIn st → pos.toNat ≤ stop.toNat → Dec
  | 0, st, pos, h, hp => hdrNext c left D0 (stepHR a stop hs st pos h hp)
  | f + 1, st, pos, h, hp =>
    let r := stepHR a stop hs st pos h hp
    if hn : r.1.status = .next then
      hdrRun a stop hs c left D0 f r.1 r.1.pos (stepH_in h hp hn).1 (stepH_in h hp hn).2
    else hdrNext c left D0 r

/-- `hdrNext` reads nothing of the emptied stream state's position or status. -/
theorem hdrNext_congr {c : Cmd} {left : UInt64} {D0 : Dec} {x : USize} {y : DStatus}
    (r : { r : Hd // r.status = .ready → ∃ g, Upto r.d g 10 }) :
    hdrNext c left { D0 with pos := x, status := y } r = hdrNext c left D0 r := by
  unfold hdrNext
  dsimp only

section
variable {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size}

/-- One stream step at a header, taken apart. -/
theorem stepD_hdr' {D : Dec} {h : DInv stop D} (ht : D.tag = .hdr) :
    stepD a stop hs D h = hdrNext D.cmd D.left (clearHd D) (stepHR a stop hs D.hd D.pos (h.hd ht) h.2) := by
  rw [stepD_hdr ht]
  rfl

/-- `runD`, one step on. -/
theorem runD_step {D : Dec} {h : DInv stop D} (he : D.tag ≠ .ended) :
    runD a stop hs D h = if hn : (stepD a stop hs D h).status = .next then
      runD a stop hs (stepD a stop hs D h) (h.step he hn) else stepD a stop hs D h := by
  rw [runD, dite_eq_right he]

/-- What `hdrRun` leaves is what `runD`'s steps reach from a stream state in the same header: in the loop's relation,
and with the same result from there. -/
theorem hdrRun_spec (c : Cmd) (left : UInt64) (D0 : Dec) :
    ∀ (fuel : Nat) (D : Dec) (hD : DInv stop D) (st : Hd) (pos : USize) (h : HIn st) (hp : pos.toNat ≤ stop.toNat),
      D.tag = .hdr → D.hd = st → D.pos = pos → D.cmd = c → D.left = left →
      (∃ x y, clearHd D = { D0 with pos := x, status := y }) →
      ((hdrRun a stop hs c left D0 fuel st pos h hp).status = .next → DInv stop (hdrRun a stop hs c left D0 fuel st pos h hp)) ∧
      (∀ hr, (hdrRun a stop hs c left D0 fuel st pos h hp).status = .next →
        Relation.TransGen (runRel a stop hs) ⟨hdrRun a stop hs c left D0 fuel st pos h hp, hr⟩ ⟨D, hD⟩) ∧
      (∀ hr : (hdrRun a stop hs c left D0 fuel st pos h hp).status = .next →
          DInv stop (hdrRun a stop hs c left D0 fuel st pos h hp),
        runD a stop hs D hD = if hn : (hdrRun a stop hs c left D0 fuel st pos h hp).status = .next then
          runD a stop hs (hdrRun a stop hs c left D0 fuel st pos h hp) (hr hn)
        else hdrRun a stop hs c left D0 fuel st pos h hp) := by
  intro fuel
  induction fuel with
  | zero =>
    intro D hD st pos h hp ht hst hpos hc hl hD0
    subst hst hpos hc hl
    obtain ⟨x, y, e⟩ := hD0
    have hne : D.tag ≠ .ended := by rw [ht]; exact fun e => DTag.noConfusion e
    have es : hdrRun a stop hs D.cmd D.left D0 0 D.hd D.pos h hp = stepD a stop hs D hD := by
      rw [stepD_hdr' ht, e, hdrNext_congr]
      rfl
    rw [es]
    exact ⟨fun hn => hD.step hne hn, fun _ hn => Relation.TransGen.single ⟨hne, hn, rfl⟩,
      fun _ => runD_step hne⟩
  | succ f ih =>
    intro D hD st pos h hp ht hst hpos hc hl hD0
    subst hst hpos hc hl
    obtain ⟨x, y, e⟩ := hD0
    have hne : D.tag ≠ .ended := by rw [ht]; exact fun e => DTag.noConfusion e
    have es1 : stepD a stop hs D hD = hdrNext D.cmd D.left D0 (stepHR a stop hs D.hd D.pos h hp) := by
      rw [stepD_hdr' ht, e, hdrNext_congr]
    by_cases hn : (stepHR a stop hs D.hd D.pos h hp).1.status = .next
    · -- one step moved on: the stream state it leaves is in the same header, and the rest is `hdrRun`'s
      have er : hdrRun a stop hs D.cmd D.left D0 (f + 1) D.hd D.pos h hp =
          hdrRun a stop hs D.cmd D.left D0 f (stepHR a stop hs D.hd D.pos h hp).1
            (stepHR a stop hs D.hd D.pos h hp).1.pos (stepH_in h hp hn).1 (stepH_in h hp hn).2 := by
        rw [hdrRun, dite_eq_left hn]
      have hsn : (stepD a stop hs D hD).status = .next := by
        rw [es1]
        unfold hdrNext
        dsimp only
        split
        · rfl
        all_goals (rename_i hx; exact absurd (hn.symm.trans hx) (fun e => HStatus.noConfusion e))
      have hD1 := hD.step hne hsn
      have ht1 : (stepD a stop hs D hD).tag = .hdr ∧ (stepD a stop hs D hD).hd = (stepHR a stop hs D.hd D.pos h hp).1 ∧
          (stepD a stop hs D hD).pos = (stepHR a stop hs D.hd D.pos h hp).1.pos ∧
          (stepD a stop hs D hD).cmd = D.cmd ∧ (stepD a stop hs D hD).left = D.left ∧
          clearHd (stepD a stop hs D hD) = { D0 with pos := (stepHR a stop hs D.hd D.pos h hp).1.pos, status := .next } := by
        rw [es1]
        unfold hdrNext
        dsimp only
        split
        · have h0 : D0.hd = Hd.none := by
            have := congrArg Dec.hd e
            exact this.symm
          have hct : D0.cmd = D.cmd := (congrArg Dec.cmd e).symm
          have hlt : D0.left = D.left := (congrArg Dec.left e).symm
          have htt : D0.tag = .hdr := ((congrArg Dec.tag e).symm).trans ht
          refine ⟨htt, rfl, rfl, hct, hlt, ?_⟩
          unfold clearHd
          rw [← h0]
        all_goals (rename_i hx; exact absurd (hn.symm.trans hx) (fun e => HStatus.noConfusion e))
      obtain ⟨i1, i2, i3⟩ := ih (stepD a stop hs D hD) hD1 _ _ (stepH_in h hp hn).1 (stepH_in h hp hn).2 ht1.1 ht1.2.1
        ht1.2.2.1 ht1.2.2.2.1 ht1.2.2.2.2.1 ⟨_, _, ht1.2.2.2.2.2⟩
      rw [er]
      refine ⟨i1, fun hr hn' => Relation.TransGen.tail (i2 hr hn') ⟨hne, hsn, rfl⟩, fun hr => ?_⟩
      rw [runD_step hne, dite_eq_left hsn]
      exact i3 hr
    · have es : hdrRun a stop hs D.cmd D.left D0 (f + 1) D.hd D.pos h hp = stepD a stop hs D hD := by
        rw [es1, hdrRun, dite_eq_right hn]
      rw [es]
      exact ⟨fun hn => hD.step hne hn, fun _ hn => Relation.TransGen.single ⟨hne, hn, rfl⟩,
        fun _ => runD_step hne⟩

/-- The header steps a stream state at a header takes at once. -/
@[inline] def stepDHdrF (D : Dec) (h : DInv stop D) (ht : D.tag = .hdr) : Dec :=
  hdrRun a stop hs D.cmd D.left (clearHd D) hdrFuel D.hd D.pos (h.hd ht) h.2

theorem stepDHdrF_spec {D : Dec} {h : DInv stop D} (ht : D.tag = .hdr) :
    ((stepDHdrF (hs := hs) D h ht).status = .next → DInv stop (stepDHdrF (hs := hs) D h ht)) ∧
      (∀ hr, (stepDHdrF (hs := hs) D h ht).status = .next →
        Relation.TransGen (runRel a stop hs) ⟨stepDHdrF (hs := hs) D h ht, hr⟩ ⟨D, h⟩) ∧
      (∀ hr : (stepDHdrF (hs := hs) D h ht).status = .next → DInv stop (stepDHdrF (hs := hs) D h ht),
        runD a stop hs D h = if hn : (stepDHdrF (hs := hs) D h ht).status = .next then
          runD a stop hs (stepDHdrF (hs := hs) D h ht) (hr hn)
        else stepDHdrF (hs := hs) D h ht) :=
  hdrRun_spec D.cmd D.left (clearHd D) hdrFuel D h D.hd D.pos (h.hd ht) h.2 ht rfl rfl rfl rfl ⟨D.pos, D.status, rfl⟩

end

/-- What `runDF` recurs on: `runD`'s argument, ordered by any number of the loop's steps at once. -/
structure RunArgT (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) where
  x : RunArg a stop hs

instance (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) : WellFoundedRelation (RunArgT a stop hs) :=
  ⟨fun u v => Relation.TransGen (runRel a stop hs) u.x v.x, InvImage.wf RunArgT.x (runRel_wf a stop hs).transGen⟩

/-- `runD`, with a header's steps taken on the header machine's state alone. -/
def runDF (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (h : DInv stop D) : Dec :=
  if he : D.tag = .ended then { D with status := .next }
  else if ht : D.tag = .hdr then
    let r := stepDHdrF (hs := hs) D h ht
    if hn : r.status = .next then runDF a stop hs r ((stepDHdrF_spec ht).1 hn) else r
  else
    let r := stepD a stop hs D h
    if hn : r.status = .next then runDF a stop hs r (h.step he hn) else r
termination_by (⟨RunArg.mk D h⟩ : RunArgT a stop hs)
decreasing_by
  · exact (stepDHdrF_spec ht).2.1 _ hn
  · exact Relation.TransGen.single ⟨he, hn, rfl⟩

/-- `runDF` is `runD`. -/
theorem runD_eq_runDF_aux (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) :
    ∀ (x : RunArg a stop hs), runD a stop hs x.D x.inv = runDF a stop hs x.D x.inv := by
  intro x
  induction x using (runRel_wf a stop hs).transGen.induction with
  | _ x ih =>
  obtain ⟨D, h⟩ := x
  dsimp only at ih ⊢
  by_cases he : D.tag = .ended
  · rw [runD, runDF, dite_eq_left he, dite_eq_left he]
  · by_cases ht : D.tag = .hdr
    · rw [runDF, dite_eq_right he, dite_eq_left ht]
      dsimp only
      obtain ⟨s1, s2, s3⟩ := stepDHdrF_spec (hs := hs) (h := h) ht
      rw [s3 s1]
      by_cases hn : (stepDHdrF (hs := hs) D h ht).status = .next
      · rw [dite_eq_left hn, dite_eq_left hn]
        exact ih ⟨_, s1 hn⟩ (s2 _ hn)
      · rw [dite_eq_right hn, dite_eq_right hn]
    · rw [runD, runDF, dite_eq_right he, dite_eq_right he, dite_eq_right ht]
      dsimp only
      by_cases hn : (stepD a stop hs D h).status = .next
      · rw [dite_eq_left hn, dite_eq_left hn]
        exact ih ⟨_, h.step he hn⟩ (Relation.TransGen.single ⟨he, hn, rfl⟩)
      · rw [dite_eq_right hn, dite_eq_right hn]

/-- The swap: what runs takes a header's steps on the header machine's state alone. -/
@[csimp] theorem runD_eq_runDF : @runD = @runDF := by
  funext a stop hs D h
  exact runD_eq_runDF_aux a stop hs ⟨D, h⟩

end Brotli.Decoder
