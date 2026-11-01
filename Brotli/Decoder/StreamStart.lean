import Brotli.Decoder.StreamRest

/-!
# Small reads at the stream's level

WBITS, and the start of a meta-block up to its ISUNCOMPRESSED or its metadata length, each all or nothing.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

private theorem not_le_lt4 {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

private theorem eq_toNat4 {x n : UInt64} (h : x = n) : x.toNat = n.toNat := by rw [h]

private theorem ne_toNat4 {x n : UInt64} (h : ¬ x = n) : ¬ x.toNat = n.toNat := fun e => h (UInt64.toNat_inj.mp e)

/-! ### The start of a meta-block -/

/-- A meta-block's start, as a read's values: `a` is 0 for the last empty block, 1 for metadata and 2 for data; `b` is ISLAST;
`c` is the skip or MLEN; `d` is ISUNCOMPRESSED. -/
def msValue (r : Rd) : MetaStart :=
  if r.a = 0 then .lastEmpty
  else if r.a = 1 then .metadata (r.b != 0) r.c.toNat
  else .data (r.b != 0) r.c.toNat (r.d != 0)

/-- From ISUNCOMPRESSED. -/
@[inline] def msUncFast (last : UInt64) (mlen : UInt64) (b0 b : BitBuffer) : Rd :=
  if last != 0 then Rd.ok b 2 last mlen 0 0
  else if 1 ≤ b.count then Rd.ok (b.drop 1) 2 last mlen (b.peek 1) 0
  else Rd.short b0

/-- From MLEN's bits. -/
@[inline] def msLenFast (last n : UInt64) (b0 b : BitBuffer) : Rd :=
  let bits := n * 4
  if bits ≤ b.count then
    let v := b.peek bits
    if 4 < n ∧ v >>> ((n - 1) * 4) = 0 then Rd.bad b0
    else msUncFast last (v + 1) b0 (b.drop bits)
  else Rd.short b0

/-- From MSKIPLEN's bits. -/
@[inline] def msSkipFast (last n : UInt64) (b0 b : BitBuffer) : Rd :=
  let bits := n * 8
  if bits ≤ b.count then
    let v := b.peek bits
    if 1 < n ∧ v >>> ((n - 1) * 8) = 0 then Rd.bad b0
    else Rd.ok (b.drop bits) 1 last (if n = 0 then 0 else v + 1) 0 0
  else Rd.short b0

/-- From MNIBBLES. -/
@[inline] def msBodyFast (last : UInt64) (b0 b : BitBuffer) : Rd :=
  if 2 ≤ b.count then
    let v := b.peek 2
    let b1 := b.drop 2
    if v = 3 then
      if 1 ≤ b1.count then
        if b1.peek 1 ≠ 0 then Rd.bad b0
        else
          let b2 := b1.drop 1
          if 2 ≤ b2.count then msSkipFast last (b2.peek 2) b0 (b2.drop 2)
          else Rd.short b0
      else Rd.short b0
    else msLenFast last (v + 4) b0 b1
  else Rd.short b0

/-- Reads the start of a meta-block. -/
def metaStartFast (b0 : BitBuffer) : Rd :=
  if 1 ≤ b0.count then
    let l := b0.peek 1
    let b1 := b0.drop 1
    if l = 0 then msBodyFast 0 b0 b1
    else if 1 ≤ b1.count then
      if b1.peek 1 = 1 then Rd.ok (b1.drop 1) 0 0 0 0 0
      else msBodyFast 1 b0 (b1.drop 1)
    else Rd.short b0
  else Rd.short b0

private theorem peek4 (b : BitBuffer) {k : UInt64} (hk : k.toNat < 64) (h : k.toNat ≤ 24) : (b.peek k).toNat < 2 ^ 24 := by
  have h1 := peek_lt b hk
  have h2 : 2 ^ k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) h
  omega

private theorem msValue_data (b : BitBuffer) (l m d e : UInt64) :
    msValue (Rd.ok b 2 l m d e) = .data (l != 0) m.toNat (d != 0) := rfl

private theorem msValue_meta (b : BitBuffer) (l m d e : UInt64) :
    msValue (Rd.ok b 1 l m d e) = .metadata (l != 0) m.toNat := rfl

theorem msUncFast_ok {last mlen : UInt64} {b0 b : BitBuffer} {room : Nat} (hw : b.Wf) (hr : 1 ≤ room) :
    ROk (msUnc (last != 0) mlen.toNat) b b0 room (msUncFast last mlen b0 b) (msValue (msUncFast last mlen b0 b)) := by
  unfold msUncFast msUnc
  cases hL : (last != 0) with
  | true =>
    simp only [↓reduceIte]
    refine ROk.done hw (fun f => ?_) _ _ _ _ _
    rw [msValue_data, hL]
    rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    by_cases h1 : 1 ≤ b.count
    · rw [ite_eq_left h1]
      refine ROk.intOk (k := 1) (by decide) h1 ?_
      refine ROk.done (drop_wf' hw (by decide) h1) (fun f => ?_) _ _ _ _ _
      rw [msValue_data, hL]
      have hp : (b.peek 1).toNat < 2 := peek_lt b (k := 1) (by decide)
      have hiff : decide ((b.peek 1).toNat = 1) = (b.peek 1 != 0) := by
        by_cases h0 : b.peek 1 = 0
        · have e : (b.peek 1).toNat = 0 := eq_toNat4 h0
          simp [h0]
        · have e : (b.peek 1).toNat ≠ 0 := ne_toNat4 h0
          have e1 : (b.peek 1).toNat = 1 := by omega
          simp [h0, e1]
      show some ((MetaStart.data false mlen.toNat (decide ((b.peek 1).toNat = 1))), _) = _
      rw [hiff]
    · rw [ite_eq_right h1]
      exact ROk.intShort (not_le_lt4 h1) (by omega)

theorem msLenFast_ok {last n : UInt64} {b0 b : BitBuffer} {room : Nat} (hw : b.Wf) (hn : n.toNat ≤ 6) (hr : n.toNat * 4 + 1 ≤ room) :
    ROk (msLen (last != 0) n.toNat) b b0 room (msLenFast last n b0 b) (msValue (msLenFast last n b0 b)) := by
  have hbits : (n * 4).toNat = n.toNat * 4 := by
    rw [UInt64.toNat_mul, show (4 : UInt64).toNat = 4 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  unfold msLenFast msLen
  dsimp only
  rw [← hbits]
  by_cases h1 : n * 4 ≤ b.count
  · rw [ite_eq_left h1]
    refine ROk.intOk (by omega) h1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := n * 4) (by omega) h1
    have hv := peek4 b (k := n * 4) (by omega) (by omega)
    generalize b.peek (n * 4) = v at hv ⊢
    generalize b.drop (n * 4) = b1 at hw1 ⊢
    have hshift : 1 ≤ n.toNat → (v >>> ((n - 1) * 4)).toNat = v.toNat >>> ((n.toNat - 1) * 4) := by
      intro hn1
      have h1n : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [show (1 : UInt64).toNat = 1 from rfl]
        omega))
      have h4n : ((n - 1) * 4).toNat = (n.toNat - 1) * 4 := by
        rw [UInt64.toNat_mul, h1n, show (4 : UInt64).toNat = 4 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.toNat_shiftRight, h4n, Nat.mod_eq_of_lt (by omega)]
    have hcond : (4 < n ∧ v >>> ((n - 1) * 4) = 0) ↔ (4 < n.toNat ∧ v.toNat >>> ((n.toNat - 1) * 4) = 0) := by
      constructor
      · rintro ⟨h4, h0⟩
        have h4' : 4 < n.toNat := UInt64.lt_iff_toNat_lt.mp h4
        exact ⟨h4', by rw [← hshift (by omega), h0]; rfl⟩
      · rintro ⟨h4, h0⟩
        exact ⟨UInt64.lt_iff_toNat_lt.mpr h4, UInt64.toNat_inj.mp (by rw [hshift (by omega), h0]; rfl)⟩
    by_cases hc : 4 < n ∧ v >>> ((n - 1) * 4) = 0
    · rw [ite_eq_left hc]
      simp only [hcond.mp hc]
      exact ROk.reject (fun _ => rfl)
    · rw [ite_eq_right hc]
      have hc' : ¬ (4 < n.toNat ∧ v.toNat >>> ((n.toNat - 1) * 4) = 0) := fun h => hc (hcond.mpr h)
      simp only [hc', ↓reduceIte]
      have hsum : (v + 1).toNat = v.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hsum]
      exact msUncFast_ok hw1 (by omega)
  · rw [ite_eq_right h1]
    exact ROk.intShort (not_le_lt4 h1) (by rw [hbits]; omega)

theorem msSkipFast_ok {last n : UInt64} {b0 b : BitBuffer} {room : Nat} (hw : b.Wf) (hn : n.toNat ≤ 3) (hr : n.toNat * 8 ≤ room) :
    ROk (msSkip (last != 0) n.toNat) b b0 room (msSkipFast last n b0 b) (msValue (msSkipFast last n b0 b)) := by
  have hbits : (n * 8).toNat = n.toNat * 8 := by
    rw [UInt64.toNat_mul, show (8 : UInt64).toNat = 8 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  unfold msSkipFast msSkip
  dsimp only
  rw [← hbits]
  by_cases h1 : n * 8 ≤ b.count
  · rw [ite_eq_left h1]
    refine ROk.intOk (by omega) h1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := n * 8) (by omega) h1
    have hv := peek4 b (k := n * 8) (by omega) (by omega)
    generalize b.peek (n * 8) = v at hv ⊢
    generalize b.drop (n * 8) = b1 at hw1 ⊢
    have hshift : 1 ≤ n.toNat → (v >>> ((n - 1) * 8)).toNat = v.toNat >>> ((n.toNat - 1) * 8) := by
      intro hn1
      have h1n : (n - 1).toNat = n.toNat - 1 := UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [show (1 : UInt64).toNat = 1 from rfl]
        omega))
      have h8n : ((n - 1) * 8).toNat = (n.toNat - 1) * 8 := by
        rw [UInt64.toNat_mul, h1n, show (8 : UInt64).toNat = 8 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      rw [UInt64.toNat_shiftRight, h8n, Nat.mod_eq_of_lt (by omega)]
    have hcond : (1 < n ∧ v >>> ((n - 1) * 8) = 0) ↔ (1 < n.toNat ∧ v.toNat >>> ((n.toNat - 1) * 8) = 0) := by
      constructor
      · rintro ⟨h4, h0⟩
        have h4' : 1 < n.toNat := UInt64.lt_iff_toNat_lt.mp h4
        exact ⟨h4', by rw [← hshift (by omega), h0]; rfl⟩
      · rintro ⟨h4, h0⟩
        exact ⟨UInt64.lt_iff_toNat_lt.mpr h4, UInt64.toNat_inj.mp (by rw [hshift (by omega), h0]; rfl)⟩
    by_cases hc : 1 < n ∧ v >>> ((n - 1) * 8) = 0
    · rw [ite_eq_left hc]
      simp only [hcond.mp hc]
      exact ROk.reject (fun _ => rfl)
    · rw [ite_eq_right hc]
      have hc' : ¬ (1 < n.toNat ∧ v.toNat >>> ((n.toNat - 1) * 8) = 0) := fun h => hc (hcond.mpr h)
      simp only [hc', ↓reduceIte]
      refine ROk.done hw1 (fun f => ?_) _ _ _ _ _
      rw [msValue_meta]
      have hval : (if n = 0 then 0 else v + 1).toNat = if n.toNat = 0 then 0 else v.toNat + 1 := by
        by_cases hz : n = 0
        · have hz' : n.toNat = 0 := eq_toNat4 hz
          rw [ite_eq_left hz, ite_eq_left hz']
          rfl
        · have hz' : ¬ n.toNat = 0 := ne_toNat4 hz
          rw [ite_eq_right hz, ite_eq_right hz', UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
      rw [hval]
  · rw [ite_eq_right h1]
    exact ROk.intShort (not_le_lt4 h1) (by rw [hbits]; exact hr)

theorem msBodyFast_ok {last : UInt64} {b0 b : BitBuffer} {room : Nat} (hw : b.Wf) (hr : 29 ≤ room) :
    ROk (msBody (last != 0)) b b0 room (msBodyFast last b0 b) (msValue (msBodyFast last b0 b)) := by
  have h2n : (2 : UInt64).toNat = 2 := rfl
  have h1n : (1 : UInt64).toNat = 1 := rfl
  unfold msBodyFast msBody
  dsimp only
  by_cases h2 : 2 ≤ b.count
  · rw [ite_eq_left h2]
    refine ROk.intOk (k := 2) (by decide) h2 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    have hv4 : (b.peek 2).toNat < 4 := peek_lt b (k := 2) (by decide)
    generalize b.peek 2 = v at hv4 ⊢
    generalize b.drop 2 = b1 at hw1 ⊢
    by_cases h3 : v = 3
    · rw [ite_eq_left h3]
      have e : v.toNat = 3 := eq_toNat4 h3
      simp only [e, ↓reduceIte]
      by_cases h1 : 1 ≤ b1.count
      · rw [ite_eq_left h1]
        refine ROk.intOk (k := 1) (by decide) h1 ?_
        dsimp only
        have hw2 := drop_wf' hw1 (k := 1) (by decide) h1
        by_cases hres : b1.peek 1 ≠ 0
        · rw [ite_eq_left hres]
          have : (b1.peek 1).toNat ≠ 0 := ne_toNat4 hres
          simp only [this, ↓reduceIte, ne_eq, not_false_eq_true]
          exact ROk.reject (fun _ => rfl)
        · rw [ite_eq_right hres]
          have h0 : b1.peek 1 = 0 := by simpa using hres
          have : (b1.peek 1).toNat = 0 := eq_toNat4 h0
          simp only [this, ne_eq, not_true_eq_false, ↓reduceIte]
          generalize b1.drop 1 = b2 at hw2 ⊢
          by_cases h22 : 2 ≤ b2.count
          · rw [ite_eq_left h22]
            refine ROk.intOk (k := 2) (by decide) h22 ?_
            dsimp only
            have hw3 := drop_wf' hw2 (k := 2) (by decide) h22
            have hn4 : (b2.peek 2).toNat < 4 := peek_lt b2 (k := 2) (by decide)
            exact msSkipFast_ok hw3 (by omega) (by rw [h2n, h1n]; omega)
          · rw [ite_eq_right h22]
            exact ROk.intShort (not_le_lt4 h22) (by rw [h2n, h1n]; omega)
      · rw [ite_eq_right h1]
        exact ROk.intShort (not_le_lt4 h1) (by rw [h2n]; omega)
    · rw [ite_eq_right h3]
      have e : ¬ v.toNat = 3 := ne_toNat4 h3
      simp only [e, ↓reduceIte]
      have hsum : (v + 4).toNat = v.toNat + 4 := by
        rw [UInt64.toNat_add, show (4 : UInt64).toNat = 4 from rfl]
        exact Nat.mod_eq_of_lt (by omega)
      rw [← hsum]
      exact msLenFast_ok hw1 (by omega) (by rw [h2n, hsum]; omega)
  · rw [ite_eq_right h2]
    exact ROk.intShort (not_le_lt4 h2) (by omega)

/-! ### WBITS -/

/-- `readWBITS`, as a chain of reads. -/
def wbitsChain (bs : List Bool) : Option (Nat × List Bool) :=
  readInt 1 bs >>= fun a =>
    if a.1 = 0 then some (16, a.2)
    else readInt 3 a.2 >>= fun b =>
      if b.1 ≠ 0 then some (17 + b.1, b.2)
      else readInt 3 b.2 >>= fun c =>
        if c.1 = 0 then some (17, c.2)
        else if c.1 = 1 then none
        else some (8 + c.1, c.2)

theorem wbitsChain_eq (bs : List Bool) : readWBITS bs = wbitsChain bs := by
  rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, r⟩⟩⟩⟩⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> (try cases c) <;> (try cases d) <;> (try cases e) <;> (try cases f) <;> (try cases g) <;> rfl

/-- Reads WBITS, into `a`. -/
def wbitsFast (b0 : BitBuffer) : Rd :=
  if 1 ≤ b0.count then
    let b1 := b0.drop 1
    if b0.peek 1 = 0 then Rd.ok b1 16 0 0 0 0
    else if 3 ≤ b1.count then
      let v := b1.peek 3
      let b2 := b1.drop 3
      if v ≠ 0 then Rd.ok b2 (17 + v) 0 0 0 0
      else if 3 ≤ b2.count then
        let c := b2.peek 3
        let b3 := b2.drop 3
        if c = 0 then Rd.ok b3 17 0 0 0 0
        else if c = 1 then Rd.bad b0
        else Rd.ok b3 (8 + c) 0 0 0 0
      else Rd.short b0
    else Rd.short b0
  else Rd.short b0

theorem wbitsFast_ok {b0 : BitBuffer} (hw : b0.Wf) : ROk readWBITS b0 b0 7 (wbitsFast b0) (wbitsFast b0).a.toNat := by
  have h1n : (1 : UInt64).toNat = 1 := rfl
  have h3n : (3 : UInt64).toNat = 3 := rfl
  refine ROk.congr ?_ wbitsChain_eq
  unfold wbitsFast wbitsChain
  dsimp only
  by_cases h1 : 1 ≤ b0.count
  · rw [ite_eq_left h1]
    refine ROk.intOk (k := 1) (by decide) h1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 1) (by decide) h1
    generalize b0.drop 1 = b1 at hw1 ⊢
    by_cases ha : b0.peek 1 = 0
    · rw [ite_eq_left ha]
      have e : (b0.peek 1).toNat = 0 := eq_toNat4 ha
      simp only [e, ↓reduceIte]
      exact ROk.done hw1 (fun f => rfl) _ _ _ _ _
    · rw [ite_eq_right ha]
      have e : ¬ (b0.peek 1).toNat = 0 := ne_toNat4 ha
      simp only [e, ↓reduceIte]
      by_cases h3 : 3 ≤ b1.count
      · rw [ite_eq_left h3]
        refine ROk.intOk (k := 3) (by decide) h3 ?_
        dsimp only
        have hw2 := drop_wf' hw1 (k := 3) (by decide) h3
        have hv : (b1.peek 3).toNat < 8 := peek_lt b1 (k := 3) (by decide)
        generalize b1.drop 3 = b2 at hw2 ⊢
        generalize b1.peek 3 = v at hv ⊢
        by_cases hb : v ≠ 0
        · rw [ite_eq_left hb]
          have e2 : v.toNat ≠ 0 := ne_toNat4 hb
          simp only [ne_eq, e2, not_false_eq_true, ↓reduceIte]
          have hs : (17 + v).toNat = 17 + v.toNat := by
            rw [UInt64.toNat_add, show (17 : UInt64).toNat = 17 from rfl]
            exact Nat.mod_eq_of_lt (by omega)
          refine ROk.done hw2 (fun f => ?_) _ _ _ _ _
          simp only [Rd.ok]
          rw [hs]
        · rw [ite_eq_right hb]
          have h0 : v = 0 := by simpa using hb
          have e2 : v.toNat = 0 := eq_toNat4 h0
          simp only [e2, ne_eq, not_true_eq_false, ↓reduceIte]
          by_cases h32 : 3 ≤ b2.count
          · rw [ite_eq_left h32]
            refine ROk.intOk (k := 3) (by decide) h32 ?_
            dsimp only
            have hw3 := drop_wf' hw2 (k := 3) (by decide) h32
            have hc8 : (b2.peek 3).toNat < 8 := peek_lt b2 (k := 3) (by decide)
            generalize b2.drop 3 = b3 at hw3 ⊢
            generalize b2.peek 3 = c at hc8 ⊢
            by_cases hc0 : c = 0
            · rw [ite_eq_left hc0]
              have e3 : c.toNat = 0 := eq_toNat4 hc0
              simp only [e3, ↓reduceIte]
              exact ROk.done hw3 (fun f => rfl) _ _ _ _ _
            · rw [ite_eq_right hc0]
              have e3 : ¬ c.toNat = 0 := ne_toNat4 hc0
              simp only [e3, ↓reduceIte]
              by_cases hc1 : c = 1
              · rw [ite_eq_left hc1]
                have e4 : c.toNat = 1 := eq_toNat4 hc1
                simp only [e4, ↓reduceIte]
                exact ROk.reject (fun _ => rfl)
              · rw [ite_eq_right hc1]
                have e4 : ¬ c.toNat = 1 := ne_toNat4 hc1
                simp only [e4, ↓reduceIte]
                have hs : (8 + c).toNat = 8 + c.toNat := by
                  rw [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]
                  exact Nat.mod_eq_of_lt (by omega)
                refine ROk.done hw3 (fun f => ?_) _ _ _ _ _
                simp only [Rd.ok]
                rw [hs]
          · rw [ite_eq_right h32]
            exact ROk.intShort (not_le_lt4 h32) (by rw [h1n, h3n]; omega)
      · rw [ite_eq_right h3]
        exact ROk.intShort (not_le_lt4 h3) (by rw [h1n]; omega)
  · rw [ite_eq_right h1]
    exact ROk.intShort (not_le_lt4 h1) (by omega)

theorem metaStartFast_ok {b0 : BitBuffer} (hw : b0.Wf) : ROk metaStart b0 b0 31 (metaStartFast b0) (msValue (metaStartFast b0)) := by
  have h1n : (1 : UInt64).toNat = 1 := rfl
  unfold metaStartFast metaStart
  dsimp only
  by_cases h1 : 1 ≤ b0.count
  · rw [ite_eq_left h1]
    refine ROk.intOk (k := 1) (by decide) h1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 1) (by decide) h1
    generalize b0.drop 1 = b1 at hw1 ⊢
    by_cases hl : b0.peek 1 = 0
    · rw [ite_eq_left hl]
      have : (b0.peek 1).toNat = 0 := eq_toNat4 hl
      simp only [this, ↓reduceIte]
      exact msBodyFast_ok (last := 0) hw1 (by rw [h1n]; omega)
    · rw [ite_eq_right hl]
      have : ¬ (b0.peek 1).toNat = 0 := ne_toNat4 hl
      simp only [this, ↓reduceIte]
      by_cases h2 : 1 ≤ b1.count
      · rw [ite_eq_left h2]
        refine ROk.intOk (k := 1) (by decide) h2 ?_
        dsimp only
        have hw2 := drop_wf' hw1 (k := 1) (by decide) h2
        by_cases he : b1.peek 1 = 1
        · rw [ite_eq_left he]
          have e : (b1.peek 1).toNat = 1 := eq_toNat4 he
          simp only [e, ↓reduceIte]
          exact ROk.done hw2 (fun f => rfl) _ _ _ _ _
        · rw [ite_eq_right he]
          have e : ¬ (b1.peek 1).toNat = 1 := ne_toNat4 he
          simp only [e, ↓reduceIte]
          exact msBodyFast_ok (last := 1) hw2 (by rw [h1n]; omega)
      · rw [ite_eq_right h2]
        exact ROk.intShort (not_le_lt4 h2) (by rw [h1n]; omega)
  · rw [ite_eq_right h1]
    exact ROk.intShort (not_le_lt4 h1) (by omega)

end Brotli.Decoder
