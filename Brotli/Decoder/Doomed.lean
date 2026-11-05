import Brotli.Decoder.OrderSpec

/-!
# A doomed prefix stays within its meta-block

Where the spec's reading in order of a stream's bytes has finished a meta-block, every prefix of the bytes before that
point has a valid continuation: the stream can end there. So a prefix with no valid continuation keeps the reading in
order of every stream it starts short of the end of the meta-block it ends in, and a decoder that has used it stands
within that meta-block.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### Bits back to bytes -/

/-- Bits as a number, least significant first. -/
private def ofBits : List Bool → Nat
  | [] => 0
  | b :: l => b.toNat + 2 * ofBits l

private theorem ofBits_lt : ∀ l : List Bool, ofBits l < 2 ^ l.length
  | [] => by simp [ofBits]
  | b :: l => by
    have := ofBits_lt l
    simp only [ofBits, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

private theorem lowBits_ofBits : ∀ l : List Bool, lowBits (ofBits l) l.length = l
  | [] => rfl
  | b :: l => by
    simp only [ofBits, List.length_cons, lowBits]
    have e : (b.toNat + 2 * ofBits l) / 2 = ofBits l := by cases b <;> simp <;> omega
    rw [e, lowBits_ofBits l]
    cases b <;> simp [Nat.testBit_zero]

/-- Bits that make whole bytes are the bits of some bytes. -/
theorem bits_onto : ∀ (n : Nat) (l : List Bool), l.length = 8 * n → ∃ e : List UInt8, bits e = l
  | 0, l, h => ⟨[], by rw [List.eq_nil_of_length_eq_zero (by omega : l.length = 0)]; rfl⟩
  | n + 1, l, h => by
    obtain ⟨e, he⟩ := bits_onto n (l.drop 8) (by rw [List.length_drop]; omega)
    have h8 : (l.take 8).length = 8 := by rw [List.length_take]; omega
    have hv : (UInt8.ofNat (ofBits (l.take 8))).toNat = ofBits (l.take 8) :=
      UInt8.toNat_ofNat_of_lt' (by have := ofBits_lt (l.take 8); rw [h8] at this; exact this)
    refine ⟨UInt8.ofNat (ofBits (l.take 8)) :: e, ?_⟩
    rw [bits_cons, he, hv]
    have := lowBits_ofBits (l.take 8)
    rw [h8] at this
    rw [this, List.take_append_drop]

/-! ### The reading in order, with other bits after what it read -/

/-- The reading in order reaches the same place with other bits after what it read, of the same length modulo 8. -/
theorem reach_rebit {P E : Type} {step : P → List Bool → ORes P E} (hs : ∀ p, NFaith (step p)) {p q : P} {bs c : List Bool}
    (h : Reach step p bs q c) : ∀ v t : List Bool, bs = v ++ c → t.length % 8 = c.length % 8 → Reach step p (v ++ t) q t := by
  induction h with
  | refl =>
    intro v t h1 _
    obtain rfl : v = [] := List.eq_nil_of_length_eq_zero (by
      have := congrArg List.length h1
      simp only [List.length_append] at this
      omega)
    exact .refl _ _
  | @next p bs p' bs' q c hst hr ih =>
    intro v t h1 ht
    obtain ⟨u, hu, hk⟩ := hs p bs p' bs' hst
    obtain ⟨w, hw⟩ := reach_suffix hs hr
    have hv : v = u ++ w := List.append_cancel_right (by rw [← h1, hu, hw, List.append_assoc])
    subst hv
    refine .next ?_ (ih w t hw ht)
    rw [List.append_assoc]
    exact hk (w ++ t) (by rw [hw]; simp only [List.length_append]; omega)

/-! ### Where a meta-block is finished -/

/-- A place where the reading in order has finished a meta-block: the next meta-block's start, or the stream's end with
its fill bits read. -/
def SBoundary : SPhase → List Bool → Prop
  | .mblock _ _, _ => True
  | .ended _, c => c.length % 8 = 0
  | _, _ => False

/-- At a meta-block's start, ISLAST and ISLASTEMPTY set, then zero fill bits, end the stream. -/
private theorem end_now (w : Nat) (st : StreamState) (pad : Nat) (hp : pad < 8) :
    srest specSem (.mblock w st) (true :: true :: List.replicate pad false) = some (st.output.reverse.map Nat.toUInt8) := by
  have he : readEnd (List.replicate pad false) = some () :=
    (show ∀ p < 8, readEnd (List.replicate p false) = some () by decide) pad hp
  show metaK w st _ = _
  rw [metaK_step]
  simp [readMetaBlock, readInt, amK, endOf, he]

/-- Where the reading in order of a stream's bytes has finished a meta-block, every prefix of the bytes before that point
has a valid continuation. -/
theorem boundary_completes {L : List UInt8} {q : SPhase} {c : List Bool} (h : Reach sStep .wbits (bits L) q c)
    (hb : SBoundary q c) {n : Nat} (hn : 8 * n + c.length ≤ 8 * L.length) :
    ∃ t y : List UInt8, decode (L.take n ++ t) = some y := by
  obtain ⟨v, hv⟩ := reach_suffix nfaith_sStep h
  have hlen : v.length + c.length = 8 * L.length := by
    have := congrArg List.length hv
    rw [bits_length, List.length_append] at this
    omega
  obtain ⟨k, r, hkr, hr8⟩ : ∃ k r, v.length = 8 * k + r ∧ r < 8 := ⟨v.length / 8, v.length % 8, by omega, by omega⟩
  have hkn : n ≤ k := by omega
  -- the bits read: whole bytes, then the first `r` bits of the next
  obtain ⟨d, hd⟩ : ∃ d : UInt8, v = bits (L.take k) ++ lowBits d.toNat r := by
    have e1 : (bits L).take v.length = v := by rw [hv]; simp
    have e2 : bits L = bits (L.take k) ++ bits (L.drop k) := by rw [← bits_append, List.take_append_drop]
    have e3 : (bits (L.take k)).length = 8 * k := by rw [bits_length, List.length_take]; omega
    rw [e2, hkr, List.take_append, List.take_of_length_le (by omega), e3, show 8 * k + r - 8 * k = r by omega] at e1
    cases e4 : L.drop k with
    | nil =>
      have := List.drop_eq_nil_iff.mp e4
      obtain rfl : r = 0 := by omega
      rw [e4] at e1
      exact ⟨0, by rw [← e1]; rfl⟩
    | cons b rest =>
      rw [e4, bits_cons, List.take_append_of_le_length (by rw [lowBits_length]; omega), lowBits_take r 8 _ (by omega)] at e1
      exact ⟨b, e1.symm⟩
  have hcut : L.take n ++ (L.drop n).take (k - n) = L.take k := by rw [← List.take_add, Nat.add_sub_of_le hkn]
  cases q with
  | mblock w st =>
    have h1 := reach_rebit nfaith_sStep h v (true :: true :: List.replicate ((14 - r) % 8) false) hv
      (by simp only [List.length_cons, List.length_replicate]; omega)
    obtain ⟨e, he⟩ := bits_onto ((r + 2 + (14 - r) % 8) / 8) (lowBits d.toNat r ++ true :: true :: List.replicate ((14 - r) % 8) false)
      (by simp only [List.length_append, lowBits_length, List.length_cons, List.length_replicate]; omega)
    have h2 : v ++ true :: true :: List.replicate ((14 - r) % 8) false = bits (L.take k ++ e) := by
      rw [bits_append, he, hd, List.append_assoc]
    rw [h2] at h1
    refine ⟨(L.drop n).take (k - n) ++ e, st.output.reverse.map Nat.toUInt8, ?_⟩
    rw [← List.append_assoc, hcut, decode_reach h1]
    exact end_now w st _ (by omega)
  | ended st =>
    have hc : c.length % 8 = 0 := hb
    obtain rfl : r = 0 := by omega
    have h1 := reach_rebit nfaith_sStep h v [] hv (by simp only [List.length_nil]; omega)
    rw [hd] at h1
    simp only [lowBits, List.append_nil] at h1
    refine ⟨(L.drop n).take (k - n), st.output.reverse.map Nat.toUInt8, ?_⟩
    rw [hcut]
    exact decode_of_exit h1 rfl
  | wbits => exact hb.elim
  | skip => exact hb.elim
  | raw => exact hb.elim
  | hdr => exact hb.elim
  | cmds => exact hb.elim

/-- A prefix with no valid continuation: the reading in order of any stream it starts finishes no meta-block at or after
the prefix's end. -/
theorem doomed_noBoundary {x : List UInt8} {n : Nat} (hd : ∀ t, decode (x.take n ++ t) = none) {L : List UInt8}
    (hL : x.take n <+: L) {q : SPhase} {c : List Bool} (h : Reach sStep .wbits (bits L) q c) (hb : SBoundary q c) :
    8 * L.length < 8 * (x.take n).length + c.length := by
  refine Nat.lt_of_not_le fun hle => ?_
  obtain ⟨u, rfl⟩ := hL
  obtain ⟨t, y, hy⟩ := boundary_completes h hb (n := (x.take n).length) (by omega)
  rw [List.take_left] at hy
  rw [hd] at hy
  cases hy

/-! ### The decoder -/

/-- A decoder that has used a prefix with no valid continuation, and asks for input or output space, stands where the spec's
reading in order of the bytes it has used comes to, and every meta-block that reading finishes ends before the prefix's
end. Asking for input, it is within 54 bits of where that reading stops for too few bits. -/
theorem decoder_doomed {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R)
    (hs : R.status = .needsInput ∨ R.status = .needsOutput) {n : Nat} (hd : ∀ t, decode (x.take n ++ t) = none)
    (hn : n ≤ R.read) :
    ∃ p, Reach sStep .wbits (bits (x.take R.read)) p R.state.val.held ∧
      (∀ q c, Reach sStep .wbits (bits (x.take R.read)) q c → SBoundary q c → 8 * R.read < 8 * n + c.length) ∧
      (R.status = .needsInput → ∃ q c, Reach sStep p R.state.val.held q c ∧ sStep q c = .short ∧ c.length < 54) := by
  have hrl := (top_inv h).read
  have hlen : (x.take R.read).length = R.read := List.length_take_of_le hrl
  have hlen' : (x.take n).length = n := List.length_take_of_le (by omega)
  have hpre : x.take n <+: x.take R.read := by
    have := List.take_prefix n (x.take R.read)
    rwa [List.take_take, Nat.min_eq_left hn] at this
  have hno : ∀ q c, Reach sStep .wbits (bits (x.take R.read)) q c → SBoundary q c → 8 * R.read < 8 * n + c.length := by
    intro q c hq hb
    have := doomed_noBoundary hd hpre hq hb
    rwa [hlen, hlen'] at this
  rcases hs with hs | hs
  · obtain ⟨p, h1, _, _, q, c, h2, _, h3⟩ := decoder_pausesInOrder h hs
    refine ⟨p, h1, hno, fun _ => ?_⟩
    rcases h3 with ⟨h3, h4⟩ | ⟨y, _, hy⟩
    · exact ⟨q, c, h2, h3, h4⟩
    · obtain ⟨u, hu⟩ := hpre
      rw [← hu, hd] at hy
      cases hy
  · obtain ⟨p, h1, _⟩ := decoder_waits h hs
    exact ⟨p, h1, hno, fun e => by rw [hs] at e; cases e⟩

end Brotli.Decoder
