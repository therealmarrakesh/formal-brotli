import Brotli.Decoder.BitBuffer
import Brotli.Properties.Complete

/-!
# Which symbol a bit pattern decodes to

The theory behind table lookup. Stream bits arrive least significant first in the bit buffer, and a prefix code
reads its first bit as the most significant, so a code word is the bit reverse of the buffer's low bits. `Hit` says
that the low `l` bits of `w` are the code word of symbol `s`. Every pattern has exactly one hit, and a hit is what
`decodeSymbol` returns, so a table only has to give each pattern its hit.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- The low `l` bits of `w`, reversed. -/
def revBits : Nat → Nat → Nat
  | 0, _ => 0
  | l + 1, w => (w % 2) * 2 ^ l + revBits l (w / 2)

theorem revBits_lt : ∀ (l w : Nat), revBits l w < 2 ^ l
  | 0, _ => by simp [revBits]
  | l + 1, w => by
    have ih := revBits_lt l (w / 2)
    have hb : w % 2 ≤ 1 := by omega
    have hm : (w % 2) * 2 ^ l ≤ 1 * 2 ^ l := Nat.mul_le_mul_right _ hb
    simp only [revBits]
    rw [Nat.pow_succ]
    omega

private theorem toNat_testBit_zero' (w : Nat) : (w.testBit 0).toNat = w % 2 := by
  rw [Nat.testBit_zero]
  have : w % 2 = 0 ∨ w % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

/-- Reading `l` of the low bits as a prefix code gives their reverse, and leaves the bits above. -/
theorem readCode_lowBits (f : List Bool) : ∀ (l n w : Nat), l ≤ n →
    readCode l (lowBits w n ++ f) = some (revBits l w, lowBits (w / 2 ^ l) (n - l) ++ f)
  | 0, n, w, _ => by simp [readCode, revBits]
  | l + 1, 0, _, h => by omega
  | l + 1, n + 1, w, h => by
    have ih := readCode_lowBits f l n (w / 2) (by omega)
    simp only [lowBits, List.cons_append, readCode, ih, Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [toNat_testBit_zero']
      rfl
    · rw [Nat.div_div_eq_div_mul, Nat.pow_succ', Nat.add_sub_add_right]

/-- The low `n` bits are the low `l` bits and then the next `n - l`. -/
theorem lowBits_split : ∀ (l n w : Nat), l ≤ n → lowBits w n = lowBits w l ++ lowBits (w / 2 ^ l) (n - l)
  | 0, n, w, _ => by simp [lowBits]
  | l + 1, 0, _, h => by omega
  | l + 1, n + 1, w, h => by
    simp only [lowBits, List.cons_append, List.cons.injEq, true_and]
    rw [lowBits_split l n (w / 2) (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ', Nat.add_sub_add_right]

/-- Numbers below `2 ^ l` with the same low bits are equal. -/
theorem lowBits_inj {l a b : Nat} (ha : a < 2 ^ l) (hb : b < 2 ^ l) (h : lowBits a l = lowBits b l) : a = b := by
  have ra := readInt_lowBits [] l l a (Nat.le_refl _)
  have rb := readInt_lowBits [] l l b (Nat.le_refl _)
  simp only [List.append_nil] at ra rb
  rw [h, rb] at ra
  simp only [Option.some.injEq, Prod.mk.injEq] at ra
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at ra
  exact ra.1.symm

/-- The bits of a reverse are the reversed bits. -/
theorem lowBits_revBits : ∀ (l w : Nat), lowBits (revBits l w) l = (lowBits w l).reverse
  | 0, _ => rfl
  | l + 1, w => by
    have h := lowBits_add l (revBits l (w / 2)) (w % 2) 1 (revBits_lt l _)
    have hsum : revBits (l + 1) w = revBits l (w / 2) + 2 ^ l * (w % 2) := by
      simp only [revBits]
      rw [Nat.mul_comm, Nat.add_comm]
    rw [hsum, h, lowBits_revBits l (w / 2)]
    simp only [lowBits, List.reverse_cons]
    congr 2
    simp only [Nat.testBit_zero]
    have : w % 2 = 0 ∨ w % 2 = 1 := by omega
    rcases this with h | h <;> simp [h]

/-- Reversing twice gives back a number that fits. -/
theorem revBits_revBits {l c : Nat} (h : c < 2 ^ l) : revBits l (revBits l c) = c := by
  apply lowBits_inj (revBits_lt l _) h
  rw [lowBits_revBits, lowBits_revBits, List.reverse_reverse]

/-- `revBits` looks only at the low `l` bits. -/
theorem revBits_mod (l w : Nat) : revBits l (w % 2 ^ l) = revBits l w := by
  apply lowBits_inj (revBits_lt l _) (revBits_lt l _)
  rw [lowBits_revBits, lowBits_revBits, lowBits_mod]

/-- `revBits` of a wider slot looks only at the bits it needs. -/
theorem revBits_mod_of_le {l W : Nat} (h : l ≤ W) (w : Nat) : revBits l (w % 2 ^ W) = revBits l w := by
  apply lowBits_inj (revBits_lt l _) (revBits_lt l _)
  rw [lowBits_revBits, lowBits_revBits, ← lowBits_take l W _ h, lowBits_mod, lowBits_take l W _ h]

/-- A slot's low bits are a code word exactly when they are the reverse of it. -/
theorem revBits_eq_iff {l c w : Nat} (h : c < 2 ^ l) : revBits l w = c ↔ w % 2 ^ l = revBits l c := by
  constructor
  · intro e
    rw [← e, ← revBits_mod l w, revBits_revBits (Nat.mod_lt _ (Nat.two_pow_pos _))]
  · intro e
    rw [← revBits_mod l w, e, revBits_revBits h]

/-- The low `l` bits of `w` are the code word of symbol `s`. A single-symbol code has the empty code word. -/
def Hit : PrefixCode → Nat → Nat → Nat → Prop
  | .single sym, _, l, s => l = 0 ∧ s = sym
  | .canonical lens, w, l, s => lens[s]? = some l ∧ l ≠ 0 ∧ code lens s = some (revBits l w)

/-- A hit is what `decodeSymbol` returns, however many bits are at hand and whatever follows them. -/
theorem Hit.decode {c : PrefixCode} {w l s : Nat} (h : Hit c w l s) (hc : Complete c) {n : Nat} (hn : l ≤ n)
    (f : List Bool) : decodeSymbol c (lowBits w n ++ f) = some (s, lowBits (w / 2 ^ l) (n - l) ++ f) := by
  cases c with
  | single sym =>
    obtain ⟨rfl, rfl⟩ := h
    simp [decodeSymbol]
  | canonical lens =>
    obtain ⟨hs, h0, hcode⟩ := h
    refine (decodeSymbol_canonical hc.1 _ s _).mpr ⟨l, _, lowBits w l, hs, h0, hcode, ?_, ?_⟩
    · have := readCode_lowBits [] l l w (Nat.le_refl _)
      simpa [lowBits] using this
    · rw [lowBits_split l n w hn, List.append_assoc]

/-- A hit's length is at most 15. -/
theorem Hit.le_15 {c : PrefixCode} {w l s : Nat} (h : Hit c w l s) (hc : Complete c) : l ≤ 15 := by
  cases c with
  | single sym =>
    obtain ⟨rfl, -⟩ := h
    omega
  | canonical lens => exact hc.1 l (List.mem_of_getElem? h.1)

private theorem readCode_length : ∀ (n : Nat) (w : List Bool) (v : Nat) (r : List Bool),
    readCode n w = some (v, r) → w.length = n + r.length
  | 0, w, v, r, h => by
    simp only [readCode, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2]
    simp
  | _ + 1, [], _, _, h => by simp [readCode] at h
  | n + 1, b :: w, v, r, h => by
    simp only [readCode] at h
    cases hr : readCode n w with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v', r'⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      have := readCode_length n w v' r' hr
      rw [← h.2]
      simp only [List.length_cons]
      omega

/-- Every pattern has a hit. -/
theorem hit_exists {c : PrefixCode} (hc : Complete c) (w : Nat) : ∃ l s, Hit c w l s := by
  cases c with
  | single sym => exact ⟨0, sym, rfl, rfl⟩
  | canonical lens =>
    obtain ⟨s, r, hd⟩ := decodeSymbol_complete hc (bs := lowBits w 15) (by simp)
    obtain ⟨len, c0, w', hs, h0, hcode, hrd, heq⟩ := (decodeSymbol_canonical hc.1 _ s r).mp hd
    have hlen : len ≤ 15 := hc.1 len (List.mem_of_getElem? hs)
    have hprefix : w' = lowBits w len := by
      have hw : w'.length = len := by
        have := readCode_length len w' c0 [] hrd
        simpa using this
      have htake : (lowBits w 15).take len = w' := by
        rw [heq, List.take_left' hw]
      rw [← htake, lowBits_take len 15 w hlen]
    subst hprefix
    have hrev := readCode_lowBits [] len len w (Nat.le_refl _)
    simp only [List.append_nil, hrd, Option.some.injEq, Prod.mk.injEq] at hrev
    exact ⟨len, s, hs, h0, by rw [hcode, hrev.1]⟩

private theorem Hit.unique_length {c : PrefixCode} {w l s l' s' : Nat} (h : Hit c w l s) (h' : Hit c w l' s')
    (hc : Complete c) : l = l' := by
  have hl := h.le_15 hc
  have hl' := h'.le_15 hc
  have d := h.decode hc hl []
  have d' := h'.decode hc hl' []
  rw [d'] at d
  simp only [List.append_nil, Option.some.injEq, Prod.mk.injEq] at d
  have hlen := congrArg List.length d.2
  simp only [lowBits_length] at hlen
  omega

/-- Fewer bits at hand than the hit's length decode to nothing: the decoder has to wait for more. -/
theorem Hit.short {c : PrefixCode} {w l s n : Nat} (h : Hit c w l s) (hc : Complete c) (hn : n < l) :
    decodeSymbol c (lowBits w n) = none := by
  cases c with
  | single sym =>
    obtain ⟨rfl, -⟩ := h
    omega
  | canonical lens =>
    cases hd : decodeSymbol (.canonical lens) (lowBits w n) with
    | none => rfl
    | some p =>
      exfalso
      obtain ⟨s', r⟩ := p
      obtain ⟨len, c0, w', hs, h0, hcode, hrd, heq⟩ := (decodeSymbol_canonical hc.1 _ s' r).mp hd
      have hw : w'.length = len := by
        have := readCode_length len w' c0 [] hrd
        simpa using this
      have hlen : len ≤ n := by
        have := congrArg List.length heq
        simp only [lowBits_length, List.length_append] at this
        omega
      have hprefix : w' = lowBits w len := by
        have htake : (lowBits w n).take len = w' := by
          rw [heq, List.take_left' hw]
        rw [← htake, lowBits_take len n w hlen]
      subst hprefix
      have hrev := readCode_lowBits [] len len w (Nat.le_refl _)
      simp only [List.append_nil, hrd, Option.some.injEq, Prod.mk.injEq] at hrev
      have hh : Hit (.canonical lens) w len s' := ⟨hs, h0, by rw [hcode, hrev.1]⟩
      have hl := (Hit.unique_length hh h hc)
      omega

/-- A pattern has only one hit. -/
theorem Hit.unique {c : PrefixCode} {w l s l' s' : Nat} (h : Hit c w l s) (h' : Hit c w l' s') (hc : Complete c) :
    l = l' ∧ s = s' := by
  have hl := h.le_15 hc
  have hl' := h'.le_15 hc
  have d := h.decode hc hl []
  have d' := h'.decode hc hl' []
  rw [d'] at d
  simp only [List.append_nil, Option.some.injEq, Prod.mk.injEq] at d
  have hlen := congrArg List.length d.2
  simp only [lowBits_length] at hlen
  exact ⟨by omega, d.1.symm⟩

end Brotli.Decoder
