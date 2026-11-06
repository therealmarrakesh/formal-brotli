module

public import Brotli.Decoder.Builder

@[expose] public section

/-!
# Literal block types with one table

For each literal block type, the table base its 64 context-map entries share, when they all name the same tree, or
`0xFFFFFFFF` when they don't (libbrotli's `trivial_literal_context`). `trivBuild` makes the 4 bytes of every type when a
header ends, one round per type: the 64 map bytes are compared in a row, with no loop. `trivBuild_spec` gives its size
and what an entry other than `0xFFFFFFFF` means, which is all the literal loop needs to skip the context's lookups.
-/

namespace Brotli.Decoder

theorem ofNat_toNat32 {k : Nat} (h : k < 2 ^ 32) : (USize.ofNat k).toNat = k := by
  rw [USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

theorem off_toNat {i : USize} {k : Nat} (h : i.toNat + k < 2 ^ 32) : (i + USize.ofNat k).toNat = i.toNat + k := by
  rw [USize.toNat_add, ofNat_toNat32 (by omega)]
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

theorem mul_toNat {i : USize} {k : Nat} (hk : k < 2 ^ 32) (h : i.toNat * k < 2 ^ 32) :
    (i * USize.ofNat k).toNat = i.toNat * k := by
  rw [USize.toNat_mul, ofNat_toNat32 hk]
  apply Nat.mod_eq_of_lt
  have := USize.le_size
  rw [USize.size_eq_two_pow] at this
  omega

/-- The byte `k` after `i`. -/
@[inline] def byteOff (t : ByteArray) (i : USize) (k : Nat) (h : i.toNat + k < t.size) (h32 : t.size < 2 ^ 32) : UInt8 :=
  t.uget (i + USize.ofNat k) (by rw [off_toNat (by omega)]; exact h)

theorem byteOff_eq {t : ByteArray} {i : USize} {k : Nat} {h : i.toNat + k < t.size} {h32 : t.size < 2 ^ 32} :
    byteOff t i k h h32 = t.data[i.toNat + k]?.getD 0 := by
  have hi : (i + USize.ofNat k).toNat = i.toNat + k := off_toNat (by omega)
  cases t with
  | mk bs =>
    have h' : i.toNat + k < bs.size := h
    simp [byteOff, ByteArray.uget, hi, h']

/-- Whether the 8 bytes from `q` all equal `v`. -/
@[inline] def same8 (m : ByteArray) (q : USize) (v : UInt8) (h : q.toNat + 8 ≤ m.size) (h32 : m.size < 2 ^ 32) : Bool :=
  byteOff m q 0 (by omega) h32 == v && byteOff m q 1 (by omega) h32 == v && byteOff m q 2 (by omega) h32 == v &&
    byteOff m q 3 (by omega) h32 == v && byteOff m q 4 (by omega) h32 == v && byteOff m q 5 (by omega) h32 == v &&
    byteOff m q 6 (by omega) h32 == v && byteOff m q 7 (by omega) h32 == v

theorem same8_spec {m : ByteArray} {q : USize} {v : UInt8} {h : q.toNat + 8 ≤ m.size} {h32 : m.size < 2 ^ 32}
    (hs : same8 m q v h h32 = true) : ∀ b, b < 8 → m.data[q.toNat + b]?.getD 0 = v := by
  simp only [same8, Bool.and_eq_true, beq_iff_eq, byteOff_eq] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  intro b hb
  match b, hb with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7
  | _ + 8, hb => exact absurd hb (by omega)

/-- Whether the 64 bytes from `p` all equal `v`, as 64 tests in a row. -/
@[inline] def same64 (m : ByteArray) (p : USize) (v : UInt8) (h : p.toNat + 64 ≤ m.size) (h32 : m.size < 2 ^ 32) : Bool :=
  same8 m p v (by omega) h32 &&
    same8 m (p + USize.ofNat 8) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 16) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 24) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 32) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 40) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 48) v (by rw [off_toNat (by omega)]; omega) h32 &&
    same8 m (p + USize.ofNat 56) v (by rw [off_toNat (by omega)]; omega) h32

private theorem same8_at {m : ByteArray} {p : USize} {v : UInt8} {j : Nat} (hj : p.toNat + j + 8 ≤ m.size)
    (h32 : m.size < 2 ^ 32) {h : (p + USize.ofNat j).toNat + 8 ≤ m.size}
    (hs : same8 m (p + USize.ofNat j) v h h32 = true) {c : Nat} (hc1 : j ≤ c) (hc2 : c < j + 8) :
    m.data[p.toNat + c]?.getD 0 = v := by
  have e := same8_spec hs (c - j) (by omega)
  rw [off_toNat (by omega), show p.toNat + j + (c - j) = p.toNat + c by omega] at e
  exact e

theorem same64_spec {m : ByteArray} {p : USize} {v : UInt8} {h : p.toNat + 64 ≤ m.size} {h32 : m.size < 2 ^ 32}
    (hs : same64 m p v h h32 = true) : ∀ c, c < 64 → m.data[p.toNat + c]?.getD 0 = v := by
  simp only [same64, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hs
  intro c hc
  rcases (show c < 8 ∨ (8 ≤ c ∧ c < 16) ∨ (16 ≤ c ∧ c < 24) ∨ (24 ≤ c ∧ c < 32) ∨ (32 ≤ c ∧ c < 40) ∨
      (40 ≤ c ∧ c < 48) ∨ (48 ≤ c ∧ c < 56) ∨ (56 ≤ c ∧ c < 64) by omega) with
    hc | hc | hc | hc | hc | hc | hc | hc
  · exact same8_spec h0 c hc
  · exact same8_at (by omega) h32 h1 hc.1 (by omega)
  · exact same8_at (by omega) h32 h2 hc.1 (by omega)
  · exact same8_at (by omega) h32 h3 hc.1 (by omega)
  · exact same8_at (by omega) h32 h4 hc.1 (by omega)
  · exact same8_at (by omega) h32 h5 hc.1 (by omega)
  · exact same8_at (by omega) h32 h6 hc.1 (by omega)
  · exact same8_at (by omega) h32 h7 hc.1 (by omega)

/-- Four bytes more. -/
@[inline] def push4 (out : ByteArray) (a b c d : UInt8) : ByteArray := (((out.push a).push b).push c).push d

theorem push4_size (out : ByteArray) (a b c d : UInt8) : (push4 out a b c d).size = out.size + 4 := by
  simp only [push4, ByteArray.size_push]

theorem push4_old {out : ByteArray} {a b c d : UInt8} {i : Nat} (hi : i < out.size) :
    (push4 out a b c d).data[i]? = out.data[i]? := by
  have hs : out.size = out.data.size := rfl
  simp only [push4, ByteArray.data_push, Array.getElem?_push, Array.size_push]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem u32At_push4_new {out : ByteArray} {a b c d : UInt8} {s : Nat} (hs : out.size = 4 * s) :
    u32At (push4 out a b c d) s = a.toNat + 256 * b.toNat + 65536 * c.toNat + 16777216 * d.toNat := by
  have hd : out.size = out.data.size := rfl
  have e0 : (push4 out a b c d).data[4 * s]? = some a := by
    simp only [push4, ByteArray.data_push, Array.getElem?_push, Array.size_push]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  have e1 : (push4 out a b c d).data[4 * s + 1]? = some b := by
    simp only [push4, ByteArray.data_push, Array.getElem?_push, Array.size_push]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  have e2 : (push4 out a b c d).data[4 * s + 2]? = some c := by
    simp only [push4, ByteArray.data_push, Array.getElem?_push, Array.size_push]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  have e3 : (push4 out a b c d).data[4 * s + 3]? = some d := by
    simp only [push4, ByteArray.data_push, Array.getElem?_push, Array.size_push]
    rw [ite_eq_left (by omega)]
  unfold u32At
  rw [e0, e1, e2, e3]
  rfl

theorem base_idx {litBase : ByteArray} {nT : Nat} {v : UInt8} (hb : litBase.size = 4 * nT)
    (hb32 : litBase.size < 2 ^ 32) (hv : v.toNat < nT) {k : Nat} (hk : k < 4) :
    (v.toUSize * USize.ofNat 4).toNat + k < litBase.size := by
  have hu : v.toUSize.toNat = v.toNat := by simp
  rw [mul_toNat (by decide) (by rw [hu]; omega), hu]
  omega

/-- A literal block type's entry, for the 64 map bytes from `p`: the table base they share, or `0xFFFFFFFF`. -/
@[inline] def trivEntry (lMap litBase : ByteArray) (nT : Nat) (hm32 : lMap.size < 2 ^ 32) (hb : litBase.size = 4 * nT)
    (hb32 : litBase.size < 2 ^ 32) (hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT)
    (p : USize) (hp : p.toNat + 64 ≤ lMap.size) (out : ByteArray) : ByteArray :=
  if same64 lMap p (lMap.uget p (by omega)) hp hm32 then
    push4 out
      (byteOff litBase ((lMap.uget p (by omega)).toUSize * USize.ofNat 4) 0 (base_idx hb hb32 (hlt p _) (by decide)) hb32)
      (byteOff litBase ((lMap.uget p (by omega)).toUSize * USize.ofNat 4) 1 (base_idx hb hb32 (hlt p _) (by decide)) hb32)
      (byteOff litBase ((lMap.uget p (by omega)).toUSize * USize.ofNat 4) 2 (base_idx hb hb32 (hlt p _) (by decide)) hb32)
      (byteOff litBase ((lMap.uget p (by omega)).toUSize * USize.ofNat 4) 3 (base_idx hb hb32 (hlt p _) (by decide)) hb32)
  else push4 out 255 255 255 255

theorem trivEntry_spec {lMap litBase : ByteArray} {nT : Nat} {hm32 : lMap.size < 2 ^ 32} {hb : litBase.size = 4 * nT}
    {hb32 : litBase.size < 2 ^ 32} {hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT}
    {p : USize} {hp : p.toNat + 64 ≤ lMap.size} {out : ByteArray} {s : Nat} (hs : out.size = 4 * s) :
    (trivEntry lMap litBase nT hm32 hb hb32 hlt p hp out).size = out.size + 4 ∧
      (∀ i, i < out.size → (trivEntry lMap litBase nT hm32 hb hb32 hlt p hp out).data[i]? = out.data[i]?) ∧
      (u32At (trivEntry lMap litBase nT hm32 hb hb32 hlt p hp out) s ≠ 4294967295 → ∀ c, c < 64 →
        u32At litBase (lMap.data[p.toNat + c]?.getD 0).toNat = u32At (trivEntry lMap litBase nT hm32 hb hb32 hlt p hp out) s) := by
  unfold trivEntry
  split
  · rename_i hS
    refine ⟨push4_size _ _ _ _ _, fun i hi => push4_old hi, fun _ c hc => ?_⟩
    rw [u32At_push4_new hs, same64_spec hS c hc, byteOff_eq, byteOff_eq, byteOff_eq, byteOff_eq]
    have hv := hlt p (by omega)
    have hu : (lMap.uget p (by omega)).toUSize.toNat = (lMap.uget p (by omega)).toNat := by simp
    rw [mul_toNat (by decide) (by rw [hu]; omega), hu]
    unfold u32At
    rw [show (lMap.uget p (by omega)).toNat * 4 = 4 * (lMap.uget p (by omega)).toNat by omega]
    rfl
  · refine ⟨push4_size _ _ _ _ _, fun i hi => push4_old hi, fun hne => ?_⟩
    rw [u32At_push4_new hs] at hne
    exact absurd rfl hne

/-- What the entries below `k` say: an entry other than `0xFFFFFFFF` is the table base of each of its type's 64
contexts. -/
def TrivInv (lMap litBase out : ByteArray) (k : Nat) : Prop :=
  ∀ s, s < k → u32At out s ≠ 4294967295 → ∀ c, c < 64 → u32At litBase (lMap.data[64 * s + c]?.getD 0).toNat = u32At out s

theorem trivP {lMap : ByteArray} {n t : USize} (hm : lMap.size = 64 * n.toNat) (hm32 : lMap.size < 2 ^ 32)
    (ht : t < n) : (t * USize.ofNat 64).toNat + 64 ≤ lMap.size := by
  have := USize.lt_iff_toNat_lt.mp ht
  rw [mul_toNat (by decide) (by omega)]
  omega

theorem trivNext {lMap : ByteArray} {n t : USize} (hm : lMap.size = 64 * n.toNat) (hm32 : lMap.size < 2 ^ 32)
    (ht : t < n) : (t + USize.ofNat 1).toNat = t.toNat + 1 := by
  have := USize.lt_iff_toNat_lt.mp ht
  exact off_toNat (by omega)

/-- The entries from type `t` on, after `out`. -/
def trivLoop (lMap litBase : ByteArray) (nT : Nat) (n : USize) (hm : lMap.size = 64 * n.toNat) (hm32 : lMap.size < 2 ^ 32)
    (hb : litBase.size = 4 * nT) (hb32 : litBase.size < 2 ^ 32)
    (hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT) (t : USize) (out : ByteArray) : ByteArray :=
  if ht : t < n then
    trivLoop lMap litBase nT n hm hm32 hb hb32 hlt (t + USize.ofNat 1)
      (trivEntry lMap litBase nT hm32 hb hb32 hlt (t * USize.ofNat 64) (trivP hm hm32 ht) out)
  else out
termination_by n.toNat - t.toNat
decreasing_by
  have := USize.lt_iff_toNat_lt.mp ht
  rw [trivNext hm hm32 ht]
  omega

theorem trivLoop_spec {lMap litBase : ByteArray} {nT : Nat} {n : USize} {hm : lMap.size = 64 * n.toNat}
    {hm32 : lMap.size < 2 ^ 32} {hb : litBase.size = 4 * nT} {hb32 : litBase.size < 2 ^ 32}
    {hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT} :
    ∀ (N : Nat) (t : USize) (out : ByteArray), n.toNat - t.toNat = N → t.toNat ≤ n.toNat → out.size = 4 * t.toNat →
      TrivInv lMap litBase out t.toNat →
      (trivLoop lMap litBase nT n hm hm32 hb hb32 hlt t out).size = 4 * n.toNat ∧
        TrivInv lMap litBase (trivLoop lMap litBase nT n hm hm32 hb hb32 hlt t out) n.toNat := by
  intro N
  induction N with
  | zero =>
    intro t out hN hle hs hi
    have ht : ¬ t < n := fun h => by have := USize.lt_iff_toNat_lt.mp h; omega
    rw [trivLoop, dite_eq_right ht]
    have e : t.toNat = n.toNat := by omega
    rw [← e]
    exact ⟨hs, hi⟩
  | succ N ih =>
    intro t out hN hle hs hi
    have ht : t < n := USize.lt_iff_toNat_lt.mpr (by omega)
    rw [trivLoop, dite_eq_left ht]
    have hnx := trivNext hm hm32 ht
    have hp : (t * USize.ofNat 64).toNat = 64 * t.toNat := by
      have := USize.lt_iff_toNat_lt.mp ht
      rw [mul_toNat (by decide) (by omega)]
      omega
    obtain ⟨e1, e2, e3⟩ := trivEntry_spec (hm32 := hm32) (hb := hb) (hb32 := hb32) (hlt := hlt)
      (p := t * USize.ofNat 64) (hp := trivP hm hm32 ht) (out := out) hs
    refine ih _ _ (by omega) (by omega) (by rw [e1, hnx]; omega) ?_
    intro s hs' hne c hc
    rw [hnx] at hs'
    by_cases hst : s = t.toNat
    · subst hst
      have := e3 hne c hc
      rw [hp] at this
      exact this
    · have hold : u32At (trivEntry lMap litBase nT hm32 hb hb32 hlt (t * USize.ofNat 64) (trivP hm hm32 ht) out) s =
          u32At out s := by
        unfold u32At
        rw [e2 _ (by omega), e2 _ (by omega), e2 _ (by omega), e2 _ (by omega)]
      rw [hold] at hne ⊢
      exact hi s (by omega) hne c hc

/-- The entries of every literal block type, made in a fresh array of their size. -/
def trivBuild (lMap litBase : ByteArray) (nT : Nat) (nL : UInt64) (hm : lMap.size = 64 * nL.toNat)
    (hm32 : lMap.size < 2 ^ 32) (hb : litBase.size = 4 * nT) (hb32 : litBase.size < 2 ^ 32)
    (hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT) : ByteArray :=
  trivLoop lMap litBase nT nL.toUSize (by rw [word_toUSize (by omega)]; exact hm) hm32 hb hb32 hlt 0
    (freshBytes (nL * 4).toNat)

theorem trivBuild_spec {lMap litBase : ByteArray} {nT : Nat} {nL : UInt64} {hm : lMap.size = 64 * nL.toNat}
    {hm32 : lMap.size < 2 ^ 32} {hb : litBase.size = 4 * nT} {hb32 : litBase.size < 2 ^ 32}
    {hlt : ∀ p : USize, ∀ h : p.toNat < lMap.size, (lMap.uget p h).toNat < nT} :
    (trivBuild lMap litBase nT nL hm hm32 hb hb32 hlt).size = 4 * nL.toNat ∧
      TrivInv lMap litBase (trivBuild lMap litBase nT nL hm hm32 hb hb32 hlt) nL.toNat := by
  have hn : nL.toUSize.toNat = nL.toNat := word_toUSize (by omega)
  have h0 : (0 : USize).toNat = 0 := rfl
  have hf : (freshBytes (nL * 4).toNat).size = 0 := rfl
  have := trivLoop_spec (lMap := lMap) (litBase := litBase) (nT := nT) (n := nL.toUSize)
    (hm := by rw [hn]; exact hm) (hm32 := hm32) (hb := hb) (hb32 := hb32) (hlt := hlt) _ 0
    (freshBytes (nL * 4).toNat) rfl (by rw [h0]; omega) (by rw [hf, h0]) (fun s hs => absurd hs (by rw [h0]; omega))
  exact ⟨this.1.trans (by rw [hn]), fun s hs => this.2 s (by rw [hn]; exact hs)⟩

end Brotli.Decoder
