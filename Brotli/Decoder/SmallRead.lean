import Brotli.Decoder.Block

/-!
# Small reads in a meta-block's header

The header is made of small reads, each at most 56 bits, so a refilled buffer holds them unless the chunk ran out.
A read is all or nothing: if the bits run short, nothing is used. `ROk` says what a read must do in the spec's terms,
and the rules below build that up one spec read at a time.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-- A small read's result, flat. What its values mean is up to the read. -/
structure Rd where
  status : ReadStatus
  word : UInt64
  count : UInt64
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
  e : UInt64

/-- A read that finished with these values. -/
@[inline] def Rd.ok (b : BitBuffer) (v0 v1 v2 v3 v4 : UInt64) : Rd := ⟨.ok, b.word, b.count, v0, v1, v2, v3, v4⟩

/-- A read that used nothing, as the bits ran short. -/
@[inline] def Rd.short (b0 : BitBuffer) : Rd := ⟨.short, b0.word, b0.count, 0, 0, 0, 0, 0⟩

/-- A read the spec rejects. -/
@[inline] def Rd.bad (b0 : BitBuffer) : Rd := ⟨.bad, b0.word, b0.count, 0, 0, 0, 0, 0⟩

/-- The buffer a read leaves. -/
@[inline] def Rd.buf (r : Rd) : BitBuffer := ⟨r.word, r.count⟩

/-- What a read from the start `b0`, now at `b`, must do: finishing gives `v` and the buffer it leaves, whatever bits
follow. Running short means nothing was used, fewer than `room` bits were held, and the spec has nothing to give from the
bits held alone. Rejecting means the spec rejects, whatever bits follow. -/
structure ROk {A : Type} (spec : List Bool → Option (A × List Bool)) (b b0 : BitBuffer) (room : Nat) (r : Rd) (v : A) :
    Prop where
  ok : r.status = .ok → r.buf.Wf ∧ ∀ f, spec (b.held ++ f) = some (v, r.buf.held ++ f)
  short : r.status = .short → r.word = b0.word ∧ r.count = b0.count ∧ b.count.toNat < room ∧ spec b.held = none
  bad : r.status = .bad → ∀ f, spec (b.held ++ f) = none

section
variable {A : Type} {spec : List Bool → Option (A × List Bool)} {b b0 : BitBuffer} {room : Nat} {r : Rd} {v : A}

/-- The read is done. -/
theorem ROk.done (hw : b.Wf) (h : ∀ f, spec (b.held ++ f) = some (v, b.held ++ f)) (v0 v1 v2 v3 v4 : UInt64) :
    ROk spec b b0 room (Rd.ok b v0 v1 v2 v3 v4) v :=
  ⟨fun _ => ⟨hw, h⟩, fun e => ReadStatus.noConfusion e, fun e => ReadStatus.noConfusion e⟩

/-- The spec rejects. -/
theorem ROk.reject (h : ∀ f, spec (b.held ++ f) = none) : ROk spec b b0 room (Rd.bad b0) v :=
  ⟨fun e => ReadStatus.noConfusion e, fun e => ReadStatus.noConfusion e, fun _ => h⟩

/-- Changing the spec for one that agrees with it. -/
theorem ROk.congr {spec' : List Bool → Option (A × List Bool)} (h : ROk spec' b b0 room r v) (e : ∀ bs, spec bs = spec' bs) :
    ROk spec b b0 room r v :=
  ⟨fun s => by
      obtain ⟨h1, h2⟩ := h.ok s
      exact ⟨h1, fun f => by rw [e]; exact h2 f⟩,
    fun s => by
      obtain ⟨h1, h2, h3, h4⟩ := h.short s
      exact ⟨h1, h2, h3, by rw [e]; exact h4⟩,
    fun s f => by rw [e]; exact h.bad s f⟩

/-- An integer that the bits held cover. -/
theorem ROk.intOk {g : Nat × List Bool → Option (A × List Bool)} {k : UInt64} (hk : k.toNat < 64) (hle : k ≤ b.count)
    (h : ROk (fun bs => g ((b.peek k).toNat, bs)) (b.drop k) b0 (room - k.toNat) r v) :
    ROk (fun bs => readInt k.toNat bs >>= g) b b0 room r v := by
  have hle' := UInt64.le_iff_toNat_le.mp hle
  have hread := fun f => read_int (b := b) f hk hle
  have hnil := hread []
  rw [List.append_nil, List.append_nil] at hnil
  refine ⟨fun s => ?_, fun s => ?_, fun s f => ?_⟩
  · obtain ⟨h1, h2⟩ := h.ok s
    exact ⟨h1, fun f => by rw [hread f]; exact h2 f⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h.short s
    have hc := drop_count (b := b) hle'
    refine ⟨h1, h2, by omega, ?_⟩
    rw [hnil]
    exact h4
  · rw [hread f]
    exact h.bad s f

/-- An integer that the bits held don't cover. -/
theorem ROk.intShort {g : Nat × List Bool → Option (A × List Bool)} {k : Nat} (hlt : b.count.toNat < k) (hroom : k ≤ room) :
    ROk (fun bs => readInt k bs >>= g) b b0 room (Rd.short b0) v := by
  refine ⟨fun e => ReadStatus.noConfusion e, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun e => ReadStatus.noConfusion e⟩
  rw [readInt_short hlt]
  rfl

/-- A symbol that the bits held cover. -/
theorem ROk.symOk {g : Nat × List Bool → Option (A × List Bool)} {t : ByteArray} {base : USize} {c : PrefixCode}
    {hfit : TableFits t base.toNat} {h32 : t.size < 2 ^ 32} (hok : TableOk t base.toNat c) (hC : Complete c)
    (hle : wordBits (lookup t base b.word hfit h32) ≤ b.count)
    (h : ROk (fun bs => g (wordValue (lookup t base b.word hfit h32), bs)) (b.drop (wordBits (lookup t base b.word hfit h32))) b0
      (room - (wordBits (lookup t base b.word hfit h32)).toNat) r v) :
    ROk (fun bs => decodeSymbol c bs >>= g) b b0 room r v := by
  have L := lookup_read (b := b) hok hfit h32 hC
  dsimp only at L
  obtain ⟨_, h1, _⟩ := L
  have hle' := UInt64.le_iff_toNat_le.mp hle
  have hread := h1 hle
  have hnil := hread []
  rw [List.append_nil, List.append_nil] at hnil
  refine ⟨fun s => ?_, fun s => ?_, fun s f => ?_⟩
  · obtain ⟨h2, h3⟩ := h.ok s
    exact ⟨h2, fun f => by rw [hread f]; exact h3 f⟩
  · obtain ⟨h2, h3, h4, h5⟩ := h.short s
    have hc := drop_count (b := b) hle'
    refine ⟨h2, h3, by omega, ?_⟩
    rw [hnil]
    exact h5
  · rw [hread f]
    exact h.bad s f

/-- A symbol that the bits held don't cover. -/
theorem ROk.symShort {g : Nat × List Bool → Option (A × List Bool)} {t : ByteArray} {base : USize} {c : PrefixCode}
    {hfit : TableFits t base.toNat} {h32 : t.size < 2 ^ 32} (hok : TableOk t base.toNat c) (hC : Complete c)
    (hnot : ¬ wordBits (lookup t base b.word hfit h32) ≤ b.count) (hroom : 15 ≤ room) :
    ROk (fun bs => decodeSymbol c bs >>= g) b b0 room (Rd.short b0) v := by
  have L := lookup_read (b := b) hok hfit h32 hC
  dsimp only at L
  obtain ⟨h0, _, h2⟩ := L
  have hlt : b.count.toNat < (wordBits (lookup t base b.word hfit h32)).toNat :=
    Nat.lt_of_not_le fun h => hnot (UInt64.le_iff_toNat_le.mpr h)
  refine ⟨fun e => ReadStatus.noConfusion e, fun _ => ⟨rfl, rfl, by omega, ?_⟩, fun e => ReadStatus.noConfusion e⟩
  rw [h2 hnot]
  rfl

end

private theorem u64_lt_of {n : Nat} {a : UInt64} (h : a.toNat < n) (hn : n ≤ 64) : a.toNat < 64 := by omega

/-- The bits a read can take and still be a read of an integer. -/
theorem peek_lt (b : BitBuffer) {k : UInt64} (hk : k.toNat < 64) : (b.peek k).toNat < 2 ^ k.toNat := by
  rw [BitBuffer.peek_toNat b hk]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The rest of the buffer stays well formed. -/
theorem drop_wf' {b : BitBuffer} (hw : b.Wf) {k : UInt64} (hk : k.toNat < 64) (hle : k ≤ b.count) : (b.drop k).Wf :=
  BitBuffer.drop_wf hw hk (UInt64.le_iff_toNat_le.mp hle)

/-! ### The variable-length code -/

/-- Reads the variable-length code of NBLTYPES and the other counts, into `a`. -/
def varLenFast (b0 : BitBuffer) : Rd :=
  if 1 ≤ b0.count then
    let first := b0.peek 1
    let b1 := b0.drop 1
    if first = 0 then Rd.ok b1 1 0 0 0 0
    else if 3 ≤ b1.count then
      let n := b1.peek 3
      let b2 := b1.drop 3
      if n = 0 then Rd.ok b2 2 0 0 0 0
      else if n ≤ b2.count then
        let x := b2.peek n
        Rd.ok (b2.drop n) ((1 <<< n) + 1 + x) 0 0 0 0
      else Rd.short b0
    else Rd.short b0
  else Rd.short b0

private theorem nat_shl_one (n : Nat) : 1 <<< n = 2 ^ n := by
  rw [Nat.shiftLeft_eq, Nat.one_mul]

private theorem one_shl' {d : UInt64} (hd : d.toNat < 32) : ((1 : UInt64) <<< d).toNat = 2 ^ d.toNat := by
  have hp : 2 ^ d.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hd
  rw [UInt64.toNat_shiftLeft, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt (show d.toNat < 64 by omega), nat_shl_one]
  exact Nat.mod_eq_of_lt (by omega)

theorem varLenFast_ok {b0 : BitBuffer} (hw : b0.Wf) : ROk readVarLen b0 b0 11 (varLenFast b0) (varLenFast b0).a.toNat := by
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h3 : (3 : UInt64).toNat = 3 := rfl
  unfold varLenFast
  refine ROk.congr ?_ (fun _ => rfl)
  split
  · rename_i hc1
    refine ROk.intOk (k := 1) (by decide) hc1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 1) (by decide) hc1
    generalize b0.drop 1 = b1 at hw1 ⊢
    by_cases hf : b0.peek 1 = 0
    · rw [ite_eq_left hf]
      have : (b0.peek 1).toNat = 0 := by rw [hf]; rfl
      exact ROk.done hw1 (fun f => by simp only [this, ↓reduceIte]; rfl) _ _ _ _ _
    · rw [ite_eq_right hf]
      have hne : (b0.peek 1).toNat ≠ 0 := fun e => hf (UInt64.toNat_inj.mp (by rw [e]; rfl))
      simp only [hne, ↓reduceIte]
      split
      · rename_i hc3
        refine ROk.intOk (k := 3) (by decide) hc3 ?_
        dsimp only
        have hw2 := drop_wf' hw1 (k := 3) (by decide) hc3
        have hn8 : (b1.peek 3).toNat < 8 := peek_lt b1 (k := 3) (by decide)
        generalize b1.drop 3 = b2 at hw2 ⊢
        generalize b1.peek 3 = n at hn8 ⊢
        by_cases hn : n = 0
        · rw [ite_eq_left hn]
          have : n.toNat = 0 := by rw [hn]; rfl
          exact ROk.done hw2 (fun f => by simp only [this, ↓reduceIte]; rfl) _ _ _ _ _
        · rw [ite_eq_right hn]
          have hne' : n.toNat ≠ 0 := fun e => hn (UInt64.toNat_inj.mp (by rw [e]; rfl))
          simp only [hne', ↓reduceIte]
          split
          · rename_i hcn
            refine ROk.intOk (by omega) hcn ?_
            have hx : (b2.peek n).toNat < 2 ^ n.toNat := peek_lt b2 (by omega)
            have hsh := one_shl' (d := n) (by omega)
            have hp : 2 ^ n.toNat ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
            have h27 : (2 : Nat) ^ 7 = 128 := rfl
            have hsum : ((1 <<< n) + 1 + b2.peek n).toNat = 2 ^ n.toNat + 1 + (b2.peek n).toNat := by
              rw [UInt64.toNat_add, UInt64.toNat_add, hsh, h1]
              rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            refine ROk.done (drop_wf' hw2 (by omega) hcn) (fun f => ?_) _ _ _ _ _
            simp only [Rd.ok]
            rw [hsum, nat_shl_one]
          · rename_i hcn
            exact ROk.intShort (Nat.lt_of_not_le fun h => hcn (UInt64.le_iff_toNat_le.mpr h)) (by
              simp only [h1, h3]
              omega)
      · rename_i hc3
        exact ROk.intShort (Nat.lt_of_not_le fun h => hc3 (UInt64.le_iff_toNat_le.mpr h)) (by
          simp only [h1]
          omega)
  · rename_i hc1
    exact ROk.intShort (Nat.lt_of_not_le fun h => hc1 (UInt64.le_iff_toNat_le.mpr h)) (by omega)

private theorem not_le_lt {a k : UInt64} (h : ¬ k ≤ a) : a.toNat < k.toNat :=
  Nat.lt_of_not_le fun e => h (UInt64.le_iff_toNat_le.mpr e)

private theorem eq_toNat {x n : UInt64} (h : x = n) : x.toNat = n.toNat := by rw [h]

private theorem ne_toNat {x n : UInt64} (h : ¬ x = n) : ¬ x.toNat = n.toNat := fun e => h (UInt64.toNat_inj.mp e)

/-! ### RLEMAX -/

/-- Reads RLEMAX, into `a`. -/
def rlemaxFast (b0 : BitBuffer) : Rd :=
  if 1 ≤ b0.count then
    let flag := b0.peek 1
    let b1 := b0.drop 1
    if flag = 0 then Rd.ok b1 0 0 0 0 0
    else if 4 ≤ b1.count then Rd.ok (b1.drop 4) (b1.peek 4 + 1) 0 0 0 0
    else Rd.short b0
  else Rd.short b0

theorem rlemaxFast_ok {b0 : BitBuffer} (hw : b0.Wf) : ROk readRLEMAX b0 b0 5 (rlemaxFast b0) (rlemaxFast b0).a.toNat := by
  unfold rlemaxFast
  refine ROk.congr ?_ (fun _ => rfl)
  split
  · rename_i hc1
    refine ROk.intOk (k := 1) (by decide) hc1 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 1) (by decide) hc1
    generalize b0.drop 1 = b1 at hw1 ⊢
    by_cases hf : b0.peek 1 = 0
    · rw [ite_eq_left hf]
      have : (b0.peek 1).toNat = 0 := eq_toNat hf
      exact ROk.done hw1 (fun f => by simp only [this, ↓reduceIte]; rfl) _ _ _ _ _
    · rw [ite_eq_right hf]
      have hne : ¬ (b0.peek 1).toNat = 0 := ne_toNat hf
      simp only [hne, ↓reduceIte]
      split
      · rename_i hc4
        refine ROk.intOk (k := 4) (by decide) hc4 ?_
        have hx : (b1.peek 4).toNat < 16 := peek_lt b1 (k := 4) (by decide)
        have hsum : (b1.peek 4 + 1).toNat = (b1.peek 4).toNat + 1 := by
          rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]
          exact Nat.mod_eq_of_lt (by omega)
        refine ROk.done (drop_wf' hw1 (by decide) hc4) (fun f => ?_) _ _ _ _ _
        simp only [Rd.ok]
        rw [hsum]
      · rename_i hc4
        exact ROk.intShort (not_le_lt hc4) (by decide)
  · rename_i hc1
    exact ROk.intShort (not_le_lt hc1) (by decide)

/-! ### A code length of a code length symbol -/

/-- The code of `readCodeLengthCodeLength`, as a chain of reads. -/
def cclChain (bs : List Bool) : Option (Nat × List Bool) :=
  readInt 2 bs >>= fun p =>
    if p.1 = 0 then some (0, p.2)
    else if p.1 = 1 then some (4, p.2)
    else if p.1 = 2 then some (3, p.2)
    else readInt 1 p.2 >>= fun q =>
      if q.1 = 0 then some (2, q.2)
      else readInt 1 q.2 >>= fun u =>
        if u.1 = 0 then some (1, u.2) else some (5, u.2)

theorem cclChain_eq (bs : List Bool) : readCodeLengthCodeLength bs = cclChain bs := by
  rcases bs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> (try cases c) <;> (try cases d) <;> rfl

/-- Reads a code length of a code length symbol, into `a`. -/
def cclFast (b0 : BitBuffer) : Rd :=
  if 2 ≤ b0.count then
    let v := b0.peek 2
    let b1 := b0.drop 2
    if v = 0 then Rd.ok b1 0 0 0 0 0
    else if v = 1 then Rd.ok b1 4 0 0 0 0
    else if v = 2 then Rd.ok b1 3 0 0 0 0
    else if 1 ≤ b1.count then
      let q := b1.peek 1
      let b2 := b1.drop 1
      if q = 0 then Rd.ok b2 2 0 0 0 0
      else if 1 ≤ b2.count then
        let u := b2.peek 1
        let b3 := b2.drop 1
        if u = 0 then Rd.ok b3 1 0 0 0 0 else Rd.ok b3 5 0 0 0 0
      else Rd.short b0
    else Rd.short b0
  else Rd.short b0

theorem cclFast_ok {b0 : BitBuffer} (hw : b0.Wf) :
    ROk readCodeLengthCodeLength b0 b0 4 (cclFast b0) (cclFast b0).a.toNat := by
  refine ROk.congr ?_ cclChain_eq
  unfold cclFast cclChain
  split
  · rename_i h2
    refine ROk.intOk (k := 2) (by decide) h2 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    generalize b0.drop 2 = b1 at hw1 ⊢
    generalize b0.peek 2 = v
    by_cases h0 : v = 0
    · rw [ite_eq_left h0]
      have e : v.toNat = 0 := eq_toNat h0
      simp only [e, ↓reduceIte]
      exact ROk.done hw1 (fun f => rfl) _ _ _ _ _
    rw [ite_eq_right h0]
    have e0 : ¬ v.toNat = 0 := ne_toNat h0
    simp only [e0, ↓reduceIte]
    by_cases h1 : v = 1
    · rw [ite_eq_left h1]
      have e : v.toNat = 1 := eq_toNat h1
      simp only [e, ↓reduceIte]
      exact ROk.done hw1 (fun f => rfl) _ _ _ _ _
    rw [ite_eq_right h1]
    have e1 : ¬ v.toNat = 1 := ne_toNat h1
    simp only [e1, ↓reduceIte]
    by_cases h2' : v = 2
    · rw [ite_eq_left h2']
      have e : v.toNat = 2 := eq_toNat h2'
      simp only [e, ↓reduceIte]
      exact ROk.done hw1 (fun f => rfl) _ _ _ _ _
    rw [ite_eq_right h2']
    have e2 : ¬ v.toNat = 2 := ne_toNat h2'
    simp only [e2, ↓reduceIte]
    split
    · rename_i hc1
      refine ROk.intOk (k := 1) (by decide) hc1 ?_
      dsimp only
      have hw2 := drop_wf' hw1 (k := 1) (by decide) hc1
      generalize b1.drop 1 = b2 at hw2 ⊢
      generalize b1.peek 1 = q
      by_cases hq : q = 0
      · rw [ite_eq_left hq]
        have e : q.toNat = 0 := eq_toNat hq
        simp only [e, ↓reduceIte]
        exact ROk.done hw2 (fun f => rfl) _ _ _ _ _
      rw [ite_eq_right hq]
      have eq0 : ¬ q.toNat = 0 := ne_toNat hq
      simp only [eq0, ↓reduceIte]
      split
      · rename_i hc2
        refine ROk.intOk (k := 1) (by decide) hc2 ?_
        dsimp only
        have hw3 := drop_wf' hw2 (k := 1) (by decide) hc2
        generalize b2.drop 1 = b3 at hw3 ⊢
        generalize b2.peek 1 = u
        by_cases hu : u = 0
        · rw [ite_eq_left hu]
          have e : u.toNat = 0 := eq_toNat hu
          simp only [e, ↓reduceIte]
          exact ROk.done hw3 (fun f => rfl) _ _ _ _ _
        · rw [ite_eq_right hu]
          have eu : ¬ u.toNat = 0 := ne_toNat hu
          simp only [eu, ↓reduceIte]
          exact ROk.done hw3 (fun f => rfl) _ _ _ _ _
      · rename_i hc2
        exact ROk.intShort (not_le_lt hc2) (by decide)
    · rename_i hc1
      exact ROk.intShort (not_le_lt hc1) (by decide)
  · rename_i h2
    exact ROk.intShort (not_le_lt h2) (by decide)

/-! ### A simple prefix code -/

/-- `readSimple`, from its tree-select bit. Each value read so far is a parameter of the next part of the chain, so
that a proof can drop a read without leaving it inside a `Decidable` instance. -/
def simpleC5 (size s1 s2 s3 s4 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt 1 bs >>= fun t =>
    if t.1 = 0 then some (.canonical (lengthsOf size [(s1, 2), (s2, 2), (s3, 2), (s4, 2)]), t.2)
    else some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 3), (s4, 3)]), t.2)

/-- `readSimple`, from its fourth symbol. -/
def simpleC4 (size bits s1 s2 s3 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt bits bs >>= fun q =>
    if size ≤ q.1 ∨ q.1 = s1 ∨ q.1 = s2 ∨ q.1 = s3 then none else simpleC5 size s1 s2 s3 q.1 q.2

/-- `readSimple`, after its third symbol. -/
def simpleN3 (size bits n s1 s2 s3 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  if n = 2 then some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 2)]), bs) else simpleC4 size bits s1 s2 s3 bs

/-- `readSimple`, from its third symbol. -/
def simpleC3 (size bits n s1 s2 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt bits bs >>= fun q =>
    if size ≤ q.1 ∨ q.1 = s1 ∨ q.1 = s2 then none else simpleN3 size bits n s1 s2 q.1 q.2

/-- `readSimple`, after its second symbol. -/
def simpleN2 (size bits n s1 s2 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  if n = 1 then some (.canonical (lengthsOf size [(s1, 1), (s2, 1)]), bs) else simpleC3 size bits n s1 s2 bs

/-- `readSimple`, from its second symbol. -/
def simpleC2 (size bits n s1 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt bits bs >>= fun q =>
    if size ≤ q.1 ∨ q.1 = s1 then none else simpleN2 size bits n s1 q.1 q.2

/-- `readSimple`, after its first symbol. -/
def simpleN1 (size bits n s1 : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  if n = 0 then some (.single s1, bs) else simpleC2 size bits n s1 bs

/-- `readSimple`, from its first symbol. -/
def simpleC1 (size bits n : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt bits bs >>= fun q => if size ≤ q.1 then none else simpleN1 size bits n q.1 q.2

/-- `readSimple`, as a chain of reads. -/
def simpleChain (size bits : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) :=
  readInt 2 bs >>= fun p => simpleC1 size bits p.1 p.2

/-- What `readSimple` does with its symbols. -/
def simpleFinish (size : Nat) (p : List Nat × List Bool) : Option (PrefixCode × List Bool) :=
  match p.1 with
  | [s] => some (.single s, p.2)
  | [s1, s2] => some (.canonical (lengthsOf size [(s1, 1), (s2, 1)]), p.2)
  | [s1, s2, s3] => some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 2)]), p.2)
  | [s1, s2, s3, s4] =>
    readInt 1 p.2 >>= fun t =>
      if t.1 = 0 then some (.canonical (lengthsOf size [(s1, 2), (s2, 2), (s3, 2), (s4, 2)]), t.2)
      else some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 3), (s4, 3)]), t.2)
  | _ => none

private theorem bind_ext {α β : Type} {x : Option α} {f g : α → Option β} (h : ∀ a, f a = g a) : (x >>= f) = (x >>= g) := by
  rw [funext h]

private theorem ite_congr' {α : Type} {a b : Prop} [Decidable a] [Decidable b] {x y u v : α} (h : a ↔ b) (h1 : x = u)
    (h2 : ¬ b → y = v) : (if a then x else y) = (if b then u else v) := by
  by_cases hb : b
  · rw [ite_eq_left (h.mpr hb), ite_eq_left hb, h1]
  · rw [ite_eq_right (fun ha => hb (h.mp ha)), ite_eq_right hb, h2 hb]

private theorem sym_step {α : Type} (size bits n : Nat) (syms : List Nat) (bs : List Bool) (F : List Nat × List Bool → Option α) :
    (readSimpleSymbols size bits (n + 1) syms bs >>= F) =
      readInt bits bs >>= fun q => if size ≤ q.1 ∨ syms.contains q.1 = true then none
        else readSimpleSymbols size bits n (syms ++ [q.1]) q.2 >>= F := by
  simp only [readSimpleSymbols]
  cases readInt bits bs with
  | none => rfl
  | some q =>
    obtain ⟨v, r⟩ := q
    show ((if size ≤ v ∨ syms.contains v = true then none else readSimpleSymbols size bits n (syms ++ [v]) r) >>= F) =
      (if size ≤ v ∨ syms.contains v = true then none else readSimpleSymbols size bits n (syms ++ [v]) r >>= F)
    by_cases c : size ≤ v ∨ syms.contains v = true
    · rw [ite_eq_left c, ite_eq_left c]
      rfl
    · rw [ite_eq_right c, ite_eq_right c]

theorem simpleChain_eq (size : Nat) (bs : List Bool) : readSimple size bs = simpleChain size (alphabetBits size) bs := by
  show (readInt 2 bs >>= fun q => readSimpleSymbols size (alphabetBits size) (q.1 + 1) [] q.2 >>= simpleFinish size) = _
  unfold simpleChain
  generalize alphabetBits size = bits
  cases h : readInt 2 bs with
  | none => rfl
  | some p =>
    obtain ⟨n, bs1⟩ := p
    have hn : n < 4 := by simpa using readInt_lt 2 bs n bs1 h
    show (readSimpleSymbols size bits (n + 1) [] bs1 >>= simpleFinish size) = simpleC1 size bits n bs1
    rw [sym_step]
    unfold simpleC1
    apply bind_ext
    intro q1
    refine ite_congr' (by simp) rfl fun _ => ?_
    unfold simpleN1
    by_cases n0 : n = 0
    · subst n0
      rfl
    rw [ite_eq_right n0]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sym_step]
    unfold simpleC2
    apply bind_ext
    intro q2
    refine ite_congr' (by simp) rfl fun _ => ?_
    unfold simpleN2
    by_cases n1 : m + 1 = 1
    · have : m = 0 := by omega
      subst this
      rfl
    rw [ite_eq_right n1]
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [sym_step]
    unfold simpleC3
    apply bind_ext
    intro q3
    refine ite_congr' (by simp) rfl fun _ => ?_
    unfold simpleN3
    by_cases n2 : j + 1 + 1 = 2
    · have : j = 0 := by omega
      subst this
      rfl
    rw [ite_eq_right n2]
    have : j = 1 := by omega
    subst this
    rw [sym_step]
    unfold simpleC4
    apply bind_ext
    intro q4
    exact ite_congr' (by simp) rfl fun _ => rfl

/-- The code a simple prefix code's symbols and shape give: `e` is NSYM - 1, or 7 for the second shape of four. -/
def simpleCode (size s1 s2 s3 s4 e : Nat) : PrefixCode :=
  if e = 0 then .single s1
  else if e = 1 then .canonical (lengthsOf size [(s1, 1), (s2, 1)])
  else if e = 2 then .canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 2)])
  else if e = 3 then .canonical (lengthsOf size [(s1, 2), (s2, 2), (s3, 2), (s4, 2)])
  else .canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 3), (s4, 3)])

/-- Reads a simple prefix code after its first two bits: its symbols into `a` to `d`, and its shape into `e`. -/
def simpleFast (size bits : UInt64) (b0 : BitBuffer) : Rd :=
  if 2 ≤ b0.count then
    let nsym := b0.peek 2
    let b1 := b0.drop 2
    if bits ≤ b1.count then
      let s1 := b1.peek bits
      let b2 := b1.drop bits
      if size ≤ s1 then Rd.bad b0
      else if nsym = 0 then Rd.ok b2 s1 0 0 0 0
      else if bits ≤ b2.count then
        let s2 := b2.peek bits
        let b3 := b2.drop bits
        if size ≤ s2 ∨ s2 = s1 then Rd.bad b0
        else if nsym = 1 then Rd.ok b3 s1 s2 0 0 1
        else if bits ≤ b3.count then
          let s3 := b3.peek bits
          let b4 := b3.drop bits
          if size ≤ s3 ∨ s3 = s1 ∨ s3 = s2 then Rd.bad b0
          else if nsym = 2 then Rd.ok b4 s1 s2 s3 0 2
          else if bits ≤ b4.count then
            let s4 := b4.peek bits
            let b5 := b4.drop bits
            if size ≤ s4 ∨ s4 = s1 ∨ s4 = s2 ∨ s4 = s3 then Rd.bad b0
            else if 1 ≤ b5.count then
              if b5.peek 1 = 0 then Rd.ok (b5.drop 1) s1 s2 s3 s4 3 else Rd.ok (b5.drop 1) s1 s2 s3 s4 7
            else Rd.short b0
          else Rd.short b0
        else Rd.short b0
      else Rd.short b0
    else Rd.short b0
  else Rd.short b0

private theorem cond_le {a b : UInt64} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt64.le_iff_toNat_le

private theorem cond_eq {a b : UInt64} : a = b ↔ a.toNat = b.toNat :=
  ⟨fun h => by rw [h], fun h => UInt64.toNat_inj.mp h⟩

/-- The code a simple prefix code's read gives. -/
def simpleValue (size : UInt64) (r : Rd) : PrefixCode :=
  simpleCode size.toNat r.a.toNat r.b.toNat r.c.toNat r.d.toNat r.e.toNat

theorem simpleFast_ok {size bits : UInt64} {b0 : BitBuffer} (hw : b0.Wf) (hb : bits.toNat ≤ 10) :
    ROk (simpleChain size.toNat bits.toNat) b0 b0 43 (simpleFast size bits b0) (simpleValue size (simpleFast size bits b0)) := by
  have hb64 : bits.toNat < 64 := by omega
  have h2n : (2 : UInt64).toNat = 2 := rfl
  unfold simpleFast simpleChain
  by_cases h2 : 2 ≤ b0.count
  · rw [ite_eq_left h2]
    refine ROk.intOk (k := 2) (by decide) h2 ?_
    dsimp only
    have hw1 := drop_wf' hw (k := 2) (by decide) h2
    generalize b0.drop 2 = b1 at hw1 ⊢
    generalize b0.peek 2 = n
    unfold simpleC1
    by_cases c1 : bits ≤ b1.count
    · rw [ite_eq_left c1]
      refine ROk.intOk hb64 c1 ?_
      dsimp only
      have hw2 := drop_wf' hw1 hb64 c1
      generalize b1.drop bits = b2 at hw2 ⊢
      generalize b1.peek bits = s1
      by_cases d1 : size ≤ s1
      · rw [ite_eq_left d1]
        simp only [cond_le.mp d1, ↓reduceIte]
        exact ROk.reject (fun _ => rfl)
      rw [ite_eq_right d1]
      have d1' : ¬ size.toNat ≤ s1.toNat := fun h => d1 (cond_le.mpr h)
      simp only [d1', ↓reduceIte]
      unfold simpleN1
      by_cases n0 : n = 0
      · rw [ite_eq_left n0]
        have e : n.toNat = 0 := eq_toNat n0
        simp only [e, ↓reduceIte]
        exact ROk.done hw2 (fun f => rfl) _ _ _ _ _
      rw [ite_eq_right n0]
      have n0' : ¬ n.toNat = 0 := ne_toNat n0
      simp only [n0', ↓reduceIte]
      unfold simpleC2
      by_cases c2 : bits ≤ b2.count
      · rw [ite_eq_left c2]
        refine ROk.intOk hb64 c2 ?_
        dsimp only
        have hw3 := drop_wf' hw2 hb64 c2
        generalize b2.drop bits = b3 at hw3 ⊢
        generalize b2.peek bits = s2
        by_cases d2 : size ≤ s2 ∨ s2 = s1
        · rw [ite_eq_left d2]
          have d2' : size.toNat ≤ s2.toNat ∨ s2.toNat = s1.toNat := by
            rcases d2 with c | c
            · exact Or.inl (cond_le.mp c)
            · exact Or.inr (cond_eq.mp c)
          simp only [d2', ↓reduceIte]
          exact ROk.reject (fun _ => rfl)
        rw [ite_eq_right d2]
        have d2' : ¬ (size.toNat ≤ s2.toNat ∨ s2.toNat = s1.toNat) := by
          intro hc
          rcases hc with c | c
          · exact d2 (Or.inl (cond_le.mpr c))
          · exact d2 (Or.inr (cond_eq.mpr c))
        simp only [d2', ↓reduceIte]
        unfold simpleN2
        by_cases n1 : n = 1
        · rw [ite_eq_left n1]
          have e : n.toNat = 1 := eq_toNat n1
          simp only [e, ↓reduceIte]
          exact ROk.done hw3 (fun f => rfl) _ _ _ _ _
        rw [ite_eq_right n1]
        have n1' : ¬ n.toNat = 1 := ne_toNat n1
        simp only [n1', ↓reduceIte]
        unfold simpleC3
        by_cases c3 : bits ≤ b3.count
        · rw [ite_eq_left c3]
          refine ROk.intOk hb64 c3 ?_
          dsimp only
          have hw4 := drop_wf' hw3 hb64 c3
          generalize b3.drop bits = b4 at hw4 ⊢
          generalize b3.peek bits = s3
          by_cases d3 : size ≤ s3 ∨ s3 = s1 ∨ s3 = s2
          · rw [ite_eq_left d3]
            have d3' : size.toNat ≤ s3.toNat ∨ s3.toNat = s1.toNat ∨ s3.toNat = s2.toNat := by
              rcases d3 with c | c | c
              · exact Or.inl (cond_le.mp c)
              · exact Or.inr (Or.inl (cond_eq.mp c))
              · exact Or.inr (Or.inr (cond_eq.mp c))
            simp only [d3', ↓reduceIte]
            exact ROk.reject (fun _ => rfl)
          rw [ite_eq_right d3]
          have d3' : ¬ (size.toNat ≤ s3.toNat ∨ s3.toNat = s1.toNat ∨ s3.toNat = s2.toNat) := by
            intro hc
            rcases hc with c | c | c
            · exact d3 (Or.inl (cond_le.mpr c))
            · exact d3 (Or.inr (Or.inl (cond_eq.mpr c)))
            · exact d3 (Or.inr (Or.inr (cond_eq.mpr c)))
          simp only [d3', ↓reduceIte]
          unfold simpleN3
          by_cases n2 : n = 2
          · rw [ite_eq_left n2]
            have e : n.toNat = 2 := eq_toNat n2
            simp only [e, ↓reduceIte]
            exact ROk.done hw4 (fun f => rfl) _ _ _ _ _
          rw [ite_eq_right n2]
          have n2' : ¬ n.toNat = 2 := ne_toNat n2
          simp only [n2', ↓reduceIte]
          unfold simpleC4
          by_cases c4 : bits ≤ b4.count
          · rw [ite_eq_left c4]
            refine ROk.intOk hb64 c4 ?_
            dsimp only
            have hw5 := drop_wf' hw4 hb64 c4
            generalize b4.drop bits = b5 at hw5 ⊢
            generalize b4.peek bits = s4
            by_cases d4 : size ≤ s4 ∨ s4 = s1 ∨ s4 = s2 ∨ s4 = s3
            · rw [ite_eq_left d4]
              have d4' : size.toNat ≤ s4.toNat ∨ s4.toNat = s1.toNat ∨ s4.toNat = s2.toNat ∨ s4.toNat = s3.toNat := by
                rcases d4 with c | c | c | c
                · exact Or.inl (cond_le.mp c)
                · exact Or.inr (Or.inl (cond_eq.mp c))
                · exact Or.inr (Or.inr (Or.inl (cond_eq.mp c)))
                · exact Or.inr (Or.inr (Or.inr (cond_eq.mp c)))
              simp only [d4', ↓reduceIte]
              exact ROk.reject (fun _ => rfl)
            rw [ite_eq_right d4]
            have d4' : ¬ (size.toNat ≤ s4.toNat ∨ s4.toNat = s1.toNat ∨ s4.toNat = s2.toNat ∨ s4.toNat = s3.toNat) := by
              intro hc
              rcases hc with c | c | c | c
              · exact d4 (Or.inl (cond_le.mpr c))
              · exact d4 (Or.inr (Or.inl (cond_eq.mpr c)))
              · exact d4 (Or.inr (Or.inr (Or.inl (cond_eq.mpr c))))
              · exact d4 (Or.inr (Or.inr (Or.inr (cond_eq.mpr c))))
            simp only [d4', ↓reduceIte]
            unfold simpleC5
            by_cases c5 : 1 ≤ b5.count
            · rw [ite_eq_left c5]
              refine ROk.intOk (k := 1) (by decide) c5 ?_
              dsimp only
              have hw6 := drop_wf' hw5 (k := 1) (by decide) c5
              by_cases t0 : b5.peek 1 = 0
              · rw [ite_eq_left t0]
                have e : (b5.peek 1).toNat = 0 := eq_toNat t0
                simp only [e, ↓reduceIte]
                exact ROk.done hw6 (fun f => rfl) _ _ _ _ _
              · rw [ite_eq_right t0]
                have e : ¬ (b5.peek 1).toNat = 0 := ne_toNat t0
                simp only [e, ↓reduceIte]
                exact ROk.done hw6 (fun f => rfl) _ _ _ _ _
            · rw [ite_eq_right c5]
              exact ROk.intShort (not_le_lt c5) (by omega)
          · rw [ite_eq_right c4]
            exact ROk.intShort (not_le_lt c4) (by omega)
        · rw [ite_eq_right c3]
          exact ROk.intShort (not_le_lt c3) (by omega)
      · rw [ite_eq_right c2]
        exact ROk.intShort (not_le_lt c2) (by omega)
    · rw [ite_eq_right c1]
      exact ROk.intShort (not_le_lt c1) (by omega)
  · rw [ite_eq_right h2]
    exact ROk.intShort (not_le_lt h2) (by decide)

/-- A read's four values fit an array index. -/
def SmallVals (r : Rd) : Prop := r.a.toNat < 2 ^ 32 ∧ r.b.toNat < 2 ^ 32 ∧ r.c.toNat < 2 ^ 32 ∧ r.d.toNat < 2 ^ 32

/-- A simple code's symbols fit an array index. -/
theorem simpleFast_small (size bits : UInt64) (b0 : BitBuffer) (hb : bits.toNat ≤ 10) : SmallVals (simpleFast size bits b0) := by
  have hpeek : ∀ b : BitBuffer, (b.peek bits).toNat < 2 ^ 32 := by
    intro b
    have h1 := peek_lt b (k := bits) (by omega)
    have h2 : 2 ^ bits.toNat ≤ 2 ^ 10 := Nat.pow_le_pow_right (by decide) hb
    have h3 : (2 : Nat) ^ 10 = 1024 := rfl
    omega
  have hz : (0 : UInt64).toNat < 2 ^ 32 := by decide
  have hite : ∀ {c : Prop} [Decidable c] {x y : Rd}, SmallVals x → SmallVals y → SmallVals (if c then x else y) := by
    intro c _ x y hx hy
    by_cases h : c
    · rw [ite_eq_left h]
      exact hx
    · rw [ite_eq_right h]
      exact hy
  unfold simpleFast
  dsimp only
  repeat' refine hite ?_ ?_
  all_goals refine ⟨?_, ?_, ?_, ?_⟩ <;> first | exact hz | exact hpeek _

/-- `ALPHABET_BITS`, as a chain of comparisons. -/
@[inline] def alphabetBitsFast (size : UInt64) : UInt64 :=
  if size ≤ 1 then 0
  else if size ≤ 2 then 1
  else if size ≤ 4 then 2
  else if size ≤ 8 then 3
  else if size ≤ 16 then 4
  else if size ≤ 32 then 5
  else if size ≤ 64 then 6
  else if size ≤ 128 then 7
  else if size ≤ 256 then 8
  else if size ≤ 512 then 9
  else 10

private theorem alphabetBits_table : ∀ n, n ≤ 1024 →
    alphabetBits n = if n ≤ 1 then 0 else if n ≤ 2 then 1 else if n ≤ 4 then 2 else if n ≤ 8 then 3 else if n ≤ 16 then 4
      else if n ≤ 32 then 5 else if n ≤ 64 then 6 else if n ≤ 128 then 7 else if n ≤ 256 then 8 else if n ≤ 512 then 9
      else 10 := by
  decide +kernel

theorem alphabetBitsFast_toNat {size : UInt64} (h : size.toNat ≤ 1024) :
    (alphabetBitsFast size).toNat = alphabetBits size.toNat ∧ (alphabetBitsFast size).toNat ≤ 10 := by
  have le_ite : ∀ (k : UInt64) (m : Nat) (x y : UInt64), k.toNat = m →
      (if size ≤ k then x else y) = (if size.toNat ≤ m then x else y) := by
    intro k m x y hm
    by_cases c : size ≤ k
    · rw [ite_eq_left c, ite_eq_left (by rw [← hm]; exact cond_le.mp c)]
    · rw [ite_eq_right c, ite_eq_right (by rw [← hm]; exact fun e => c (cond_le.mpr e))]
  rw [alphabetBits_table _ h]
  unfold alphabetBitsFast
  rw [le_ite 512 512 _ _ rfl, le_ite 256 256 _ _ rfl, le_ite 128 128 _ _ rfl, le_ite 64 64 _ _ rfl, le_ite 32 32 _ _ rfl,
    le_ite 16 16 _ _ rfl, le_ite 8 8 _ _ rfl, le_ite 4 4 _ _ rfl, le_ite 2 2 _ _ rfl, le_ite 1 1 _ _ rfl]
  generalize size.toNat = n at h
  repeat' split
  all_goals first | exact ⟨rfl, by decide⟩ | omega

/-! ### Reads through a table -/

section Tabled

variable {t : ByteArray} {base : USize} {hfit : TableFits t base.toNat} {h32 : t.size < 2 ^ 32} {code : PrefixCode}

/-- A block count, once its symbol is looked up. -/
@[inline] def countFinish (b0 : BitBuffer) (v : UInt64) : Rd :=
  if hc : wordSym v < 26 then
    let row := countRow (wordSym v) (lt26 hc)
    let b1 := b0.drop (wordBits v)
    if rowBits row ≤ b1.count then Rd.ok (b1.drop (rowBits row)) (rowBase row + b1.peek (rowBits row)) 0 0 0 0
    else Rd.short b0
  else Rd.bad b0

/-- Reads a block count, into `a`. -/
def blockCountFast (t : ByteArray) (base : USize) (hfit : TableFits t base.toNat) (h32 : t.size < 2 ^ 32) (b0 : BitBuffer) : Rd :=
  let v := lookup t base b0.word hfit h32
  if wordBits v ≤ b0.count then countFinish b0 v else Rd.short b0

private theorem rows_fit' {c bits lowest high : Nat} (h : blockCountCodes[c]? = some (bits, lowest, high)) :
    bits ≤ 24 ∧ lowest + 2 ^ bits ≤ 16793841 := by
  have hmem := List.mem_of_getElem? h
  have h1 := blockCountCodes_extraBits.1 _ hmem
  have h2 := blockCountCodes_ranges _ hmem
  have h3 := blockCountCodes_largest.1 _ hmem
  have hp : 0 < 2 ^ bits := Nat.two_pow_pos _
  simp only at h1 h2 h3
  omega

theorem blockCountFast_ok {b0 : BitBuffer} (hw : b0.Wf) (hok : TableOk t base.toNat code) (hC : Complete code)
    (hs : code.Symbols blockCountAlphabetSize) :
    ROk (readBlockCount code) b0 b0 39 (blockCountFast t base hfit h32 b0) (blockCountFast t base hfit h32 b0).a.toNat := by
  unfold blockCountFast readBlockCount
  dsimp only
  refine ROk.congr (spec' := fun bs => decodeSymbol code bs >>= fun p =>
    blockCountCodes[p.1]? >>= fun q => readInt q.1 p.2 >>= fun e => some (q.2.1 + e.1, e.2)) ?_ (fun bs => rfl)
  have L := lookup_read (b := b0) hok hfit h32 hC
  dsimp only at L
  obtain ⟨hle15, _, _⟩ := L
  split
  · rename_i hl
    refine ROk.symOk hok hC hl ?_
    dsimp only
    have hw1 := drop_wf' hw (wordBits_lt _) hl
    have hsym : wordValue (lookup t base b0.word hfit h32) < blockCountAlphabetSize := by
      have L := lookup_read (b := b0) hok hfit h32 hC
      dsimp only at L
      have := L.2.1 hl []
      rw [List.append_nil, List.append_nil] at this
      exact decodeSymbol_lt hs this
    generalize lookup t base b0.word hfit h32 = v at hl hw1 hsym hle15 ⊢
    have hsym26 : (wordSym v).toNat < 26 := hsym
    have hcU : wordSym v < 26 := UInt64.lt_iff_toNat_lt.mpr hsym26
    unfold countFinish
    rw [dite_eq_left hcU]
    dsimp only
    obtain ⟨⟨bits, lowest, high⟩, hrow⟩ := blockCount_table hsym
    obtain ⟨hb24, hmax⟩ := rows_fit' hrow
    have hgetD : blockCountCodes.getD (wordSym v).toNat (0, 0, 0) = (bits, lowest, high) := by
      rw [List.getD_eq_getElem?_getD]
      show (blockCountCodes[wordValue v]?).getD _ = _
      rw [hrow]
      rfl
    obtain ⟨hk, hlo⟩ := countRow_fields (lt26 hcU)
    rw [hgetD] at hk hlo
    generalize countRow (wordSym v) (lt26 hcU) = row at hk hlo ⊢
    have hk' : (rowBits row).toNat = bits := hk
    have hlo' : (rowBase row).toNat = lowest := hlo
    generalize b0.drop (wordBits v) = b1 at hw1 ⊢
    refine ROk.congr (spec' := fun bs => readInt (rowBits row).toNat bs >>= fun e => some (lowest + e.1, e.2)) ?_ (fun bs => by
      show (blockCountCodes[wordValue v]? >>= _) = _
      rw [hrow, hk']
      rfl)
    split
    · rename_i hc3
      refine ROk.intOk (by omega) hc3 ?_
      have hx : (b1.peek (rowBits row)).toNat < 2 ^ bits := by
        have := peek_lt b1 (k := rowBits row) (by omega)
        rwa [hk'] at this
      have hsum : (rowBase row + b1.peek (rowBits row)).toNat = lowest + (b1.peek (rowBits row)).toNat := by
        rw [UInt64.toNat_add, hlo']
        exact Nat.mod_eq_of_lt (by have : (16793841 : Nat) < 2 ^ 64 := by decide
                                   omega)
      refine ROk.done (drop_wf' hw1 (by omega) hc3) (fun f => ?_) _ _ _ _ _
      simp only [Rd.ok]
      rw [hsum]
    · rename_i hc3
      refine ROk.intShort (not_le_lt hc3) ?_
      have := wordBits_lt v
      omega
  · rename_i hl
    exact ROk.symShort hok hC hl (by omega)

/-- One symbol of a context map's values: a value and a run of 1, or a run of zeros. -/
def mapSym (rlemax : Nat) (code : PrefixCode) (bs : List Bool) : Option ((Nat × Nat) × List Bool) :=
  decodeSymbol code bs >>= fun p =>
    match contextMapValue rlemax p.1 with
    | some v => some ((v, 1), p.2)
    | none => readInt p.1 p.2 >>= fun q => some ((0, (1 <<< p.1) + q.1), q.2)

/-- Reads one symbol of a context map's values: the value into `a`, and the run into `b`. -/
def mapSymFast (t : ByteArray) (base : USize) (hfit : TableFits t base.toNat) (h32 : t.size < 2 ^ 32) (rlemax : UInt64)
    (b0 : BitBuffer) : Rd :=
  let v := lookup t base b0.word hfit h32
  if wordBits v ≤ b0.count then
    let sym := wordSym v
    let b1 := b0.drop (wordBits v)
    if sym = 0 then Rd.ok b1 0 1 0 0 0
    else if sym ≤ rlemax then
      if sym ≤ b1.count then Rd.ok (b1.drop sym) 0 ((1 <<< sym) + b1.peek sym) 0 0 0
      else Rd.short b0
    else Rd.ok b1 (sym - rlemax) 1 0 0 0
  else Rd.short b0

theorem mapSymFast_ok {b0 : BitBuffer} {rlemax : UInt64} (hw : b0.Wf) (hok : TableOk t base.toNat code) (hC : Complete code)
    (hr : rlemax.toNat ≤ 16) :
    ROk (mapSym rlemax.toNat code) b0 b0 31 (mapSymFast t base hfit h32 rlemax b0)
      ((mapSymFast t base hfit h32 rlemax b0).a.toNat, (mapSymFast t base hfit h32 rlemax b0).b.toNat) := by
  unfold mapSymFast mapSym
  dsimp only
  split
  · rename_i hl
    refine ROk.symOk hok hC hl ?_
    dsimp only
    have hw1 := drop_wf' hw (wordBits_lt _) hl
    have hle15 := (lookup_read (b := b0) (hfit := hfit) (h32 := h32) hok hC).1
    generalize lookup t base b0.word hfit h32 = v at hl hw1 hle15 ⊢
    have hbits := wordBits_lt v
    show ROk (fun bs => match contextMapValue rlemax.toNat (wordSym v).toNat with
      | some v => some ((v, 1), bs)
      | none => readInt (wordSym v).toNat bs >>= fun q => some ((0, (1 <<< (wordSym v).toNat) + q.1), q.2)) _ _ _ _ _
    generalize wordSym v = sym
    generalize b0.drop (wordBits v) = b1 at hw1 ⊢
    by_cases h0 : sym = 0
    · rw [ite_eq_left h0]
      have e : contextMapValue rlemax.toNat sym.toNat = some 0 := by
        have : sym.toNat = 0 := eq_toNat h0
        simp [contextMapValue, this]
      simp only [e]
      exact ROk.done hw1 (fun f => rfl) _ _ _ _ _
    rw [ite_eq_right h0]
    have h0' : ¬ sym.toNat = 0 := ne_toNat h0
    by_cases hle : sym ≤ rlemax
    · rw [ite_eq_left hle]
      have hle' := cond_le.mp hle
      have e : contextMapValue rlemax.toNat sym.toNat = none := by
        simp [contextMapValue, h0', hle']
      simp only [e]
      split
      · rename_i hc
        refine ROk.intOk (by omega) hc ?_
        have hx : (b1.peek sym).toNat < 2 ^ sym.toNat := peek_lt b1 (by omega)
        have hsh := one_shl' (d := sym) (by omega)
        have hp : 2 ^ sym.toNat ≤ 2 ^ 16 := Nat.pow_le_pow_right (by decide) (by omega)
        have h216 : (2 : Nat) ^ 16 = 65536 := rfl
        have hsum : ((1 <<< sym) + b1.peek sym).toNat = 2 ^ sym.toNat + (b1.peek sym).toNat := by
          rw [UInt64.toNat_add, hsh]
          exact Nat.mod_eq_of_lt (by omega)
        refine ROk.done (drop_wf' hw1 (by omega) hc) (fun f => ?_) _ _ _ _ _
        simp only [Rd.ok]
        rw [hsum, nat_shl_one]
        rfl
      · rename_i hc
        exact ROk.intShort (not_le_lt hc) (by omega)
    · rw [ite_eq_right hle]
      have hle' : ¬ sym.toNat ≤ rlemax.toNat := fun h => hle (cond_le.mpr h)
      have e : contextMapValue rlemax.toNat sym.toNat = some (sym.toNat - rlemax.toNat) := by
        simp [contextMapValue, h0', hle']
      simp only [e]
      have hsub : (sym - rlemax).toNat = sym.toNat - rlemax.toNat :=
        UInt64.toNat_sub_of_le _ _ (cond_le.mpr (by omega))
      refine ROk.done hw1 (fun f => ?_) _ _ _ _ _
      simp only [Rd.ok]
      rw [hsub]
      rfl
  · rename_i hl
    exact ROk.symShort hok hC hl (by omega)

/-- One code length symbol and its extra bits. -/
def lenSym (clc : PrefixCode) (bs : List Bool) : Option ((Nat × Nat) × List Bool) :=
  decodeSymbol clc bs >>= fun p =>
    readInt (if p.1 = 16 then 2 else if p.1 = 17 then 3 else 0) p.2 >>= fun q => some ((p.1, q.1), q.2)

/-- Reads one code length symbol into `a`, and its extra bits' value into `b`. -/
def lenSymFast (t : ByteArray) (base : USize) (hfit : TableFits t base.toNat) (h32 : t.size < 2 ^ 32) (b0 : BitBuffer) : Rd :=
  let v := lookup t base b0.word hfit h32
  if wordBits v ≤ b0.count then
    let sym := wordSym v
    let b1 := b0.drop (wordBits v)
    let k : UInt64 := if sym = 16 then 2 else if sym = 17 then 3 else 0
    if k ≤ b1.count then Rd.ok (b1.drop k) sym (b1.peek k) 0 0 0
    else Rd.short b0
  else Rd.short b0

theorem lenSymFast_ok {b0 : BitBuffer} (hw : b0.Wf) (hok : TableOk t base.toNat code) (hC : Complete code) :
    ROk (lenSym code) b0 b0 18 (lenSymFast t base hfit h32 b0)
      ((lenSymFast t base hfit h32 b0).a.toNat, (lenSymFast t base hfit h32 b0).b.toNat) := by
  unfold lenSymFast lenSym
  dsimp only
  split
  · rename_i hl
    refine ROk.symOk hok hC hl ?_
    dsimp only
    have hw1 := drop_wf' hw (wordBits_lt _) hl
    have hle15 := (lookup_read (b := b0) (hfit := hfit) (h32 := h32) hok hC).1
    generalize lookup t base b0.word hfit h32 = v at hl hw1 hle15 ⊢
    have hbits := wordBits_lt v
    show ROk (fun bs => readInt (if (wordSym v).toNat = 16 then 2 else if (wordSym v).toNat = 17 then 3 else 0) bs >>=
      fun q => some (((wordSym v).toNat, q.1), q.2)) _ _ _ _ _
    generalize wordSym v = sym
    generalize b0.drop (wordBits v) = b1 at hw1 ⊢
    have hk : (if sym = 16 then (2 : UInt64) else if sym = 17 then 3 else 0).toNat =
        if sym.toNat = 16 then 2 else if sym.toNat = 17 then 3 else 0 := by
      by_cases h16 : sym = 16
      · rw [ite_eq_left h16, ite_eq_left (show sym.toNat = 16 from eq_toNat h16)]
        rfl
      · rw [ite_eq_right h16, ite_eq_right (show ¬ sym.toNat = 16 from ne_toNat h16)]
        by_cases h17 : sym = 17
        · rw [ite_eq_left h17, ite_eq_left (show sym.toNat = 17 from eq_toNat h17)]
          rfl
        · rw [ite_eq_right h17, ite_eq_right (show ¬ sym.toNat = 17 from ne_toNat h17)]
          rfl
    have hk3 : (if sym = 16 then (2 : UInt64) else if sym = 17 then 3 else 0).toNat ≤ 3 := by
      rw [hk]
      split
      · omega
      · split <;> omega
    rw [← hk]
    generalize (if sym = 16 then (2 : UInt64) else if sym = 17 then 3 else 0) = k at hk3 ⊢
    split
    · rename_i hc
      refine ROk.intOk (by omega) hc ?_
      exact ROk.done (drop_wf' hw1 (by omega) hc) (fun f => rfl) _ _ _ _ _
    · rename_i hc
      refine ROk.intShort (not_le_lt hc) (by omega)
  · rename_i hl
    exact ROk.symShort hok hC hl (by omega)

end Tabled

end Brotli.Decoder
