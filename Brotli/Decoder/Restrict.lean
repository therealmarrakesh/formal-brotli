module

public import Brotli.Decoder.StreamOrder

@[expose] public section

/-!
# The reading in order looks at no bit it doesn't take

Each of the spec's reads looks at no bit after the ones it takes: from those bits followed by any others, it reads the
same. So does each step of the reading in order, from any bits whose length is the same modulo 8, since the fill bits
before a byte boundary depend on that length. So a stream's reading in order reaches, from a stream's first bytes, what it
reaches from more bytes when it has not read into the bytes added.
-/

namespace Brotli.Decoder

open Brotli.Spec

section
variable {A B C : Type}

/-- A read that looks at no bit after the ones it takes. -/
def Faith (rd : List Bool → Option (A × List Bool)) : Prop :=
  ∀ bs v r, rd bs = some (v, r) → ∃ u, bs = u ++ r ∧ ∀ t, rd (u ++ t) = some (v, t)

theorem faith_some (f : A) : Faith fun bs => some (f, bs) := by
  intro bs v r h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨[], rfl, fun _ => rfl⟩

theorem faith_none : Faith fun _ => (none : Option (A × List Bool)) := by
  intro _ _ _ h
  cases h

theorem faith_ite {c : Prop} [Decidable c] {f g : List Bool → Option (A × List Bool)} (hf : Faith f) (hg : Faith g) :
    Faith fun bs => if c then f bs else g bs := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf
  · simpa only [h, ↓reduceIte] using hg

theorem faith_bind {rd1 : List Bool → Option (A × List Bool)} {rd2 : A × List Bool → Option (B × List Bool)} (h1 : Faith rd1)
    (h2 : ∀ a, Faith fun bs => rd2 (a, bs)) : Faith fun bs => rd1 bs >>= rd2 := by
  intro bs v r h
  have h' : rd1 bs >>= rd2 = some (v, r) := h
  cases e1 : rd1 bs with
  | none => rw [e1] at h'; simp at h'
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [e1] at h'
    obtain ⟨u2, eb, hu2⟩ := h2 a b v r h'
    obtain ⟨u1, ebs, hu1⟩ := h1 bs a b e1
    refine ⟨u1 ++ u2, by rw [ebs, eb, List.append_assoc], fun t => ?_⟩
    show rd1 (u1 ++ u2 ++ t) >>= rd2 = _
    rw [List.append_assoc, hu1]
    exact hu2 t

/-- A value looked up, not read, then a read. -/
theorem faith_obind {o : Option C} {k : C → List Bool → Option (B × List Bool)} (h : ∀ c, Faith (k c)) :
    Faith fun bs => o >>= fun c => k c bs := by
  cases o with
  | none =>
    intro _ _ _ hn
    simp at hn
  | some c => exact h c

/-- A read that takes the bits it reads, and from those alone reads the same, looks at no bit after them. -/
theorem faith_of_split {rd : List Bool → Option (A × List Bool)}
    (hs : ∀ bs v r, rd bs = some (v, r) → ∃ u, bs = u ++ r ∧ rd u = some (v, []))
    (he : ∀ u t v, rd u = some (v, []) → rd (u ++ t) = some (v, t)) : Faith rd := by
  intro bs v r h
  obtain ⟨u, rfl, hu⟩ := hs bs v r h
  exact ⟨u, rfl, fun t => he u t v hu⟩

end

/-- Of two ways to cut the same bits, the one with the longer first part starts with the other's. -/
private theorem prefix_of {u r w s : List Bool} (h : u ++ r = w ++ s) (hl : w.length ≤ u.length) : ∃ m, u = w ++ m := by
  obtain ⟨m, hm⟩ := List.prefix_of_prefix_length_le ⟨s, h.symm⟩ ⟨r, rfl⟩ hl
  exact ⟨m, hm.symm⟩

/-! ### The spec's reads -/

theorem faith_readInt : ∀ n, Faith (readInt n)
  | 0 => by
    intro bs v r h
    simp only [readInt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, fun t => by simp [readInt]⟩
  | n + 1 => by
    intro bs v r h
    cases bs with
    | nil => simp [readInt] at h
    | cons b s =>
      simp only [readInt] at h
      cases e : readInt n s with
      | none => simp [e] at h
      | some p =>
        obtain ⟨w, rest⟩ := p
        simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨u, hu, hk⟩ := faith_readInt n s w rest e
        exact ⟨b :: u, by rw [hu]; rfl, fun t => by simp only [List.cons_append, readInt, hk t, Option.map_some]⟩

theorem faith_readCode (n : Nat) : Faith (readCode n) :=
  faith_of_split (readCode_split n) fun _ t _ h => by simpa using readCode_ext t h

private theorem dl_faith (lens : List Nat) : ∀ (k len : Nat) (bs : List Bool) (s : Nat) (r : List Bool),
    decodeLengths lens bs len k = some (s, r) →
    ∃ u, bs = u ++ r ∧ len ≤ u.length ∧ ∀ t, decodeLengths lens (u ++ t) len k = some (s, t)
  | 0, _, _, _, _, h => by simp [decodeLengths] at h
  | k + 1, len, bs, s, r, h => by
    simp only [decodeLengths] at h
    cases hr : readCode len bs with
    | none => rw [hr] at h; simp at h
    | some x =>
      obtain ⟨c, rest⟩ := x
      rw [hr] at h
      dsimp only at h
      obtain ⟨w, hw, hw1⟩ := readCode_split len bs c rest hr
      have hwl := readCode_length len w c [] hw1
      simp only [List.length_nil, Nat.add_zero] at hwl
      have hwt : ∀ m, readCode len (w ++ m) = some (c, m) := fun m => by simpa using readCode_ext m hw1
      -- When the length's codes don't hold the symbol, the next length decides, on any bits that start with `w`.
      have hrec : decodeLengths lens bs (len + 1) k = some (s, r) →
          (∀ m, decodeLengths lens (w ++ m) len (k + 1) = decodeLengths lens (w ++ m) (len + 1) k) →
          ∃ u, bs = u ++ r ∧ len ≤ u.length ∧ ∀ t, decodeLengths lens (u ++ t) len (k + 1) = some (s, t) := by
        intro h1 hm
        obtain ⟨u, hu, hul, hk⟩ := dl_faith lens k (len + 1) bs s r h1
        obtain ⟨m, rfl⟩ := prefix_of (hu.symm.trans hw) (by omega)
        refine ⟨w ++ m, hu, by omega, fun t => ?_⟩
        rw [List.append_assoc, hm, ← List.append_assoc]
        exact hk t
      by_cases hle : nextCode lens len ≤ c
      · rw [ite_eq_left hle] at h
        cases hs : (symbolsOfLength lens len)[c - nextCode lens len]? with
        | none =>
          rw [hs] at h
          refine hrec h fun m => ?_
          simp only [decodeLengths, hwt, ite_eq_left hle, hs]
        | some sym =>
          rw [hs] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨w, hw, by omega, fun t => ?_⟩
          simp only [decodeLengths, hwt, ite_eq_left hle, hs]
      · rw [ite_eq_right hle] at h
        refine hrec h fun m => ?_
        simp only [decodeLengths, hwt, ite_eq_right hle]

theorem faith_decodeSymbol (c : PrefixCode) : Faith (decodeSymbol c) := by
  cases c with
  | single sym => exact faith_some sym
  | canonical lens =>
    intro bs v r h
    obtain ⟨u, hu, _, hk⟩ := dl_faith lens 15 1 bs v r h
    exact ⟨u, hu, hk⟩

/-- A variable-length code's table takes the bits of the row it reads. -/
private theorem table_split : ∀ (T : List (Nat × Nat × Nat)) (bs : List Bool) (a : Nat) (r : List Bool),
    T.findSome? (tableStep bs) = some (a, r) → ∃ u, bs = u ++ r ∧ T.findSome? (tableStep u) = some (a, [])
  | [], _, _, _, h => by simp at h
  | f :: T, bs, a, r, h => by
    simp only [List.findSome?_cons] at h ⊢
    obtain ⟨s, n, pr⟩ := f
    cases hf : tableStep bs (s, n, pr) with
    | some x =>
      obtain ⟨a', r'⟩ := x
      rw [hf] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [tableStep] at hf
      cases hr : readInt n bs with
      | none => rw [hr] at hf; cases hf
      | some y =>
        obtain ⟨v, rest⟩ := y
        rw [hr] at hf
        dsimp only at hf
        by_cases hv : v = pr
        · rw [ite_eq_left hv] at hf
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          obtain ⟨u, hu, hk⟩ := faith_readInt n bs v rest hr
          have hu0 : readInt n u = some (v, []) := by simpa using hk []
          refine ⟨u, hu, ?_⟩
          simp only [tableStep, hu0, hv, ↓reduceIte]
        · rw [ite_eq_right hv] at hf
          cases hf
    | none =>
      rw [hf] at h
      dsimp only at h
      obtain ⟨u, hu, hk⟩ := table_split T bs a r h
      refine ⟨u, hu, ?_⟩
      have hn : tableStep u (s, n, pr) = none := by
        simp only [tableStep] at hf ⊢
        cases hu' : readInt n u with
        | none => rfl
        | some y =>
          obtain ⟨v, rest⟩ := y
          have e := readInt_ext n u r v rest hu'
          rw [← hu] at e
          rw [e] at hf
          dsimp only at hf ⊢
          by_cases hv : v = pr
          · rw [ite_eq_left hv] at hf
            cases hf
          · exact ite_eq_right hv
      rw [hn]
      exact hk

theorem faith_readWBITS : Faith readWBITS :=
  faith_of_split (table_split wbitsCode) fun _ t _ h => by simpa using readWBITS_ext t h

theorem faith_readCodeLengthCodeLength : Faith readCodeLengthCodeLength :=
  faith_of_split (table_split codeLengthCodeLengthCode) fun _ t _ h => by simpa using readCodeLengthCodeLength_ext t h

theorem faith_readVarLen : Faith readVarLen := by
  show Faith fun bs => readVarLen bs
  unfold readVarLen
  refine faith_bind (faith_readInt 1) fun a => ?_
  dsimp only
  refine faith_ite (faith_some _) (faith_bind (faith_readInt 3) fun b => ?_)
  dsimp only
  exact faith_ite (faith_some _) (faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_some _)

theorem faith_readRLEMAX : Faith readRLEMAX := by
  show Faith fun bs => readRLEMAX bs
  unfold readRLEMAX
  refine faith_bind (faith_readInt 1) fun _ => ?_
  dsimp only
  exact faith_ite (faith_some _) (faith_bind (faith_readInt 4) fun _ => by dsimp only; exact faith_some _)

theorem faith_readBlockCount (code : PrefixCode) : Faith (readBlockCount code) := by
  show Faith fun bs => readBlockCount code bs
  unfold readBlockCount
  refine faith_bind (faith_decodeSymbol code) fun _ => ?_
  dsimp only
  refine faith_obind fun x => ?_
  obtain ⟨bits, lowest, z⟩ := x
  dsimp only
  exact faith_bind (faith_readInt bits) fun _ => by dsimp only; exact faith_some _

theorem faith_readBlockType (n : Nat) (code : PrefixCode) (bt : BlockTypes) : Faith (readBlockType n code bt) := by
  show Faith fun bs => readBlockType n code bt bs
  unfold readBlockType
  refine faith_bind (faith_decodeSymbol code) fun _ => ?_
  dsimp only
  exact faith_ite faith_none (faith_some _)

theorem faith_nextElement (c : BlockCategory) (st : BlockState) : Faith (nextElement c st) := by
  show Faith fun bs => nextElement c st bs
  unfold nextElement
  refine faith_ite (faith_ite faith_none (faith_bind (faith_readBlockType _ _ _) fun _ => ?_)) (faith_some _)
  dsimp only
  exact faith_bind (faith_readBlockCount _) fun _ => by dsimp only; exact faith_some _

/-! ### The reads of the reading in order -/

theorem faith_readNp : Faith readNp := by
  show Faith fun bs => readNp bs
  unfold readNp
  exact faith_bind (faith_readInt 2) fun _ => by
    dsimp only
    exact faith_bind (faith_readInt 4) fun _ => by dsimp only; exact faith_some _

theorem faith_lenSym (clc : PrefixCode) : Faith (lenSym clc) := by
  show Faith fun bs => lenSym clc bs
  unfold lenSym
  exact faith_bind (faith_decodeSymbol clc) fun a => by
    dsimp only
    exact faith_bind (faith_readInt (if a = 16 then 2 else if a = 17 then 3 else 0)) fun _ => by dsimp only; exact faith_some _

theorem faith_mapSym (rlemax : Nat) (code : PrefixCode) : Faith (mapSym rlemax code) := by
  show Faith fun bs => mapSym rlemax code bs
  unfold mapSym
  refine faith_bind (faith_decodeSymbol code) fun a => ?_
  dsimp only
  cases contextMapValue rlemax a with
  | some v => exact faith_some _
  | none => exact faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_some _

theorem faith_readInsertHalf (code : PrefixCode) : Faith (readInsertHalf code) := by
  show Faith fun bs => readInsertHalf code bs
  unfold readInsertHalf
  refine faith_bind (faith_decodeSymbol code) fun _ => ?_
  dsimp only
  refine faith_obind fun x => ?_
  obtain ⟨_, _⟩ := x
  dsimp only
  refine faith_obind fun y => ?_
  obtain ⟨_, _, _⟩ := y
  dsimp only
  refine faith_obind fun z => ?_
  obtain ⟨_, _, _⟩ := z
  dsimp only
  exact faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_some _

theorem faith_readDistanceParts (npostfix ndirect : Nat) (code : PrefixCode) : Faith (readDistanceParts npostfix ndirect code) := by
  show Faith fun bs => readDistanceParts npostfix ndirect code bs
  unfold readDistanceParts
  exact faith_bind (faith_decodeSymbol code) fun _ => by
    dsimp only
    exact faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_some _

theorem faith_simpleC5 (size s1 s2 s3 s4 : Nat) : Faith (simpleC5 size s1 s2 s3 s4) := by
  show Faith fun bs => simpleC5 size s1 s2 s3 s4 bs
  unfold simpleC5
  exact faith_bind (faith_readInt 1) fun _ => by dsimp only; exact faith_ite (faith_some _) (faith_some _)

theorem faith_simpleC4 (size bits s1 s2 s3 : Nat) : Faith (simpleC4 size bits s1 s2 s3) := by
  show Faith fun bs => simpleC4 size bits s1 s2 s3 bs
  unfold simpleC4
  exact faith_bind (faith_readInt bits) fun _ => by dsimp only; exact faith_ite faith_none (faith_simpleC5 _ _ _ _ _)

theorem faith_simpleN3 (size bits n s1 s2 s3 : Nat) : Faith (simpleN3 size bits n s1 s2 s3) := by
  show Faith fun bs => simpleN3 size bits n s1 s2 s3 bs
  unfold simpleN3
  exact faith_ite (faith_some _) (faith_simpleC4 _ _ _ _ _)

theorem faith_simpleC3 (size bits n s1 s2 : Nat) : Faith (simpleC3 size bits n s1 s2) := by
  show Faith fun bs => simpleC3 size bits n s1 s2 bs
  unfold simpleC3
  exact faith_bind (faith_readInt bits) fun _ => by dsimp only; exact faith_ite faith_none (faith_simpleN3 _ _ _ _ _ _)

theorem faith_simpleN2 (size bits n s1 s2 : Nat) : Faith (simpleN2 size bits n s1 s2) := by
  show Faith fun bs => simpleN2 size bits n s1 s2 bs
  unfold simpleN2
  exact faith_ite (faith_some _) (faith_simpleC3 _ _ _ _ _)

theorem faith_simpleC2 (size bits n s1 : Nat) : Faith (simpleC2 size bits n s1) := by
  show Faith fun bs => simpleC2 size bits n s1 bs
  unfold simpleC2
  exact faith_bind (faith_readInt bits) fun _ => by dsimp only; exact faith_ite faith_none (faith_simpleN2 _ _ _ _ _)

theorem faith_simpleN1 (size bits n s1 : Nat) : Faith (simpleN1 size bits n s1) := by
  show Faith fun bs => simpleN1 size bits n s1 bs
  unfold simpleN1
  exact faith_ite (faith_some _) (faith_simpleC2 _ _ _ _)

theorem faith_simpleC1 (size bits n : Nat) : Faith (simpleC1 size bits n) := by
  show Faith fun bs => simpleC1 size bits n bs
  unfold simpleC1
  exact faith_bind (faith_readInt bits) fun _ => by dsimp only; exact faith_ite faith_none (faith_simpleN1 _ _ _ _)

theorem faith_simpleChain (size bits : Nat) : Faith (simpleChain size bits) := by
  show Faith fun bs => simpleChain size bits bs
  unfold simpleChain
  exact faith_bind (faith_readInt 2) fun _ => by dsimp only; exact faith_simpleC1 _ _ _

theorem faith_msUnc (last : Bool) (mlen : Nat) : Faith (msUnc last mlen) := by
  show Faith fun bs => msUnc last mlen bs
  unfold msUnc
  exact faith_ite (faith_some _) (faith_bind (faith_readInt 1) fun a => faith_some (MetaStart.data false mlen (a = 1)))

theorem faith_msLen (last : Bool) (mn : Nat) : Faith (msLen last mn) := by
  show Faith fun bs => msLen last mn bs
  unfold msLen
  exact faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_ite faith_none (faith_msUnc _ _)

theorem faith_msSkip (last : Bool) (n : Nat) : Faith (msSkip last n) := by
  show Faith fun bs => msSkip last n bs
  unfold msSkip
  exact faith_bind (faith_readInt _) fun _ => by dsimp only; exact faith_ite faith_none (faith_some _)

theorem faith_msBody (last : Bool) : Faith (msBody last) := by
  show Faith fun bs => msBody last bs
  unfold msBody
  refine faith_bind (faith_readInt 2) fun _ => ?_
  dsimp only
  refine faith_ite (faith_bind (faith_readInt 1) fun _ => ?_) (faith_msLen _ _)
  dsimp only
  exact faith_ite faith_none (faith_bind (faith_readInt 2) fun _ => by dsimp only; exact faith_msSkip _ _)

theorem faith_metaStart : Faith metaStart := by
  show Faith fun bs => metaStart bs
  unfold metaStart
  refine faith_bind (faith_readInt 1) fun _ => ?_
  dsimp only
  exact faith_ite (faith_msBody _) (faith_bind (faith_readInt 1) fun _ => by
    dsimp only
    exact faith_ite (faith_some _) (faith_msBody _))

/-- The fill bits look at no bit after them, on bits whose length is the same modulo 8. -/
theorem faith_readFill {bs r : List Bool} (h : readFill bs = some r) :
    ∃ u, bs = u ++ r ∧ ∀ t : List Bool, t.length % 8 = r.length % 8 → readFill (u ++ t) = some t := by
  unfold readFill at h
  cases e : readInt (bs.length % 8) bs with
  | none => rw [e] at h; simp at h
  | some p =>
    obtain ⟨v, b⟩ := p
    rw [e] at h
    dsimp only [bind, Option.bind] at h
    by_cases hv : v = 0
    · rw [ite_eq_left hv] at h
      cases h
      obtain ⟨u, hu, hk⟩ := faith_readInt _ bs v r e
      refine ⟨u, hu, fun t ht => ?_⟩
      have hl : (u ++ t).length % 8 = bs.length % 8 := by
        rw [hu]
        simp only [List.length_append]
        omega
      unfold readFill
      rw [hl, hk t]
      dsimp only [bind, Option.bind]
      rw [ite_eq_left hv]
    · rw [ite_eq_right hv] at h
      cases h

/-! ### Steps -/

section
variable {A P E : Type}

/-- The bits after a step's field, when it reads one. -/
def ORes.left : ORes P E → Option (List Bool)
  | .next _ r => some r
  | .exit _ r => some r
  | _ => none

/-- A step's result with other bits after its field. -/
def ORes.rebit : ORes P E → List Bool → ORes P E
  | .next p _, t => .next p t
  | .exit e _, t => .exit e t
  | o, _ => o

/-- A step that looks at no bit after its field, on bits whose length is the same modulo 8. -/
def KFaith (k : List Bool → ORes P E) : Prop :=
  ∀ bs r, (k bs).left = some r → ∃ u, bs = u ++ r ∧ ∀ t : List Bool, t.length % 8 = r.length % 8 → k (u ++ t) = (k bs).rebit t

/-- The same, for the steps that go on. -/
def NFaith (k : List Bool → ORes P E) : Prop :=
  ∀ bs q r, k bs = .next q r → ∃ u, bs = u ++ r ∧ ∀ t : List Bool, t.length % 8 = r.length % 8 → k (u ++ t) = .next q t

theorem KFaith.nfaith {k : List Bool → ORes P E} (h : KFaith k) : NFaith k := by
  intro bs q r hq
  obtain ⟨u, hu, hk⟩ := h bs r (by rw [hq]; rfl)
  exact ⟨u, hu, fun t ht => by rw [hk t ht, hq]; rfl⟩

theorem KFaith.exit {k : List Bool → ORes P E} (h : KFaith k) {bs : List Bool} {e : E} {r : List Bool} (he : k bs = .exit e r) :
    ∃ u, bs = u ++ r ∧ ∀ t : List Bool, t.length % 8 = r.length % 8 → k (u ++ t) = .exit e t := by
  obtain ⟨u, hu, hk⟩ := h bs r (by rw [he]; rfl)
  exact ⟨u, hu, fun t ht => by rw [hk t ht, he]; rfl⟩

theorem kfaith_next (f : P) : KFaith fun bs => (.next f bs : ORes P E) := by
  intro bs r h
  cases h
  exact ⟨[], rfl, fun _ _ => rfl⟩

theorem kfaith_exit (e : E) : KFaith fun bs => (.exit e bs : ORes P E) := by
  intro bs r h
  cases h
  exact ⟨[], rfl, fun _ _ => rfl⟩

theorem kfaith_bad : KFaith fun _ => (.bad : ORes P E) := by
  intro _ _ h
  cases h

theorem kfaith_ite {c : Prop} [Decidable c] {f g : List Bool → ORes P E} (hf : KFaith f) (hg : KFaith g) :
    KFaith fun bs => if c then f bs else g bs := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf
  · simpa only [h, ↓reduceIte] using hg

theorem kfaith_lookIn {o : Option A} {k : A → List Bool → ORes P E} (h : ∀ a, KFaith (k a)) :
    KFaith fun bs => lookIn o fun a => k a bs := by
  cases o with
  | none => exact kfaith_bad
  | some a => exact h a

theorem kfaith_readIn {room : Nat} {rd : List Bool → Option (A × List Bool)} {k : A → List Bool → ORes P E} (hr : Faith rd)
    (hk : ∀ a, KFaith (k a)) : KFaith fun bs => readIn room rd bs k := by
  intro bs r h
  have h' : (readIn room rd bs k).left = some r := h
  cases e : rd bs with
  | none =>
    unfold readIn at h'
    rw [e] at h'
    by_cases hl : bs.length < room
    · rw [ite_eq_left hl] at h'
      cases h'
    · rw [ite_eq_right hl] at h'
      cases h'
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [readIn_some e] at h'
    obtain ⟨u2, hb, hu2⟩ := hk a b r h'
    obtain ⟨u1, hbs, hu1⟩ := hr bs a b e
    refine ⟨u1 ++ u2, by rw [hbs, hb, List.append_assoc], fun t ht => ?_⟩
    show readIn room rd (u1 ++ u2 ++ t) k = (readIn room rd bs k).rebit t
    rw [List.append_assoc, readIn_some (hu1 _), readIn_some e]
    exact hu2 t ht

theorem kfaith_nextIn {c : BlockCategory} {st : BlockState} {k : BlockState → List Bool → ORes P E} (hk : ∀ a, KFaith (k a)) :
    KFaith fun bs => nextIn c st bs k := by
  show KFaith fun bs => if st.count = 0 ∧ c.n < 2 then .bad else readIn 54 (nextElement c st) bs k
  exact kfaith_ite kfaith_bad (kfaith_readIn (faith_nextElement c st) hk)

/-- The reading in order leaves a suffix of its bits. -/
theorem reach_suffix {step : P → List Bool → ORes P E} (hs : ∀ p, NFaith (step p)) {p q : P} {bs c : List Bool}
    (h : Reach step p bs q c) : ∃ v, bs = v ++ c := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | next hst _ ih =>
    obtain ⟨u, hu, _⟩ := hs _ _ _ _ hst
    obtain ⟨v, hv⟩ := ih
    exact ⟨u ++ v, by rw [hu, hv, List.append_assoc]⟩

/-- The reading in order reaches, from bits that end with whole bytes it doesn't read into, what it reaches without them. -/
theorem reach_restrict {step : P → List Bool → ORes P E} (hs : ∀ p, NFaith (step p)) {p q : P} {bs c : List Bool}
    (h : Reach step p bs q c) : ∀ A B F : List Bool, bs = A ++ F → c = B ++ F → F.length % 8 = 0 → Reach step p A q B := by
  induction h with
  | refl =>
    intro A B F h1 h2 _
    rw [h1] at h2
    rw [List.append_cancel_right h2]
    exact .refl _ _
  | @next p bs p' bs' q c hst hr ih =>
    intro A B F h1 h2 hF
    obtain ⟨u, hu, hk⟩ := hs p bs p' bs' hst
    obtain ⟨v, hv⟩ := reach_suffix hs hr
    have hv' : bs' = v ++ B ++ F := by rw [hv, h2, List.append_assoc]
    have hA : A = u ++ (v ++ B) := List.append_cancel_right (by rw [← h1, hu, hv, h2]; simp only [List.append_assoc])
    rw [hA]
    refine .next (hk (v ++ B) ?_) (ih (v ++ B) B F hv' h2 hF)
    rw [hv']
    simp only [List.length_append]
    omega

/-- A step that reads the fill bits and goes on. -/
theorem kfaith_of_fill {k : List Bool → ORes P E} (X : P)
    (hk : ∀ bs, k bs = match readFill bs with | some b => .next X b | none => .bad) : KFaith k := by
  intro bs r h
  rw [hk] at h
  cases e : readFill bs with
  | none => rw [e] at h; cases h
  | some b =>
    rw [e] at h
    cases h
    obtain ⟨u, hu, hf⟩ := faith_readFill e
    refine ⟨u, hu, fun t ht => ?_⟩
    rw [hk, hk, hf t ht, e]
    rfl

end

/-! ### The steps of the reading in order -/

theorem kfaith_cStep (w : Nat) (m : MetaBlockHeader) : ∀ p, KFaith (cStep w m p)
  | .command s => kfaith_ite (kfaith_exit s) (kfaith_nextIn fun _ => kfaith_next _)
  | .insertCopy _ _ => kfaith_lookIn fun _ => kfaith_readIn (faith_readInsertHalf _) fun _ => kfaith_next _
  | .copyLength _ _ _ _ _ _ => kfaith_ite kfaith_bad (kfaith_readIn (faith_readInt _) fun _ => kfaith_next _)
  | .literals _ _ _ _ _ 0 _ _ => kfaith_next _
  | .literals _ _ _ _ _ (_ + 1) _ _ => kfaith_ite (kfaith_nextIn fun _ => kfaith_next _) (kfaith_next _)
  | .literalSymbol _ _ _ _ _ _ _ _ =>
    kfaith_lookIn fun _ => kfaith_lookIn fun _ => kfaith_lookIn fun _ => kfaith_readIn (faith_decodeSymbol _) fun _ => kfaith_next _
  | .distance _ _ _ =>
    kfaith_ite (kfaith_next _)
      (kfaith_ite (kfaith_lookIn fun _ => kfaith_lookIn fun q => kfaith_next q) (kfaith_nextIn fun _ => kfaith_next _))
  | .distanceSymbol _ _ _ =>
    kfaith_lookIn fun _ => kfaith_lookIn fun _ => kfaith_readIn (faith_readDistanceParts _ _ _) fun _ =>
      kfaith_lookIn fun _ => kfaith_lookIn fun q => kfaith_next q
  | .copy _ _ 0 => kfaith_next _
  | .copy _ _ (_ + 1) => kfaith_next _
  | .word _ [] => kfaith_next _
  | .word _ (_ :: _) => kfaith_next _

theorem kfaith_hStep (g : Gh) : ∀ p, KFaith (hStep g p)
  | .cat _ => kfaith_readIn faith_readVarLen fun _ => kfaith_ite (kfaith_next _) (kfaith_next _)
  | .code _ _ =>
    kfaith_readIn (faith_readInt 2) fun _ => kfaith_ite (kfaith_readIn (faith_simpleChain _ _) fun _ => kfaith_next _) (kfaith_next _)
  | .clens _ _ [] _ _ => kfaith_ite (kfaith_next _) kfaith_bad
  | .clens _ _ (_ :: _) _ _ =>
    kfaith_readIn faith_readCodeLengthCodeLength fun _ =>
      kfaith_ite (kfaith_next _) (kfaith_ite (kfaith_next _) (kfaith_ite kfaith_bad (kfaith_next _)))
  | .syms _ _ _ _ =>
    kfaith_ite kfaith_bad (kfaith_ite (kfaith_next _) (kfaith_ite kfaith_bad
      (kfaith_readIn (faith_lenSym _) fun _ => kfaith_ite kfaith_bad (kfaith_ite kfaith_bad (kfaith_next _)))))
  | .first _ _ _ _ => kfaith_readIn (faith_readBlockCount _) fun _ => kfaith_next _
  | .np => kfaith_readIn faith_readNp fun _ => kfaith_next _
  | .modes _ 0 => kfaith_next _
  | .modes _ (_ + 1) => kfaith_readIn (faith_readInt 2) fun _ => kfaith_next _
  | .trees _ => kfaith_readIn faith_readVarLen fun _ => kfaith_ite (kfaith_next _) (kfaith_next _)
  | .rlemax _ _ => kfaith_readIn faith_readRLEMAX fun _ => kfaith_next _
  | .vals _ _ rlemax code _ _ => kfaith_ite (kfaith_next _) (by
      cases runOf rlemax code with
      | some _ => exact kfaith_next _
      | none => exact kfaith_readIn (faith_mapSym _ _) fun _ => kfaith_ite kfaith_bad (kfaith_next _))
  | .imtf _ _ _ => kfaith_readIn (faith_readInt 1) fun _ => kfaith_ite (kfaith_next _) kfaith_bad
  | .codes _ _ (_ + 1) => kfaith_next _
  | .codes .L _ 0 => kfaith_next _
  | .codes .I _ 0 => kfaith_next _
  | .codes .D _ 0 => kfaith_exit _

theorem kfaith_startPlace (w : Nat) (st : StreamState) : ∀ ms, KFaith (startPlace w st ms)
  | .lastEmpty => kfaith_next _
  | .metadata _ _ => kfaith_of_fill _ fun _ => rfl
  | .data _ _ _ => kfaith_ite (kfaith_of_fill _ fun _ => rfl) (kfaith_next _)

theorem nfaith_sStep : ∀ p, NFaith (sStep p)
  | .wbits => (kfaith_readIn faith_readWBITS fun _ => kfaith_next _).nfaith
  | .mblock w st => (kfaith_readIn faith_metaStart (kfaith_startPlace w st)).nfaith
  | .skip _ _ _ 0 => (kfaith_next _).nfaith
  | .skip _ _ _ (_ + 1) => (kfaith_readIn (faith_readInt 8) fun _ => kfaith_next _).nfaith
  | .raw _ _ _ 0 => (kfaith_next _).nfaith
  | .raw _ _ _ (_ + 1) => (kfaith_readIn (faith_readInt 8) fun _ => kfaith_next _).nfaith
  | .hdr w st last mlen g p => by
    intro bs q r h
    cases e : hStep g p bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      obtain ⟨u, hu, hk⟩ := (kfaith_hStep g p).nfaith bs q' _ e
      exact ⟨u, hu, fun t ht => by simp only [sStep, hk t ht]⟩
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      obtain ⟨u, hu, hk⟩ := (kfaith_hStep g p).exit e
      exact ⟨u, hu, fun t ht => by simp only [sStep, hk t ht]⟩
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .cmds w last m p => by
    intro bs q r h
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      obtain ⟨u, hu, hk⟩ := (kfaith_cStep w m p).nfaith bs p' _ e
      exact ⟨u, hu, fun t ht => by simp only [sStep, hk t ht]⟩
    | exit s b =>
      by_cases hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance) = true
      · have h' : sStep (.cmds w last m p) bs = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b := by
          simp only [sStep, e, hc, ↓reduceIte]
        rw [h'] at h
        cases h
        obtain ⟨u, hu, hk⟩ := (kfaith_cStep w m p).exit e
        exact ⟨u, hu, fun t ht => by simp only [sStep, hk t ht, hc, ↓reduceIte]⟩
      · have h' : sStep (.cmds w last m p) bs = .bad := by
          simp only [sStep, e]
          exact ite_eq_right hc
        rw [h'] at h
        cases h
    | bad =>
      have h' : sStep (.cmds w last m p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.cmds w last m p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .ended st => by
    intro bs q r h
    by_cases hm : bs.length % 8 = 0
    · have h' : sStep (.ended st) bs = if bs.isEmpty then .exit (st.output.reverse.map Nat.toUInt8) bs else .bad := by
        simp only [sStep, hm, ↓reduceIte]
      rw [h'] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none =>
        have h' : sStep (.ended st) bs = .bad := by simp only [sStep, hm, ↓reduceIte, e]
        rw [h'] at h
        cases h
      | some b =>
        have h' : sStep (.ended st) bs = .next (.ended st) b := by simp only [sStep, hm, ↓reduceIte, e]
        rw [h'] at h
        cases h
        obtain ⟨u, hu, hk⟩ := faith_readFill e
        refine ⟨u, hu, fun t ht => ?_⟩
        have hm' : ¬ (u ++ t).length % 8 = 0 := by
          rw [hu] at hm
          simp only [List.length_append] at hm ⊢
          omega
        simp only [sStep, hm', ↓reduceIte, hk t ht]

end Brotli.Decoder
