module

public import Brotli.Decoder.HeaderRest
public import Brotli.Decoder.Rest
public import Brotli.Decoder.StepRead
public import Brotli.Decoder.StreamOrder
public import Brotli.Decoder.Restrict

@[expose] public section

/-!
# How far the reading in order goes without reading or producing

A step of the reading in order reads bits, produces bytes, or goes to a place lower in a bounded ranking of the places.
So the steps the reading in order takes are at most a constant times the bits it reads and the bytes it produces, plus a
constant.

A meta-block's commands need the format's distances for this: a command whose distance takes no extra bits refers to the
dictionary only with a word of at least one byte, so no command reads nothing and produces nothing.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The distances a stream has used -/

/-- Each of the last four distances is at most 16 or at most the largest backward distance. -/
def DistOk (w : Nat) (r : Distances) (produced : Nat) : Prop :=
  r.last ≤ max 16 (maxBackwardDistance w produced) ∧ r.secondToLast ≤ max 16 (maxBackwardDistance w produced) ∧
    r.thirdToLast ≤ max 16 (maxBackwardDistance w produced) ∧ r.fourthToLast ≤ max 16 (maxBackwardDistance w produced)

theorem DistOk.mono {w : Nat} {r : Distances} {p p' : Nat} (h : DistOk w r p) (hp : p ≤ p') : DistOk w r p' := by
  have : maxBackwardDistance w p ≤ maxBackwardDistance w p' := by
    unfold maxBackwardDistance
    omega
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem ringOk_initial (w : Nat) : DistOk w initialDistances 0 := by
  unfold DistOk initialDistances
  dsimp only
  omega

/-- A distance pushed is at most the largest backward distance. -/
theorem ringOk_push {w : Nat} {r : Distances} {produced dcode d : Nat} (h : DistOk w r produced) :
    DistOk w (pushDistance r dcode d (isDictionaryReference d (maxBackwardDistance w produced))) produced := by
  unfold pushDistance
  split
  · exact h
  · rename_i hc
    have hd : d ≤ maxBackwardDistance w produced := by
      unfold isDictionaryReference at hc
      simp only [decide_eq_true_eq, not_or, Nat.not_lt] at hc
      exact hc.2
    obtain ⟨h1, h2, h3, _⟩ := h
    show d ≤ _ ∧ r.last ≤ _ ∧ r.secondToLast ≤ _ ∧ r.thirdToLast ≤ _
    exact ⟨by omega, h1, h2, h3⟩

/-- A special distance is at most the largest of the last four, plus 3. -/
theorem special_le (r : Distances) : ∀ i : Fin 16,
    specialDistance r i ≤ ((max (max r.last r.secondToLast) (max r.thirdToLast r.fourthToLast) : Nat) : Int) + 3
  | 0 => by simp only [specialDistance]; omega
  | 1 => by simp only [specialDistance]; omega
  | 2 => by simp only [specialDistance]; omega
  | 3 => by simp only [specialDistance]; omega
  | 4 => by simp only [specialDistance]; omega
  | 5 => by simp only [specialDistance]; omega
  | 6 => by simp only [specialDistance]; omega
  | 7 => by simp only [specialDistance]; omega
  | 8 => by simp only [specialDistance]; omega
  | 9 => by simp only [specialDistance]; omega
  | 10 => by simp only [specialDistance]; omega
  | 11 => by simp only [specialDistance]; omega
  | 12 => by simp only [specialDistance]; omega
  | 13 => by simp only [specialDistance]; omega
  | 14 => by simp only [specialDistance]; omega
  | 15 => by simp only [specialDistance]; omega
  | ⟨_ + 16, h⟩ => absurd h (by omega)

/-- A distance symbol with no extra bits is one of the last distances or a direct distance. -/
theorem extraBits_zero {np nd dc : Nat} (h : distanceExtraBits np nd dc = 0) : dc < 16 + nd := by
  unfold distanceExtraBits at h
  by_cases hd : dc < 16 + nd
  · exact hd
  · rw [ite_eq_right hd] at h
    generalize (dc - nd - 16) >>> (np + 1) = z at h
    omega

/-- A distance with no extra bits is small: from the last four, or one of the direct distances. -/
theorem distance_small {np nd w produced dc e d : Nat} {r : Distances} (hr : DistOk w r produced) (hnd : nd ≤ 120)
    (h0 : distanceExtraBits np nd dc = 0) (hd : distanceOf np nd r dc e = some d) :
    d ≤ max (max 16 (maxBackwardDistance w produced) + 3) 120 := by
  unfold distanceOf at hd
  split at hd
  · rename_i hlt
    dsimp only at hd
    split at hd
    · cases hd
    · rename_i hv
      cases hd
      have hs := special_le r ⟨dc, hlt⟩
      have ht : ((specialDistance r ⟨dc, hlt⟩).toNat : Int) = specialDistance r ⟨dc, hlt⟩ := Int.toNat_of_nonneg (by omega)
      obtain ⟨h1, h2, h3, h4⟩ := hr
      omega
  · split at hd
    · cases hd
      omega
    · exfalso
      rename_i h2
      exact h2 (extraBits_zero h0)

private theorem transforms_0 : transforms[0]? = some ⟨"", .identity, ""⟩ := rfl
private theorem transforms_1 : transforms[1]? = some ⟨"", .identity, " "⟩ := rfl
private theorem transforms_2 : transforms[2]? = some ⟨" ", .identity, " "⟩ := rfl
private theorem transforms_3 : transforms[3]? = some ⟨"", .omitFirst 1, ""⟩ := rfl

/-- A dictionary word whose word number is at most 119 has at least one byte: its transform is one of the first four. -/
theorem dictionaryWord_ne_nil {clen d maxD : Nat} {word : List Nat} (h : dictionaryWord clen d maxD = some word)
    (hw : d - (maxD + 1) ≤ 119) : word ≠ [] := by
  unfold dictionaryWord at h
  split at h
  · cases h
  · rename_i hl
    dsimp only at h
    generalize d - (maxD + 1) = wid at h hw
    have hn : 5 ≤ NDBITS.getD clen 0 := (show ∀ l < 25, 4 ≤ l → 5 ≤ NDBITS.getD l 0 by decide) clen (by omega) (by omega)
    have ht : wid >>> NDBITS.getD clen 0 ≤ 3 := by
      rw [Nat.shiftRight_eq_div_pow]
      have h1 : wid / 2 ^ NDBITS.getD clen 0 ≤ wid / 2 ^ 5 := Nat.div_le_div_left (Nat.pow_le_pow_right (by decide) hn) (by decide)
      have h32 : (2 : Nat) ^ 5 = 32 := rfl
      rw [h32] at h1
      omega
    generalize wid >>> NDBITS.getD clen 0 = tid at h ht
    have hlen : ((List.range clen).map fun k => DICT (wordOffset clen (wid % NWORDS clen) + k)).length = clen := by simp
    generalize ((List.range clen).map fun k => DICT (wordOffset clen (wid % NWORDS clen) + k)) = base at h hlen
    have key : ∀ t, transforms[tid]? = some t → (applyTransform t base).length + 1 ≥ clen := by
      intro t et
      rcases (show tid = 0 ∨ tid = 1 ∨ tid = 2 ∨ tid = 3 by omega) with rfl | rfl | rfl | rfl
      · rw [transforms_0] at et
        cases et
        simp [applyTransform, applyElementary, bytes, hlen]
      · rw [transforms_1] at et
        cases et
        simp [applyTransform, applyElementary, bytes, hlen]
        omega
      · rw [transforms_2] at et
        cases et
        simp [applyTransform, applyElementary, bytes, hlen]
        omega
      · rw [transforms_3] at et
        cases et
        simp [applyTransform, applyElementary, bytes, hlen]
        omega
    cases et : transforms[tid]? with
    | none => rw [et] at h; cases h
    | some t =>
      rw [et] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      intro e
      have := key t et
      rw [e] at this
      simp at this
      omega

/-- A distance's parts that read no bits have no extra bits. -/
theorem readDistanceParts_zero {np nd : Nat} {code : PrefixCode} {bs b : List Bool} {dc e : Nat}
    (h : readDistanceParts np nd code bs = some ((dc, e), b)) (hl : bs.length ≤ b.length) : distanceExtraBits np nd dc = 0 := by
  unfold readDistanceParts at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; simp at h
  | some p =>
    obtain ⟨dc', b1⟩ := p
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    obtain ⟨u, hu, _⟩ := faith_decodeSymbol code bs dc' b1 hd
    cases hi : readInt (distanceExtraBits np nd dc') b1 with
    | none => rw [hi] at h; cases h
    | some q =>
      obtain ⟨e', b2⟩ := q
      rw [hi] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have := readInt_length _ _ _ _ hi
      rw [hu, List.length_append] at hl
      omega

/-! ### Reads -/

section
variable {A P E : Type}

theorem readIn_next' {room : Nat} {rd : List Bool → Option (A × List Bool)} {bs : List Bool} {k : A → List Bool → ORes P E}
    {q : P} {c : List Bool} (h : readIn room rd bs k = .next q c) : ∃ v b, rd bs = some (v, b) ∧ k v b = .next q c := by
  unfold readIn at h
  cases e : rd bs with
  | none =>
    rw [e] at h
    dsimp only at h
    by_cases hl : bs.length < room
    · rw [ite_eq_left hl] at h
      cases h
    · rw [ite_eq_right hl] at h
      cases h
  | some p =>
    obtain ⟨v, b⟩ := p
    rw [e] at h
    exact ⟨v, b, rfl, h⟩

theorem lookIn_next' {o : Option A} {k : A → ORes P E} {q : P} {c : List Bool} (h : lookIn o k = .next q c) :
    ∃ v, o = some v ∧ k v = .next q c := by
  cases o with
  | none => cases h
  | some v => exact ⟨v, rfl, h⟩

theorem nextIn_next' {cat : BlockCategory} {st : BlockState} {bs : List Bool} {k : BlockState → List Bool → ORes P E}
    {q : P} {c : List Bool} (h : nextIn cat st bs k = .next q c) : ∃ v b, nextElement cat st bs = some (v, b) ∧ k v b = .next q c := by
  unfold nextIn at h
  split at h
  · cases h
  · exact readIn_next' h

end

theorem decodeSymbol_le {code : PrefixCode} {bs b : List Bool} {v : Nat} (h : decodeSymbol code bs = some (v, b)) :
    b.length ≤ bs.length := by
  obtain ⟨u, hu, _⟩ := faith_decodeSymbol code bs v b h
  rw [hu, List.length_append]
  omega

theorem readBlockType_le {n : Nat} {code : PrefixCode} {bt v : BlockTypes} {bs b : List Bool}
    (h : readBlockType n code bt bs = some (v, b)) : b.length ≤ bs.length := by
  obtain ⟨u, hu, _⟩ := faith_readBlockType n code bt bs v b h
  rw [hu, List.length_append]
  omega

/-- A block count takes at least two bits. -/
theorem readBlockCount_lt {code : PrefixCode} {bs b : List Bool} {v : Nat} (h : readBlockCount code bs = some (v, b)) :
    b.length + 2 ≤ bs.length := by
  unfold readBlockCount at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; simp at h
  | some p =>
    obtain ⟨c, b1⟩ := p
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    have h1 := decodeSymbol_le hd
    cases hc : blockCountCodes[c]? with
    | none => rw [hc] at h; cases h
    | some row =>
      obtain ⟨bits, lowest, z⟩ := row
      rw [hc] at h
      dsimp only at h
      have hb : 2 ≤ bits := (show ∀ e ∈ blockCountCodes, 2 ≤ e.1 by decide) _ (List.mem_of_getElem? hc)
      cases hi : readInt bits b1 with
      | none => rw [hi] at h; cases h
      | some q =>
        obtain ⟨e, b2⟩ := q
        rw [hi] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := readInt_length _ _ _ _ hi
        omega

/-- An element's block switch takes nothing, while the block lasts, or at least two bits. -/
theorem nextElement_progress {cat : BlockCategory} {st v : BlockState} {bs b : List Bool} (h : nextElement cat st bs = some (v, b)) :
    (st.count ≠ 0 ∧ v = { st with count := st.count - 1 } ∧ b = bs) ∨ b.length + 2 ≤ bs.length := by
  by_cases h0 : st.count = 0
  · right
    unfold nextElement at h
    rw [ite_eq_left h0] at h
    split at h
    · cases h
    · cases ht : readBlockType cat.n cat.typeCode st.types bs with
      | none => rw [ht] at h; simp at h
      | some p =>
        obtain ⟨types, b1⟩ := p
        rw [ht] at h
        dsimp only [bind, Option.bind] at h
        have h1 := readBlockType_le ht
        cases hc : readBlockCount cat.countCode b1 with
        | none => rw [hc] at h; cases h
        | some q =>
          obtain ⟨count, b2⟩ := q
          rw [hc] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl⟩ := h
          have := readBlockCount_lt hc
          omega
  · left
    rw [nextElement_count bs h0] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h0, h.1.symm, h.2.symm⟩

/-- A copy length is at least 2. -/
theorem readInsertHalf_base {code : PrefixCode} {bs b : List Bool} {v : Nat × Nat × Nat × Nat} (h : readInsertHalf code bs = some (v, b)) :
    2 ≤ v.2.2.2 := by
  unfold readInsertHalf at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; simp at h
  | some p =>
    obtain ⟨c, b1⟩ := p
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    cases hi : insertCopyCodes c with
    | none => rw [hi] at h; cases h
    | some r =>
      obtain ⟨ic, cc⟩ := r
      rw [hi] at h
      dsimp only at h
      cases hl : insertLengthCodes[ic]? with
      | none => rw [hl] at h; cases h
      | some r2 =>
        obtain ⟨ib, ibase, _⟩ := r2
        rw [hl] at h
        dsimp only at h
        cases hcl : copyLengthCodes[cc]? with
        | none => rw [hcl] at h; cases h
        | some r3 =>
          obtain ⟨cb, cbase, z⟩ := r3
          rw [hcl] at h
          dsimp only at h
          have hb : 2 ≤ cbase := (show ∀ e ∈ copyLengthCodes, 2 ≤ e.2.1 by decide) _ (List.mem_of_getElem? hcl)
          cases hx : readInt ib b1 with
          | none => rw [hx] at h; cases h
          | some q =>
            rw [hx] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            exact hb

/-! ### A meta-block's commands -/

/-- What every place of the commands the reading in order reaches has: the distances used so far, and a copy length of at
least 2 once it is known. -/
def CInv (w : Nat) : Phase → Prop
  | .command s => DistOk w s.distances s.produced
  | .insertCopy s _ => DistOk w s.distances s.produced
  | .copyLength s _ _ _ _ copyBase => DistOk w s.distances s.produced ∧ 2 ≤ copyBase
  | .literals s _ _ _ clen _ _ _ => DistOk w s.distances s.produced ∧ 2 ≤ clen
  | .literalSymbol s _ _ _ clen _ _ _ => DistOk w s.distances s.produced ∧ 2 ≤ clen
  | .distance s _ clen => DistOk w s.distances s.produced ∧ 2 ≤ clen
  | .distanceSymbol s clen _ => DistOk w s.distances s.produced ∧ 2 ≤ clen
  | .copy s _ _ => DistOk w s.distances s.produced
  | .word s _ => DistOk w s.distances s.produced

/-- A ranking of the commands' places: a step that reads and produces nothing goes lower. -/
def cstage : Phase → Nat
  | .command s => if s.remaining = 0 then 2 else 20
  | .insertCopy .. => 19
  | .copyLength .. => 18
  | .literals .. => 17
  | .literalSymbol .. => 16
  | .distance .. => 15
  | .distanceSymbol .. => 14
  | .copy _ _ 0 => 21
  | .copy _ _ (_ + 1) => 13
  | .word _ [] => 21
  | .word _ (_ :: _) => 13

theorem cstage_le (p : Phase) : cstage p ≤ 21 := by
  unfold cstage
  split
  · split <;> omega
  all_goals omega

/-- A step reads bits or produces bytes. -/
def Moved (bs c : List Bool) (o o' : List Nat) : Prop := c.length < bs.length ∨ o.length < o'.length

/-- What a copy goes on to. -/
theorem copyPhase_facts {w : Nat} {s : CommandState} {clen dcode d : Nat} {q : Phase} (hr : DistOk w s.distances s.produced)
    (hc : 2 ≤ clen) (h : copyPhase w s clen dcode d = some q) :
    CInv w q ∧ q.out = s.output ∧ (d ≤ max (max 16 (maxBackwardDistance w s.produced) + 3) 120 → cstage q = 13) := by
  unfold copyPhase at h
  dsimp only at h
  by_cases hd : isDictionaryReference d (maxBackwardDistance w s.produced) = true
  · rw [ite_eq_left hd] at h
    cases hw : dictionaryWord clen d (maxBackwardDistance w s.produced) with
    | none => rw [hw] at h; cases h
    | some word =>
      rw [hw] at h
      dsimp only [Option.bind] at h
      split at h
      · cases h
      · cases h
        refine ⟨(ringOk_push hr).mono (Nat.le_add_right _ _), rfl, fun hsm => ?_⟩
        have hlt : maxBackwardDistance w s.produced < d := by
          unfold isDictionaryReference at hd
          simpa using hd
        have hne := dictionaryWord_ne_nil hw (by omega)
        cases word with
        | nil => exact absurd rfl hne
        | cons _ _ => rfl
  · rw [ite_eq_right hd] at h
    split at h
    · cases h
    · cases h
      refine ⟨(ringOk_push hr).mono (Nat.le_add_right _ _), rfl, fun _ => ?_⟩
      obtain ⟨n, rfl⟩ : ∃ n, clen = n + 1 := ⟨clen - 1, by omega⟩
      rfl

private theorem extraBits_zero_zero (np nd : Nat) : distanceExtraBits np nd 0 = 0 := by
  unfold distanceExtraBits
  rw [ite_eq_left (by omega)]

/-- Each step of the commands read in order keeps what its places have, grows the output, and reads bits, produces bytes
or goes lower in the ranking. -/
theorem cStep_moves {w : Nat} {m : MetaBlockHeader} (hm : m.ndirect ≤ 120) : ∀ (p : Phase) (bs : List Bool) (q : Phase) (c : List Bool),
    CInv w p → cStep w m p bs = .next q c → CInv w q ∧ (∃ l, q.out = l ++ p.out) ∧ (Moved bs c p.out q.out ∨ cstage q < cstage p)
  | .command s, bs, q, c, hi, h => by
    have h' : (if s.remaining = 0 then ORes.exit s bs else nextIn m.insertCopy s.insertCopy bs fun ic b => .next (.insertCopy s ic) b) =
        .next q c := h
    split at h'
    · cases h'
    · rename_i h0
      obtain ⟨ic, b, e1, e2⟩ := nextIn_next' h'
      cases e2
      refine ⟨hi, ⟨[], rfl⟩, ?_⟩
      rcases nextElement_progress e1 with ⟨_, _, rfl⟩ | hl
      · right
        show 19 < (if s.remaining = 0 then 2 else 20)
        rw [ite_eq_right h0]
        omega
      · exact Or.inl (Or.inl (by omega))
  | .insertCopy s ic, bs, q, c, hi, h => by
    obtain ⟨code, _, h2⟩ := lookIn_next' h
    obtain ⟨v, b, e1, e2⟩ := readIn_next' h2
    cases e2
    exact ⟨⟨hi, readInsertHalf_base e1⟩, ⟨[], rfl⟩, Or.inr (by simp only [cstage]; omega)⟩
  | .copyLength s ic c0 ilen copyBits copyBase, bs, q, c, hi, h => by
    have h' : (if s.remaining < ilen then ORes.bad else readIn 24 (readInt copyBits) bs fun e b =>
        .next (.literals s ic c0 ilen (copyBase + e) ilen s.literal s.output) b) = .next q c := h
    split at h'
    · cases h'
    · obtain ⟨e, b, _, e2⟩ := readIn_next' h'
      cases e2
      exact ⟨⟨hi.1, by have := hi.2; omega⟩, ⟨[], rfl⟩, Or.inr (by simp only [cstage]; omega)⟩
  | .literals s ic c0 ilen clen 0 lit out, bs, q, c, hi, h => by
    cases h
    exact ⟨⟨hi.1.mono (Nat.le_add_right _ _), hi.2⟩, ⟨[], rfl⟩, Or.inr (by simp only [cstage]; omega)⟩
  | .literals s ic c0 ilen clen (n + 1) lit out, bs, q, c, hi, h => by
    have h' : (if lit.count = 0 then nextIn m.literal lit bs fun lit b =>
          .next (.literals s ic c0 ilen clen (n + 1) { lit with count := lit.count + 1 } out) b
        else .next (.literalSymbol s ic c0 ilen clen n { lit with count := lit.count - 1 } out) bs) = .next q c := h
    split at h'
    · rename_i h0
      obtain ⟨lit', b, e1, e2⟩ := nextIn_next' h'
      cases e2
      refine ⟨hi, ⟨[], rfl⟩, Or.inl (Or.inl ?_)⟩
      rcases nextElement_progress e1 with ⟨h1, _⟩ | hl
      · exact absurd h0 h1
      · omega
    · cases h'
      exact ⟨hi, ⟨[], rfl⟩, Or.inr (by simp only [cstage]; omega)⟩
  | .literalSymbol s ic c0 ilen clen n lit out, bs, q, c, hi, h => by
    obtain ⟨_, _, h2⟩ := lookIn_next' h
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨_, _, h4⟩ := lookIn_next' h3
    obtain ⟨byte, b, _, e2⟩ := readIn_next' h4
    cases e2
    exact ⟨hi, ⟨[byte], rfl⟩, Or.inl (Or.inr (by simp [Phase.out]))⟩
  | .distance s c0 clen, bs, q, c, hi, h => by
    have h' : (if s.remaining = 0 then ORes.next (Phase.command s) bs
        else if implicitZeroDistance c0 then
          lookIn (distanceOf m.npostfix m.ndirect s.distances 0 0) fun d => lookIn (copyPhase w s clen 0 d) fun q => .next q bs
        else nextIn m.distance s.distance bs fun dist b => .next (.distanceSymbol s clen dist) b) = .next q c := h
    split at h'
    · rename_i h0
      cases h'
      refine ⟨hi.1, ⟨[], rfl⟩, Or.inr ?_⟩
      show (if s.remaining = 0 then 2 else 20) < 15
      rw [ite_eq_left h0]
      omega
    · split at h'
      · obtain ⟨d, hd, h2⟩ := lookIn_next' h'
        obtain ⟨q', hq, e2⟩ := lookIn_next' h2
        cases e2
        obtain ⟨f1, f2, f3⟩ := copyPhase_facts hi.1 hi.2 hq
        refine ⟨f1, ⟨[], by rw [f2]; rfl⟩, Or.inr ?_⟩
        rw [f3 (distance_small hi.1 hm (extraBits_zero_zero _ _) hd)]
        exact (show 13 < 15 by decide)
      · obtain ⟨dist, b, _, e2⟩ := nextIn_next' h'
        cases e2
        exact ⟨hi, ⟨[], rfl⟩, Or.inr (by simp only [cstage]; omega)⟩
  | .distanceSymbol s clen dist, bs, q, c, hi, h => by
    obtain ⟨_, _, h2⟩ := lookIn_next' h
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨⟨dc, e⟩, b, e1, h4⟩ := readIn_next' h3
    obtain ⟨d, hd, h5⟩ := lookIn_next' h4
    obtain ⟨q', hq, e2⟩ := lookIn_next' h5
    cases e2
    obtain ⟨f1, f2, f3⟩ := copyPhase_facts (s := { s with distance := dist }) hi.1 hi.2 hq
    refine ⟨f1, ⟨[], by rw [f2]; rfl⟩, ?_⟩
    by_cases hl : c.length < bs.length
    · exact Or.inl (Or.inl hl)
    · right
      have h0 := readDistanceParts_zero e1 (by omega)
      rw [f3 (distance_small hi.1 hm h0 hd)]
      exact (show 13 < 14 by decide)
  | .copy s d 0, bs, q, c, hi, h => by
    cases h
    refine ⟨hi, ⟨[], rfl⟩, Or.inr ?_⟩
    show (if s.remaining = 0 then 2 else 20) < 21
    split <;> omega
  | .copy s d (n + 1), bs, q, c, hi, h => by
    cases h
    exact ⟨hi, ⟨[s.output.getD (d - 1) 0], rfl⟩, Or.inl (Or.inr (by simp [Phase.out]))⟩
  | .word s [], bs, q, c, hi, h => by
    cases h
    refine ⟨hi, ⟨[], rfl⟩, Or.inr ?_⟩
    show (if s.remaining = 0 then 2 else 20) < 21
    split <;> omega
  | .word s (b :: pending), bs, q, c, hi, h => by
    cases h
    exact ⟨hi, ⟨[b], rfl⟩, Or.inl (Or.inr (by simp [Phase.out]))⟩

/-! ### Bytes a meta-block's commands produce -/

/-- What a place in the commands has: bytes produced or still to come, and, in the literals, an insert length within what
is left. Bytes produced and to come stay the same over a meta-block's commands, so a meta-block of at least one byte ends
with bytes produced. -/
def CLive : Phase → Prop
  | .command s | .insertCopy s _ | .copyLength s .. | .distance s .. | .distanceSymbol s .. | .copy s .. | .word s _ =>
    1 ≤ s.produced + s.remaining
  | .literals s _ _ ilen _ _ _ _ | .literalSymbol s _ _ ilen _ _ _ _ => 1 ≤ s.produced + s.remaining ∧ ilen ≤ s.remaining

/-- A copy keeps the bytes produced and to come. -/
theorem copyPhase_live {w : Nat} {s : CommandState} {clen dcode d : Nat} {q : Phase} (hs : 1 ≤ s.produced + s.remaining)
    (h : copyPhase w s clen dcode d = some q) : CLive q := by
  unfold copyPhase at h
  dsimp only at h
  split at h
  · cases hw : dictionaryWord clen d (maxBackwardDistance w s.produced) with
    | none => rw [hw] at h; cases h
    | some word =>
      rw [hw] at h
      dsimp only [Option.bind] at h
      split at h
      · cases h
      · cases h
        show 1 ≤ s.produced + word.length + (s.remaining - word.length)
        omega
  · split at h
    · cases h
    · cases h
      show 1 ≤ s.produced + clen + (s.remaining - clen)
      omega

/-- Each step of the commands read in order keeps what its places have. -/
theorem cStep_live {w : Nat} {m : MetaBlockHeader} : ∀ (p : Phase) (bs : List Bool) (q : Phase) (c : List Bool),
    CLive p → cStep w m p bs = .next q c → CLive q
  | .command s, bs, q, c, hi, h => by
    have h' : (if s.remaining = 0 then ORes.exit s bs else nextIn m.insertCopy s.insertCopy bs fun ic b => .next (.insertCopy s ic) b) =
        .next q c := h
    split at h'
    · cases h'
    · obtain ⟨ic, b, _, e2⟩ := nextIn_next' h'
      cases e2
      exact hi
  | .insertCopy s ic, bs, q, c, hi, h => by
    obtain ⟨code, _, h2⟩ := lookIn_next' h
    obtain ⟨v, b, _, e2⟩ := readIn_next' h2
    cases e2
    exact hi
  | .copyLength s ic c0 ilen copyBits copyBase, bs, q, c, hi, h => by
    have h' : (if s.remaining < ilen then ORes.bad else readIn 24 (readInt copyBits) bs fun e b =>
        .next (.literals s ic c0 ilen (copyBase + e) ilen s.literal s.output) b) = .next q c := h
    split at h'
    · cases h'
    · rename_i hl
      obtain ⟨e, b, _, e2⟩ := readIn_next' h'
      cases e2
      exact ⟨hi, by omega⟩
  | .literals s ic c0 ilen clen 0 lit out, bs, q, c, hi, h => by
    cases h
    have hi' : 1 ≤ s.produced + s.remaining ∧ ilen ≤ s.remaining := hi
    show 1 ≤ s.produced + ilen + (s.remaining - ilen)
    omega
  | .literals s ic c0 ilen clen (n + 1) lit out, bs, q, c, hi, h => by
    have h' : (if lit.count = 0 then nextIn m.literal lit bs fun lit b =>
          .next (.literals s ic c0 ilen clen (n + 1) { lit with count := lit.count + 1 } out) b
        else .next (.literalSymbol s ic c0 ilen clen n { lit with count := lit.count - 1 } out) bs) = .next q c := h
    split at h'
    · obtain ⟨lit', b, _, e2⟩ := nextIn_next' h'
      cases e2
      exact hi
    · cases h'
      exact hi
  | .literalSymbol s ic c0 ilen clen n lit out, bs, q, c, hi, h => by
    obtain ⟨_, _, h2⟩ := lookIn_next' h
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨_, _, h4⟩ := lookIn_next' h3
    obtain ⟨byte, b, _, e2⟩ := readIn_next' h4
    cases e2
    exact hi
  | .distance s c0 clen, bs, q, c, hi, h => by
    have h' : (if s.remaining = 0 then ORes.next (Phase.command s) bs
        else if implicitZeroDistance c0 then
          lookIn (distanceOf m.npostfix m.ndirect s.distances 0 0) fun d => lookIn (copyPhase w s clen 0 d) fun q => .next q bs
        else nextIn m.distance s.distance bs fun dist b => .next (.distanceSymbol s clen dist) b) = .next q c := h
    split at h'
    · cases h'
      exact hi
    · split at h'
      · obtain ⟨d, _, h2⟩ := lookIn_next' h'
        obtain ⟨q', hq, e2⟩ := lookIn_next' h2
        cases e2
        exact copyPhase_live hi hq
      · obtain ⟨dist, b, _, e2⟩ := nextIn_next' h'
        cases e2
        exact hi
  | .distanceSymbol s clen dist, bs, q, c, hi, h => by
    obtain ⟨_, _, h2⟩ := lookIn_next' h
    obtain ⟨_, _, h3⟩ := lookIn_next' h2
    obtain ⟨⟨dc, e⟩, b, _, h4⟩ := readIn_next' h3
    obtain ⟨d, _, h5⟩ := lookIn_next' h4
    obtain ⟨q', hq, e2⟩ := lookIn_next' h5
    cases e2
    exact copyPhase_live (s := { s with distance := dist }) hi hq
  | .copy s d 0, bs, q, c, hi, h => by
    cases h
    exact hi
  | .copy s d (n + 1), bs, q, c, hi, h => by
    cases h
    exact hi
  | .word s [], bs, q, c, hi, h => by
    cases h
    exact hi
  | .word s (b :: pending), bs, q, c, hi, h => by
    cases h
    exact hi

/-- The commands read in order keep what their places have. -/
theorem reach_live {w : Nat} {m : MetaBlockHeader} {p q : Phase} {bs c : List Bool} (h : Reach (cStep w m) p bs q c)
    (hi : CLive p) : CLive q := by
  induction h with
  | refl => exact hi
  | next hs _ ih => exact ih (cStep_live _ _ _ _ hi hs)

/-! ### A header -/

/-- A read that looks at no bit after the ones it takes, and fails on no bits, takes at least one. -/
theorem takes_one {A : Type} {rd : List Bool → Option (A × List Bool)} (hf : Faith rd) (h0 : rd [] = none) {bs b : List Bool} {v : A}
    (h : rd bs = some (v, b)) : b.length < bs.length := by
  obtain ⟨u, hu, hk⟩ := hf bs v b h
  cases u with
  | nil =>
    have := hk []
    simp only [List.append_nil] at this
    rw [h0] at this
    cases this
  | cons x u =>
    rw [hu]
    simp only [List.cons_append, List.length_cons, List.length_append]
    omega

theorem faith_le {A : Type} {rd : List Bool → Option (A × List Bool)} (hf : Faith rd) {bs b : List Bool} {v : A}
    (h : rd bs = some (v, b)) : b.length ≤ bs.length := by
  obtain ⟨u, hu, _⟩ := hf bs v b h
  rw [hu, List.length_append]
  omega

/-- A context map's run is at least one value. -/
theorem mapSym_run {rlemax : Nat} {code : PrefixCode} {bs b : List Bool} {v : Nat × Nat} (h : mapSym rlemax code bs = some (v, b)) :
    1 ≤ v.2 := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    cases hc : contextMapValue rlemax p.1 with
    | some x =>
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact Nat.le_refl _
    | none =>
      rw [hc] at h
      dsimp only at h
      cases hi : readInt p.1 p.2 with
      | none => rw [hi] at h; cases h
      | some q =>
        rw [hi] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        show 1 ≤ (1 <<< p.1) + q.1
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        have := Nat.two_pow_pos p.1
        omega

/-- How a group of codes is ranked: by whether codes are left, and what follows. -/
def ckStage (k : CK) (g : Gh) : Nat → Nat
  | _ + 1 => 2
  | 0 => match k with
    | .D => 22
    | .I => (if g.treesD = 0 then 22 else 2) + 1
    | .L => (if g.m.insertCopy.n = 0 then (if g.treesD = 0 then 22 else 2) + 1 else 2) + 1

/-- How a code is ranked by what it is for: above where its owner goes on to. -/
def oStage (g : Gh) : Owner → Nat
  | .type .. => 2
  | .count .. => 2
  | .map isL _ _ => mapSize g isL + 3
  | .codes k _ left => ckStage k g left + 1

/-- A ranking of a header's places: a step that reads nothing goes lower. -/
def hstage (g : Gh) : HPhase → Nat
  | .cat _ => 1
  | .code _ _ => 1
  | .clens o size [] _ _ => oStage g o + size + 2
  | .clens _ _ (_ :: _) _ _ => 1
  | .syms o size _ st => oStage g o + (size - st.lens.length) + 1
  | .first .. => 1
  | .np => 1
  | .modes _ 0 => 2
  | .modes _ (_ + 1) => 1
  | .trees _ => 1
  | .rlemax _ _ => 1
  | .vals _ _ _ _ _ left => left + 2
  | .imtf .. => 1
  | .codes k _ n => ckStage k g n

theorem ownerPlace_stage (g : Gh) (o : Owner) (c : PrefixCode) : hstage g (ownerPlace g o c) < oStage g o := by
  cases o with
  | type => simp only [ownerPlace, hstage, oStage]; omega
  | count => simp only [ownerPlace, hstage, oStage]; omega
  | map => simp only [ownerPlace, hstage, oStage]; omega
  | codes => simp only [ownerPlace, hstage, oStage]; omega

/-- Each step of a header read in order reads bits or goes lower in the ranking. -/
theorem hStep_moves (g : Gh) : ∀ (p : HPhase) (bs : List Bool) (q : Gh × HPhase) (c : List Bool),
    hStepP (g, p) bs = .next q c → c.length < bs.length ∨ hstage q.1 q.2 < hstage g p
  | .cat i, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.cat i) bs = _ from h)
    have hl := takes_one faith_readVarLen rfl e1
    split at e2 <;> cases e2 <;> exact Or.inl hl
  | .code o size, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.code o size) bs = _ from h)
    have hl := readInt_length _ _ _ _ e1
    split at e2
    · obtain ⟨c', b', e3, e4⟩ := readIn_next' e2
      cases e4
      have := faith_le (faith_simpleChain _ _) e3
      exact Or.inl (by omega)
    · cases e2
      exact Or.inl (by omega)
  | .clens o size [] acc sum, bs, q, c, h => by
    have h' : (if (acc.filter (·.2 != 0)).length = 1 then ORes.next (g, HPhase.syms o size (codeLengthCode acc) ⟨[], 8, none⟩) bs
        else .bad) = .next q c := h
    split at h'
    · cases h'
      right
      simp only [hstage, List.length_nil, Nat.sub_zero]
      omega
    · cases h'
  | .clens o size (x :: rest) acc sum, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.clens o size (x :: rest) acc sum) bs = _ from h)
    have hl := takes_one faith_readCodeLengthCodeLength rfl e1
    split at e2
    · cases e2; exact Or.inl hl
    · split at e2
      · cases e2; exact Or.inl hl
      · split at e2
        · cases e2
        · cases e2; exact Or.inl hl
  | .syms o size clc st, bs, q, c, h => by
    have h' : (if size < st.lens.length then ORes.bad
        else if lengthSum st.lens = 32768 then
          .next (g, ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) bs
        else if st.lens.length = size then .bad
        else readIn 18 (lenSym clc) bs fun v b =>
          if size < (applyCodeLength st v.1 v.2).lens.length then .bad
          else if 32768 < lengthSum (applyCodeLength st v.1 v.2).lens then .bad
          else .next (g, .syms o size clc (applyCodeLength st v.1 v.2)) b) = .next q c := h
    split at h'
    · cases h'
    · rename_i h1
      split at h'
      · cases h'
        right
        have := ownerPlace_stage g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))
        show hstage g (ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) <
          oStage g o + (size - st.lens.length) + 1
        omega
      · split at h'
        · cases h'
        · rename_i h3
          obtain ⟨v, b, _, e2⟩ := readIn_next' h'
          split at e2
          · cases e2
          · rename_i h4
            split at e2
            · cases e2
            · cases e2
              right
              have := applyCodeLength_length st v.1 v.2
              show oStage g o + (size - (applyCodeLength st v.1 v.2).lens.length) + 1 < oStage g o + (size - st.lens.length) + 1
              omega
  | .first i n tc cc, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.first i n tc cc) bs = _ from h)
    cases e2
    have := readBlockCount_lt e1
    exact Or.inl (by omega)
  | .np, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g .np bs = _ from h)
    cases e2
    exact Or.inl (takes_one faith_readNp rfl e1)
  | .modes done 0, bs, q, c, h => by
    cases h
    right
    simp only [hstage]
    omega
  | .modes done (n + 1), bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.modes done (n + 1)) bs = _ from h)
    cases e2
    have := readInt_length _ _ _ _ e1
    exact Or.inl (by omega)
  | .trees isL, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.trees isL) bs = _ from h)
    have hl := takes_one faith_readVarLen rfl e1
    split at e2 <;> cases e2 <;> exact Or.inl hl
  | .rlemax isL ntrees, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.rlemax isL ntrees) bs = _ from h)
    cases e2
    exact Or.inl (takes_one faith_readRLEMAX rfl e1)
  | .vals isL ntrees rlemax code done left, bs, q, c, h => by
    rcases hStep_vals_next h with ⟨h0, rfl, rfl⟩ | ⟨h0, v, _, rfl, rfl⟩ | ⟨_, _, h'⟩
    · right
      simp only [hstage]
      omega
    · right
      simp only [hstage]
      omega
    · obtain ⟨v, b, e1, e2⟩ := readIn_next' h'
      split at e2
      · cases e2
      · cases e2
        right
        have := mapSym_run e1
        show (left - v.2) + 2 < left + 2
        omega
  | .imtf isL ntrees vals, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.imtf isL ntrees vals) bs = _ from h)
    have := readInt_length _ _ _ _ e1
    generalize (if v = 0 then vals else inverseMoveToFront vals) = fin at e2
    by_cases hc : (List.range ntrees).all fin.contains = true
    · rw [ite_eq_left hc] at e2
      cases e2
      exact Or.inl (by omega)
    · rw [ite_eq_right hc] at e2
      cases e2
  | .codes k done (n + 1), bs, q, c, h => by
    cases h
    right
    simp only [hstage, ckStage]
    omega
  | .codes .L done 0, bs, q, c, h => by
    cases h
    right
    show ckStage .I (g.setCodes .L done) g.m.insertCopy.n < ckStage .L g 0
    have e : (g.setCodes .L done).treesD = g.treesD := rfl
    cases hn : g.m.insertCopy.n with
    | zero => simp only [ckStage, e, hn, ↓reduceIte]; omega
    | succ n => simp only [ckStage, hn]; split <;> omega
  | .codes .I done 0, bs, q, c, h => by
    cases h
    right
    show ckStage .D (g.setCodes .I done) g.treesD < ckStage .I g 0
    cases hn : g.treesD with
    | zero => simp only [ckStage, hn, ↓reduceIte]; omega
    | succ n => simp only [ckStage, hn]; split <;> omega
  | .codes .D done 0, bs, q, c, h => by cases h

/-! ### Where a layer ends -/

section
variable {A P E : Type}

/-- A step that never ends its layer. -/
def NoExit (k : List Bool → ORes P E) : Prop := ∀ bs e c, k bs ≠ .exit e c

theorem noExit_next (q : P) : NoExit fun bs => (.next q bs : ORes P E) := fun _ _ _ h => by cases h

theorem noExit_bad : NoExit fun _ => (.bad : ORes P E) := fun _ _ _ h => by cases h

theorem noExit_ite {c : Prop} [Decidable c] {f g : List Bool → ORes P E} (hf : NoExit f) (hg : NoExit g) :
    NoExit fun bs => if c then f bs else g bs := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf
  · simpa only [h, ↓reduceIte] using hg

theorem noExit_lookIn {o : Option A} {k : A → List Bool → ORes P E} (h : ∀ a, NoExit (k a)) : NoExit fun bs => lookIn o fun a => k a bs := by
  cases o with
  | none => exact noExit_bad
  | some a => exact h a

theorem noExit_readIn {room : Nat} {rd : List Bool → Option (A × List Bool)} {k : A → List Bool → ORes P E} (hk : ∀ a, NoExit (k a)) :
    NoExit fun bs => readIn room rd bs k := by
  intro bs e c h
  have h' : readIn room rd bs k = .exit e c := h
  unfold readIn at h'
  cases hr : rd bs with
  | none =>
    rw [hr] at h'
    dsimp only at h'
    by_cases hl : bs.length < room
    · rw [ite_eq_left hl] at h'
      cases h'
    · rw [ite_eq_right hl] at h'
      cases h'
  | some p =>
    rw [hr] at h'
    exact hk p.1 p.2 e c h'

theorem noExit_nextIn {cat : BlockCategory} {st : BlockState} {k : BlockState → List Bool → ORes P E} (hk : ∀ a, NoExit (k a)) :
    NoExit fun bs => nextIn cat st bs k := by
  show NoExit fun bs => if st.count = 0 ∧ cat.n < 2 then .bad else readIn 54 (nextElement cat st) bs k
  exact noExit_ite noExit_bad (noExit_readIn hk)

end

/-- A header ends only at its last group of codes. -/
theorem hStep_exit {g : Gh} : ∀ {p : HPhase} {bs : List Bool} {m : MetaBlockHeader} {b : List Bool}, hStepP (g, p) bs = .exit m b →
    ∃ done, p = .codes .D done 0 ∧ m = (g.setCodes .D done).m
  | .cat _, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_ite (noExit_next _) (noExit_next _)) bs _ _)
  | .code _ _, bs, _, _, h =>
    absurd h (noExit_readIn (fun _ => noExit_ite (noExit_readIn fun _ => noExit_next _) (noExit_next _)) bs _ _)
  | .clens _ _ [] _ _, bs, _, _, h => absurd h (noExit_ite (noExit_next _) noExit_bad bs _ _)
  | .clens _ _ (_ :: _) _ _, bs, _, _, h =>
    absurd h (noExit_readIn (fun _ => noExit_ite (noExit_next _) (noExit_ite (noExit_next _) (noExit_ite noExit_bad (noExit_next _)))) bs _ _)
  | .syms _ _ _ _, bs, _, _, h =>
    absurd h (noExit_ite noExit_bad (noExit_ite (noExit_next _) (noExit_ite noExit_bad
      (noExit_readIn fun _ => noExit_ite noExit_bad (noExit_ite noExit_bad (noExit_next _))))) bs _ _)
  | .first _ _ _ _, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_next _) bs _ _)
  | .np, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_next _) bs _ _)
  | .modes _ 0, bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .modes _ (_ + 1), bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_next _) bs _ _)
  | .trees _, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_ite (noExit_next _) (noExit_next _)) bs _ _)
  | .rlemax _ _, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_next _) bs _ _)
  | .vals _ _ _ _ _ _, _, _, _, h => absurd h hStep_vals_ne_exit
  | .imtf _ _ _, bs, _, _, h => absurd h (noExit_readIn (fun _ => noExit_ite (noExit_next _) noExit_bad) bs _ _)
  | .codes _ _ (_ + 1), bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .codes .L _ 0, bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .codes .I _ 0, bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .codes .D done 0, _, _, _, h => by
    cases h
    exact ⟨done, rfl, rfl⟩

/-- The commands end only at a command's start at MLEN. -/
theorem cStep_exit {w : Nat} {m : MetaBlockHeader} : ∀ {p : Phase} {bs : List Bool} {s : CommandState} {b : List Bool},
    cStep w m p bs = .exit s b → p = .command s ∧ s.remaining = 0
  | .command s, bs, s', b, h => by
    have h' : (if s.remaining = 0 then ORes.exit s bs else nextIn m.insertCopy s.insertCopy bs fun ic b => .next (Phase.insertCopy s ic) b) =
        .exit s' b := h
    split at h'
    · rename_i h0
      cases h'
      exact ⟨rfl, h0⟩
    · exact absurd h' (noExit_nextIn (fun _ => noExit_next _) bs _ _)
  | .insertCopy _ _, bs, _, _, h => absurd h (noExit_lookIn (fun _ => noExit_readIn fun _ => noExit_next _) bs _ _)
  | .copyLength _ _ _ _ _ _, bs, _, _, h => absurd h (noExit_ite noExit_bad (noExit_readIn fun _ => noExit_next _) bs _ _)
  | .literals _ _ _ _ _ 0 _ _, bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .literals _ _ _ _ _ (_ + 1) _ _, bs, _, _, h =>
    absurd h (noExit_ite (noExit_nextIn fun _ => noExit_next _) (noExit_next _) bs _ _)
  | .literalSymbol _ _ _ _ _ _ _ _, bs, _, _, h =>
    absurd h (noExit_lookIn (fun _ => noExit_lookIn fun _ => noExit_lookIn fun _ => noExit_readIn fun _ => noExit_next _) bs _ _)
  | .distance _ _ _, bs, _, _, h =>
    absurd h (noExit_ite (noExit_next _) (noExit_ite (noExit_lookIn fun _ => noExit_lookIn fun q => noExit_next q)
      (noExit_nextIn fun _ => noExit_next _)) bs _ _)
  | .distanceSymbol _ _ _, bs, _, _, h =>
    absurd h (noExit_lookIn (fun _ => noExit_lookIn fun _ => noExit_readIn fun _ =>
      noExit_lookIn fun _ => noExit_lookIn fun q => noExit_next q) bs _ _)
  | .copy _ _ 0, bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .copy _ _ (_ + 1), bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .word _ [], bs, _, _, h => absurd h (noExit_next _ bs _ _)
  | .word _ (_ :: _), bs, _, _, h => absurd h (noExit_next _ bs _ _)

theorem setCat_ndirect (g : Gh) (i : Cat) (c : BlockCategory) : (g.setCat i c).m.ndirect = g.m.ndirect := by
  cases i <;> rfl

theorem setMap_ndirect (g : Gh) (isL : Bool) (n : Nat) (cmap : List Nat) : (g.setMap isL n cmap).m.ndirect = g.m.ndirect := by
  cases isL <;> rfl

theorem setCodes_ndirect (g : Gh) (k : CK) (cs : List PrefixCode) : (g.setCodes k cs).m.ndirect = g.m.ndirect := by
  cases k <;> rfl

theorem readNp_lt {bs b : List Bool} {v : Nat × Nat} (h : readNp bs = some (v, b)) : v.1 < 4 ∧ v.2 < 16 := by
  unfold readNp at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; cases h
  | some p =>
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readInt 4 p.2 with
    | none => rw [h2] at h; cases h
    | some q =>
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨readInt_lt _ _ _ _ h1, readInt_lt _ _ _ _ h2⟩

/-- A header's NDIRECT stays at most 120. -/
theorem hStep_ndirect {g : Gh} (hn : g.m.ndirect ≤ 120) : ∀ {p : HPhase} {bs : List Bool} {q : Gh × HPhase} {c : List Bool},
    hStepP (g, p) bs = .next q c → q.1.m.ndirect ≤ 120
  | .cat i, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.cat i) bs = _ from h)
    split at e2 <;> cases e2
    · show (g.setCat i _).m.ndirect ≤ 120
      rw [setCat_ndirect]
      exact hn
    · exact hn
  | .code o size, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.code o size) bs = _ from h)
    split at e2
    · obtain ⟨_, _, _, e4⟩ := readIn_next' e2
      cases e4
      exact hn
    · cases e2
      exact hn
  | .clens o size [] acc sum, bs, q, c, h => by
    have h' : (if (acc.filter (·.2 != 0)).length = 1 then ORes.next (g, HPhase.syms o size (codeLengthCode acc) ⟨[], 8, none⟩) bs
        else .bad) = .next q c := h
    split at h' <;> cases h'
    exact hn
  | .clens o size (x :: rest) acc sum, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.clens o size (x :: rest) acc sum) bs = _ from h)
    split at e2
    · cases e2; exact hn
    · split at e2
      · cases e2; exact hn
      · split at e2
        · cases e2
        · cases e2; exact hn
  | .syms o size clc st, bs, q, c, h => by
    have h' : (if size < st.lens.length then ORes.bad
        else if lengthSum st.lens = 32768 then
          .next (g, ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) bs
        else if st.lens.length = size then .bad
        else readIn 18 (lenSym clc) bs fun v b =>
          if size < (applyCodeLength st v.1 v.2).lens.length then .bad
          else if 32768 < lengthSum (applyCodeLength st v.1 v.2).lens then .bad
          else .next (g, .syms o size clc (applyCodeLength st v.1 v.2)) b) = .next q c := h
    split at h'
    · cases h'
    · split at h'
      · cases h'; exact hn
      · split at h'
        · cases h'
        · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
          split at e2
          · cases e2
          · split at e2
            · cases e2
            · cases e2; exact hn
  | .first i n tc cc, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.first i n tc cc) bs = _ from h)
    cases e2
    show (g.setCat i _).m.ndirect ≤ 120
    rw [setCat_ndirect]
    exact hn
  | .np, bs, q, c, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g .np bs = _ from h)
    cases e2
    obtain ⟨h1, h2⟩ := readNp_lt e1
    show v.2 <<< v.1 ≤ 120
    rw [Nat.shiftLeft_eq]
    have : 2 ^ v.1 ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    rw [h8] at this
    have : v.2 * 2 ^ v.1 ≤ 15 * 8 := Nat.mul_le_mul (by omega) this
    omega
  | .modes done 0, bs, q, c, h => by
    cases h
    exact hn
  | .modes done (n + 1), bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.modes done (n + 1)) bs = _ from h)
    cases e2
    exact hn
  | .trees isL, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.trees isL) bs = _ from h)
    split at e2 <;> cases e2
    · show (g.setMap isL _ _).m.ndirect ≤ 120
      rw [setMap_ndirect]
      exact hn
    · exact hn
  | .rlemax isL ntrees, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.rlemax isL ntrees) bs = _ from h)
    cases e2
    exact hn
  | .vals isL ntrees rlemax code done left, bs, q, c, h => by
    rcases hStep_vals_next h with ⟨_, rfl, rfl⟩ | ⟨_, v, _, rfl, rfl⟩ | ⟨_, _, h'⟩
    · exact hn
    · exact hn
    · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
      split at e2
      · cases e2
      · cases e2; exact hn
  | .imtf isL ntrees vals, bs, q, c, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.imtf isL ntrees vals) bs = _ from h)
    generalize (if v = 0 then vals else inverseMoveToFront vals) = fin at e2
    by_cases hc : (List.range ntrees).all fin.contains = true
    · rw [ite_eq_left hc] at e2
      cases e2
      show (g.setMap isL ntrees fin).m.ndirect ≤ 120
      rw [setMap_ndirect]
      exact hn
    · rw [ite_eq_right hc] at e2
      cases e2
  | .codes k done (n + 1), bs, q, c, h => by
    cases h
    exact hn
  | .codes .L done 0, bs, q, c, h => by
    cases h
    show (g.setCodes .L done).m.ndirect ≤ 120
    rw [setCodes_ndirect]
    exact hn
  | .codes .I done 0, bs, q, c, h => by
    cases h
    show (g.setCodes .I done).m.ndirect ≤ 120
    rw [setCodes_ndirect]
    exact hn
  | .codes .D done 0, bs, q, c, h => by cases h

/-! ### How high a header's places rank -/

/-- What a header so far has: at most 256 block types for literals and distances, and NPOSTFIX and NDIRECT in range. -/
def GOk (g : Gh) : Prop := g.m.literal.n ≤ 256 ∧ g.m.distance.n ≤ 256 ∧ g.m.npostfix ≤ 3 ∧ g.m.ndirect ≤ 120

/-- What a code's owner has: at most 256 block types. -/
def OOk : Owner → Prop
  | .type _ n => n ≤ 256
  | .count _ n _ => n ≤ 256
  | _ => True

/-- What a header's place has: an alphabet of at most 1024 symbols, at most 256 block types or trees, and at most 16384
context map values left. -/
def HOk : HPhase → Prop
  | .code o size => size ≤ 1024 ∧ OOk o
  | .clens o size _ _ _ => size ≤ 1024 ∧ OOk o
  | .syms o size _ _ => size ≤ 1024 ∧ OOk o
  | .first _ n _ _ => n ≤ 256
  | .rlemax _ ntrees => ntrees ≤ 256
  | .vals _ _ _ _ _ left => left ≤ 16384
  | _ => True

theorem mapSize_le {g : Gh} (hg : GOk g) (isL : Bool) : mapSize g isL ≤ 16384 := by
  obtain ⟨h1, h2, _⟩ := hg
  unfold mapSize literalContextMapSize distanceContextMapSize
  split <;> omega

theorem hstage_le {g : Gh} {p : HPhase} (hg : GOk g) (hp : HOk p) : hstage g p ≤ 17500 := by
  have ho : ∀ o, oStage g o ≤ 16387 := by
    intro o
    cases o with
    | type => simp only [oStage]; omega
    | count => simp only [oStage]; omega
    | map isL => have := mapSize_le hg isL; simp only [oStage]; omega
    | codes k done left =>
      simp only [oStage]
      cases left with
      | succ => simp only [ckStage]; omega
      | zero => cases k <;> simp only [ckStage] <;> (repeat' split) <;> omega
  cases p with
  | clens o size order acc sum =>
    cases order with
    | nil => have := ho o; have := hp.1; simp only [hstage]; omega
    | cons => simp only [hstage]; omega
  | syms o size clc st => have := ho o; have := hp.1; simp only [hstage]; omega
  | vals => have : _ ≤ 16384 := hp; simp only [hstage]; omega
  | codes k done n =>
    simp only [hstage]
    cases n with
    | succ => simp only [ckStage]; omega
    | zero => cases k <;> simp only [ckStage] <;> (repeat' split) <;> omega
  | modes done n => cases n <;> simp only [hstage] <;> omega
  | cat => simp only [hstage]; omega
  | code => simp only [hstage]; omega
  | first => simp only [hstage]; omega
  | np => simp only [hstage]; omega
  | trees => simp only [hstage]; omega
  | rlemax => simp only [hstage]; omega
  | imtf => simp only [hstage]; omega

theorem setCat_gok {g : Gh} (hg : GOk g) (i : Cat) {c : BlockCategory} (hc : c.n ≤ 256) : GOk (g.setCat i c) := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  cases i
  · exact ⟨hc, h2, h3, h4⟩
  · exact ⟨h1, h2, h3, h4⟩
  · exact ⟨h1, hc, h3, h4⟩

theorem setMap_gok {g : Gh} (hg : GOk g) (isL : Bool) (n : Nat) (cmap : List Nat) : GOk (g.setMap isL n cmap) := by
  cases isL <;> exact hg

theorem setCodes_gok {g : Gh} (hg : GOk g) (k : CK) (cs : List PrefixCode) : GOk (g.setCodes k cs) := by
  cases k <;> exact hg

theorem ownerPlace_ok {g : Gh} (hg : GOk g) {o : Owner} (ho : OOk o) (c : PrefixCode) : HOk (ownerPlace g o c) := by
  cases o with
  | type i n => exact ⟨by decide, ho⟩
  | count i n tc => exact ho
  | map isL ntrees rlemax => exact mapSize_le hg isL
  | codes => trivial

theorem ckSize_le {g : Gh} (hg : GOk g) (k : CK) : ckSize k g ≤ 1024 := by
  obtain ⟨_, _, h3, h4⟩ := hg
  cases k with
  | L => show literalAlphabetSize ≤ 1024; decide
  | I => show insertCopyAlphabetSize ≤ 1024; decide
  | D =>
    show 16 + g.m.ndirect + (48 <<< g.m.npostfix) ≤ 1024
    rw [Nat.shiftLeft_eq]
    have : 2 ^ g.m.npostfix ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) h3
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    rw [h8] at this
    omega

/-- Each step of a header read in order keeps what its places have. -/
theorem hStep_ok {g : Gh} (hg : GOk g) : ∀ {p : HPhase} {bs : List Bool} {q : Gh × HPhase} {c : List Bool}, HOk p →
    hStepP (g, p) bs = .next q c → GOk q.1 ∧ HOk q.2
  | .cat i, bs, q, c, _, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.cat i) bs = _ from h)
    have hv := readVarLen_range e1
    split at e2 <;> cases e2
    · refine ⟨setCat_gok hg i (by show v ≤ 256; omega), ?_⟩
      cases i <;> trivial
    · exact ⟨hg, by show v + 2 ≤ 1024 ∧ v ≤ 256; omega⟩
  | .code o size, bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.code o size) bs = _ from h)
    split at e2
    · obtain ⟨cd, _, _, e4⟩ := readIn_next' e2
      cases e4
      exact ⟨hg, ownerPlace_ok hg hp.2 cd⟩
    · cases e2
      exact ⟨hg, hp⟩
  | .clens o size [] acc sum, bs, q, c, hp, h => by
    have h' : (if (acc.filter (·.2 != 0)).length = 1 then ORes.next (g, HPhase.syms o size (codeLengthCode acc) ⟨[], 8, none⟩) bs
        else .bad) = .next q c := h
    split at h' <;> cases h'
    exact ⟨hg, hp⟩
  | .clens o size (x :: rest) acc sum, bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.clens o size (x :: rest) acc sum) bs = _ from h)
    split at e2
    · cases e2; exact ⟨hg, hp⟩
    · split at e2
      · cases e2; exact ⟨hg, hp⟩
      · split at e2
        · cases e2
        · cases e2; exact ⟨hg, hp⟩
  | .syms o size clc st, bs, q, c, hp, h => by
    have h' : (if size < st.lens.length then ORes.bad
        else if lengthSum st.lens = 32768 then
          .next (g, ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) bs
        else if st.lens.length = size then .bad
        else readIn 18 (lenSym clc) bs fun v b =>
          if size < (applyCodeLength st v.1 v.2).lens.length then .bad
          else if 32768 < lengthSum (applyCodeLength st v.1 v.2).lens then .bad
          else .next (g, .syms o size clc (applyCodeLength st v.1 v.2)) b) = .next q c := h
    split at h'
    · cases h'
    · split at h'
      · cases h'; exact ⟨hg, ownerPlace_ok hg hp.2 _⟩
      · split at h'
        · cases h'
        · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
          split at e2
          · cases e2
          · split at e2
            · cases e2
            · cases e2; exact ⟨hg, hp⟩
  | .first i n tc cc, bs, q, c, hp, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.first i n tc cc) bs = _ from h)
    cases e2
    refine ⟨setCat_gok hg i hp, ?_⟩
    cases i <;> trivial
  | .np, bs, q, c, _, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g .np bs = _ from h)
    cases e2
    obtain ⟨h1, h2⟩ := readNp_lt e1
    obtain ⟨g1, g2, _, _⟩ := hg
    refine ⟨⟨g1, g2, by show v.1 ≤ 3; omega, ?_⟩, trivial⟩
    show v.2 <<< v.1 ≤ 120
    rw [Nat.shiftLeft_eq]
    have : 2 ^ v.1 ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) (by omega)
    have h8 : (2 : Nat) ^ 3 = 8 := rfl
    rw [h8] at this
    have : v.2 * 2 ^ v.1 ≤ 15 * 8 := Nat.mul_le_mul (by omega) this
    omega
  | .modes done 0, bs, q, c, _, h => by
    cases h
    exact ⟨hg, trivial⟩
  | .modes done (n + 1), bs, q, c, _, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.modes done (n + 1)) bs = _ from h)
    cases e2
    exact ⟨hg, trivial⟩
  | .trees isL, bs, q, c, _, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.trees isL) bs = _ from h)
    have hv := readVarLen_range e1
    split at e2 <;> cases e2
    · refine ⟨setMap_gok hg _ _ _, ?_⟩
      cases isL <;> trivial
    · exact ⟨hg, by show v ≤ 256; omega⟩
  | .rlemax isL ntrees, bs, q, c, hp, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.rlemax isL ntrees) bs = _ from h)
    cases e2
    have := readRLEMAX_range e1
    have hn : ntrees ≤ 256 := hp
    exact ⟨hg, (show ntrees + v ≤ 1024 by omega), trivial⟩
  | .vals isL ntrees rlemax code done left, bs, q, c, hp, h => by
    rcases hStep_vals_next h with ⟨_, rfl, rfl⟩ | ⟨_, v, _, rfl, rfl⟩ | ⟨_, _, h'⟩
    · exact ⟨hg, trivial⟩
    · exact ⟨hg, by show 0 ≤ 16384; omega⟩
    · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
      split at e2
      · cases e2
      · cases e2
        have hl : left ≤ 16384 := hp
        exact ⟨hg, by show left - v.2 ≤ 16384; omega⟩
  | .imtf isL ntrees vals, bs, q, c, _, h => by
    obtain ⟨v, b, _, e2⟩ := readIn_next' (show hStep g (.imtf isL ntrees vals) bs = _ from h)
    generalize (if v = 0 then vals else inverseMoveToFront vals) = fin at e2
    by_cases hc : (List.range ntrees).all fin.contains = true
    · rw [ite_eq_left hc] at e2
      cases e2
      refine ⟨setMap_gok hg _ _ _, ?_⟩
      cases isL <;> trivial
    · rw [ite_eq_right hc] at e2
      cases e2
  | .codes k done (n + 1), bs, q, c, _, h => by
    cases h
    exact ⟨hg, ckSize_le hg k, trivial⟩
  | .codes .L done 0, bs, q, c, _, h => by
    cases h
    exact ⟨setCodes_gok hg _ _, trivial⟩
  | .codes .I done 0, bs, q, c, _, h => by
    cases h
    exact ⟨setCodes_gok hg _ _, trivial⟩
  | .codes .D done 0, bs, q, c, _, h => by cases h

/-! ### The stream -/

/-- What every place of the stream the reading in order reaches has. -/
def SInv : SPhase → Prop
  | .wbits => True
  | .mblock w st => DistOk w st.distances st.produced
  | .skip w st _ _ => DistOk w st.distances st.produced
  | .raw w st _ _ => DistOk w st.distances st.produced
  | .hdr w st _ _ g p => DistOk w st.distances st.produced ∧ GOk g ∧ HOk p
  | .cmds w _ m p => m.ndirect ≤ 120 ∧ CInv w p
  | .ended _ => True

/-- A ranking of the stream's places: a step that reads and produces nothing goes lower. -/
def sstage : SPhase → Nat
  | .wbits => 1
  | .mblock .. => 1
  | .skip _ _ _ 0 => 2
  | .skip _ _ _ (_ + 1) => 1
  | .raw _ _ _ 0 => 2
  | .raw _ _ _ (_ + 1) => 1
  | .hdr _ _ _ _ g p => hstage g p
  | .cmds _ _ _ p => cstage p
  | .ended _ => 1

theorem sstage_le {p : SPhase} (h : SInv p) : sstage p ≤ 17500 := by
  cases p with
  | hdr w st last mlen g q => exact hstage_le h.2.1 h.2.2
  | cmds w last m q => have := cstage_le q; simp only [sstage]; omega
  | skip w st last n => cases n <;> simp only [sstage] <;> omega
  | raw w st last n => cases n <;> simp only [sstage] <;> omega
  | wbits => simp only [sstage]; omega
  | mblock => simp only [sstage]; omega
  | ended => simp only [sstage]; omega

/-- A compressed meta-block's window keeps the distances used so far, of which there are none when it differs. -/
theorem distOk_blockWindow {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} (h : DistOk w st.distances st.produced) :
    DistOk (blockWindow w st last mlen) st.distances st.produced := by
  unfold blockWindow
  split
  · rename_i hc
    have e : ∀ x, maxBackwardDistance x st.produced = 0 := fun x => by
      unfold maxBackwardDistance
      rw [hc.2]
      exact Nat.min_zero x
    unfold DistOk at h ⊢
    rw [e] at h ⊢
    exact h
  · exact h

theorem afterBlock_facts (w : Nat) (last : Bool) (st : StreamState) (h : DistOk w st.distances st.produced) :
    SInv (afterBlock w last st) ∧ (afterBlock w last st).out = st.output ∧ sstage (afterBlock w last st) = 1 := by
  cases last
  · exact ⟨h, rfl, rfl⟩
  · exact ⟨trivial, rfl, rfl⟩

/-- The fill bits take the bits up to a byte boundary. -/
theorem readFill_len {bs b : List Bool} (h : readFill bs = some b) : b.length + bs.length % 8 = bs.length := by
  unfold readFill at h
  cases e : readInt (bs.length % 8) bs with
  | none => rw [e] at h; simp at h
  | some p =>
    obtain ⟨v, r⟩ := p
    rw [e] at h
    dsimp only [bind, Option.bind] at h
    have := readInt_length _ _ _ _ e
    by_cases hv : v = 0
    · rw [ite_eq_left hv] at h
      cases h
      exact this
    · rw [ite_eq_right hv] at h
      cases h

/-- Each step of the stream read in order keeps what its places have, grows the output, and reads bits, produces bytes or
goes lower in the ranking. -/
theorem sStep_moves : ∀ (p : SPhase) (bs : List Bool) (q : SPhase) (c : List Bool), SInv p → sStep p bs = .next q c →
    SInv q ∧ (∃ l, q.out = l ++ p.out) ∧ (Moved bs c p.out q.out ∨ sstage q < sstage p)
  | .wbits, bs, q, c, _, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' h
    cases e2
    exact ⟨ringOk_initial _, ⟨[], rfl⟩, Or.inl (Or.inl (takes_one faith_readWBITS rfl e1))⟩
  | .mblock w st, bs, q, c, hi, h => by
    obtain ⟨ms, b, e1, e2⟩ := readIn_next' h
    have hl := takes_one faith_metaStart rfl e1
    cases ms with
    | lastEmpty =>
      cases e2
      exact ⟨trivial, ⟨[], rfl⟩, Or.inl (Or.inl hl)⟩
    | metadata last skip =>
      cases hf : readFill b with
      | none => simp only [startPlace, hf] at e2; cases e2
      | some b' =>
        simp only [startPlace, hf] at e2
        cases e2
        have := readFill_len hf
        exact ⟨hi, ⟨[], rfl⟩, Or.inl (Or.inl (by omega))⟩
    | data last mlen unc =>
      cases unc with
      | true =>
        cases hf : readFill b with
        | none => simp only [startPlace, hf, ↓reduceIte] at e2; cases e2
        | some b' =>
          simp only [startPlace, hf, ↓reduceIte] at e2
          cases e2
          have := readFill_len hf
          exact ⟨hi, ⟨[], rfl⟩, Or.inl (Or.inl (by omega))⟩
      | false =>
        simp only [startPlace, Bool.false_eq_true, ↓reduceIte] at e2
        cases e2
        exact ⟨⟨distOk_blockWindow hi, ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩, trivial⟩, ⟨[], rfl⟩,
          Or.inl (Or.inl hl)⟩
  | .skip w st last 0, bs, q, c, hi, h => by
    cases h
    obtain ⟨f1, f2, f3⟩ := afterBlock_facts w last st hi
    refine ⟨f1, ⟨[], by rw [f2]; rfl⟩, Or.inr ?_⟩
    rw [f3]
    exact (show 1 < 2 by decide)
  | .skip w st last (n + 1), bs, q, c, hi, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' h
    cases e2
    have := readInt_length _ _ _ _ e1
    exact ⟨hi, ⟨[], rfl⟩, Or.inl (Or.inl (by omega))⟩
  | .raw w st last 0, bs, q, c, hi, h => by
    cases h
    obtain ⟨f1, f2, f3⟩ := afterBlock_facts w last st hi
    refine ⟨f1, ⟨[], by rw [f2]; rfl⟩, Or.inr ?_⟩
    rw [f3]
    exact (show 1 < 2 by decide)
  | .raw w st last (n + 1), bs, q, c, hi, h => by
    obtain ⟨v, b, e1, e2⟩ := readIn_next' h
    cases e2
    have := readInt_length _ _ _ _ e1
    exact ⟨hi.mono (Nat.le_add_right _ _), ⟨[v], rfl⟩, Or.inl (Or.inl (by omega))⟩
  | .hdr w st last mlen g p, bs, q, c, hi, h => by
    cases e : hStep g p bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      refine ⟨⟨hi.1, hStep_ok hi.2.1 hi.2.2 (show hStepP (g, p) bs = _ from e)⟩, ⟨[], rfl⟩, ?_⟩
      rcases hStep_moves g p bs q' _ e with hl | hl
      · exact Or.inl (Or.inl hl)
      · exact Or.inr hl
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, e]
      rw [h'] at h
      cases h
      obtain ⟨done, rfl, rfl⟩ := hStep_exit (show hStepP (g, p) bs = _ from e)
      refine ⟨⟨by rw [setCodes_ndirect]; exact hi.2.1.2.2.2, hi.1⟩, ⟨[], rfl⟩, Or.inr ?_⟩
      show cstage (.command (startState st mlen _)) < ckStage .D g 0
      simp only [cstage, ckStage]
      split <;> omega
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, e]
      rw [h'] at h
      cases h
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, e]
      rw [h'] at h
      cases h
  | .cmds w last m p, bs, q, c, hi, h => by
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h'] at h
      cases h
      obtain ⟨f1, f2, f3⟩ := cStep_moves hi.1 p bs p' _ hi.2 e
      exact ⟨⟨hi.1, f1⟩, f2, f3⟩
    | exit s b =>
      obtain ⟨rfl, h0⟩ := cStep_exit e
      have hb : b = bs := by
        have e' : cStep w m (.command s) bs = .exit s bs := by
          show (if s.remaining = 0 then _ else _) = _
          rw [ite_eq_left h0]
        rw [e'] at e
        cases e
        rfl
      subst hb
      by_cases hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance) = true
      · have h' : sStep (.cmds w last m (.command s)) b = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b := by
          simp only [sStep, e, hc, ↓reduceIte]
        rw [h'] at h
        cases h
        obtain ⟨f1, f2, f3⟩ := afterBlock_facts w last ⟨s.output, s.produced, s.distances⟩ hi.2
        refine ⟨f1, ⟨[], by rw [f2]; rfl⟩, Or.inr ?_⟩
        rw [f3]
        show 1 < cstage (.command s)
        simp only [cstage, h0, ↓reduceIte]
        omega
      · have h' : sStep (.cmds w last m (.command s)) b = .bad := by
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
  | .ended st, bs, q, c, _, h => by
    by_cases hm : bs.length % 8 = 0
    · simp only [sStep, hm, ↓reduceIte] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
      | some b =>
        simp only [sStep, hm, ↓reduceIte, e] at h
        cases h
        have := readFill_len e
        exact ⟨trivial, ⟨[], rfl⟩, Or.inl (Or.inl (by omega))⟩

/-! ### Counting the steps -/

/-- The places the reading in order reaches from a place in `n` steps. -/
inductive ReachN {P E : Type} (step : P → List Bool → ORes P E) : Nat → P → List Bool → P → List Bool → Prop
  | refl (p : P) (bs : List Bool) : ReachN step 0 p bs p bs
  | next {n : Nat} {p : P} {bs : List Bool} {p' : P} {bs' : List Bool} {q : P} {c : List Bool} :
      step p bs = .next p' bs' → ReachN step n p' bs' q c → ReachN step (n + 1) p bs q c

theorem ReachN.reach {P E : Type} {step : P → List Bool → ORes P E} {n : Nat} {p q : P} {bs c : List Bool}
    (h : ReachN step n p bs q c) : Reach step p bs q c := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next hs ih

theorem Reach.count {P E : Type} {step : P → List Bool → ORes P E} {p q : P} {bs c : List Bool} (h : Reach step p bs q c) :
    ∃ n, ReachN step n p bs q c := by
  induction h with
  | refl => exact ⟨0, .refl _ _⟩
  | next hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, .next hs hn⟩

/-- The reading in order of a stream takes at most 17501 steps for each bit it reads and each byte it produces, and 17500
more. -/
theorem steps_le : ∀ {n : Nat} {p : SPhase} {bs : List Bool} {q : SPhase} {c : List Bool}, ReachN sStep n p bs q c → SInv p →
    SInv q ∧ c.length ≤ bs.length ∧ p.out.length ≤ q.out.length ∧
      n + sstage q + 17501 * c.length + 17501 * p.out.length ≤ 17501 * bs.length + 17501 * q.out.length + sstage p := by
  intro n p bs q c h
  induction h with
  | refl => intro hi; exact ⟨hi, Nat.le_refl _, Nat.le_refl _, by omega⟩
  | @next n p bs p' bs' q c hs _ ih =>
    intro hi
    obtain ⟨hi', ⟨l, hl⟩, hm⟩ := sStep_moves p bs p' bs' hi hs
    obtain ⟨u, hu, _⟩ := nfaith_sStep p bs p' bs' hs
    have hb : bs'.length + u.length = bs.length := by rw [hu, List.length_append]; omega
    have ho : p'.out.length = l.length + p.out.length := by rw [hl, List.length_append]
    have hs' := sstage_le hi'
    obtain ⟨hq, h1, h2, h3⟩ := ih hi'
    refine ⟨hq, by omega, by omega, ?_⟩
    rcases hm with (hm | hm) | hm
    · omega
    · omega
    · omega

end Brotli.Decoder
