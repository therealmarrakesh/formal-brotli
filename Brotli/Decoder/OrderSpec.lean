module

public import Brotli.Decoder.StreamTop

@[expose] public section

/-!
# The reading in order is the spec's

Each step of the reading in order says what the spec says from where it is: a step that goes on reaches a place worth
the same, a step that ends a layer gives what follows the layer, and a rejection or too few bits is where the spec
rejects the bits at hand. So the reading in order of a stream's first bytes reaches only places whose worth is what
`decode` gives for those bytes, and its end is `decode`'s result.
-/

namespace Brotli.Decoder

open Brotli.Spec

section
variable {A P E α : Type}

/-- A step that says what `f` says, with `M` what its places are worth and `X` what its ends are worth. -/
def Agrees (M : P → List Bool → Option α) (X : E → List Bool → Option α) (k : List Bool → ORes P E) (f : List Bool → Option α) :
    Prop :=
  ∀ bs, (∀ q c, k bs = .next q c → f bs = M q c) ∧ (∀ e c, k bs = .exit e c → f bs = X e c) ∧
    (k bs = .bad → f bs = none) ∧ (k bs = .short → f bs = none)

variable {M : P → List Bool → Option α} {X : E → List Bool → Option α}

theorem agrees_next (q : P) : Agrees M X (fun bs => .next q bs) (M q) := fun _ =>
  ⟨(fun _ _ h => by cases h; rfl), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩

theorem agrees_exit (e : E) : Agrees M X (fun bs => .exit e bs) (X e) := fun _ =>
  ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h; rfl), (fun h => by cases h), (fun h => by cases h)⟩

theorem agrees_bad : Agrees M X (fun _ => .bad) (fun _ => none) := fun _ =>
  ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => rfl), (fun h => by cases h)⟩

theorem agrees_congr {k : List Bool → ORes P E} {f g : List Bool → Option α} (h : Agrees M X k f) (e : ∀ bs, g bs = f bs) :
    Agrees M X k g := by
  intro bs
  rw [e bs]
  exact h bs

theorem agrees_kcongr {k k' : List Bool → ORes P E} {f : List Bool → Option α} (e : ∀ bs, k' bs = k bs) (h : Agrees M X k f) :
    Agrees M X k' f := by
  intro bs
  rw [e bs]
  exact h bs

theorem agrees_ite {c : Prop} [Decidable c] {k1 k2 : List Bool → ORes P E} {f1 f2 : List Bool → Option α}
    (h1 : Agrees M X k1 f1) (h2 : Agrees M X k2 f2) :
    Agrees M X (fun bs => if c then k1 bs else k2 bs) (fun bs => if c then f1 bs else f2 bs) := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using h1
  · simpa only [h, ↓reduceIte] using h2

theorem agrees_lookIn {o : Option A} {k : A → List Bool → ORes P E} {f : A → List Bool → Option α}
    (h : ∀ a, Agrees M X (k a) (f a)) : Agrees M X (fun bs => lookIn o fun a => k a bs) (fun bs => o >>= fun a => f a bs) := by
  cases o with
  | none => exact agrees_bad
  | some a => exact h a

theorem agrees_readIn {room : Nat} {rd : List Bool → Option (A × List Bool)} {k : A → List Bool → ORes P E}
    {f : A → List Bool → Option α} (h : ∀ a, Agrees M X (k a) (f a)) :
    Agrees M X (fun bs => readIn room rd bs k) (fun bs => rd bs >>= fun p => f p.1 p.2) := by
  intro bs
  dsimp only
  have hk0 : readIn room rd bs k = match rd bs with | some (v, b) => k v b | none => if bs.length < room then .short else .bad := rfl
  rw [hk0]
  cases rd bs with
  | none =>
    by_cases hl : bs.length < room
    · rw [ite_eq_left hl]
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => rfl)⟩
    · rw [ite_eq_right hl]
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => rfl), (fun h => by cases h)⟩
  | some p =>
    obtain ⟨a, b⟩ := p
    exact h a b

theorem agrees_nextIn {c : BlockCategory} {st : BlockState} {k : BlockState → List Bool → ORes P E}
    {f : BlockState → List Bool → Option α} (h : ∀ a, Agrees M X (k a) (f a)) :
    Agrees M X (fun bs => nextIn c st bs k) (fun bs => nextElement c st bs >>= fun p => f p.1 p.2) := by
  by_cases h0 : st.count = 0 ∧ c.n < 2
  · have e : (fun bs => nextIn c st bs k) = fun _ => .bad := funext fun bs => by
      unfold nextIn
      rw [ite_eq_left h0]
    rw [e]
    exact agrees_congr (f := fun _ => none) agrees_bad fun bs => by rw [nextElement_single bs h0.1 h0.2]; rfl
  · have e : (fun bs => nextIn c st bs k) = fun bs => readIn 54 (nextElement c st) bs k := funext fun bs => by
      unfold nextIn
      rw [ite_eq_right h0]
    rw [e]
    exact agrees_readIn h

/-- A step that reads the fill bits and goes on. -/
theorem agrees_fill {k : List Bool → ORes P E} {f : List Bool → Option α} (q : P)
    (hk : ∀ bs, k bs = match readFill bs with | some b => .next q b | none => .bad)
    (hf : ∀ bs, f bs = readFill bs >>= fun b => M q b) : Agrees M X k f := by
  intro bs
  rw [hk, hf]
  cases readFill bs with
  | none => exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => rfl), (fun h => by cases h)⟩
  | some b => exact ⟨(fun _ _ h => by cases h; rfl), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩

end

/-! ### A meta-block's commands -/

section
variable {α : Type}

private theorem rest_insertCopy_half (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (ic : BlockState) (bs : List Bool) :
    rest w m K (.insertCopy s ic) bs = m.insertCopyCodes[ic.types.cur]? >>= fun code => readInsertHalf code bs >>= fun p =>
      rest w m K (.copyLength s ic p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2) p.2 := by
  rw [rest_insertCopy]
  cases m.insertCopyCodes[ic.types.cur]? with
  | none => rfl
  | some code =>
    show (decodeSymbol code bs >>= _) = readInsertHalf code bs >>= _
    unfold readInsertHalf
    cases decodeSymbol code bs with
    | none => rfl
    | some p =>
      obtain ⟨c, b⟩ := p
      show (insertCopyCodes c >>= _) = (insertCopyCodes c >>= _) >>= _
      cases insertCopyCodes c with
      | none => rfl
      | some q =>
        obtain ⟨i, cc⟩ := q
        show (insertLengthCodes[i]? >>= _) = (insertLengthCodes[i]? >>= _) >>= _
        cases insertLengthCodes[i]? with
        | none => rfl
        | some r =>
          obtain ⟨ib, ibase, _⟩ := r
          show (copyLengthCodes[cc]? >>= _) = (copyLengthCodes[cc]? >>= _) >>= _
          cases copyLengthCodes[cc]? with
          | none => rfl
          | some u =>
            obtain ⟨cb, cbase, _⟩ := u
            show (readInt ib b >>= _) = (readInt ib b >>= _) >>= _
            cases readInt ib b with
            | none => rfl
            | some v => rfl

private theorem rest_copyLength_check (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (ic : BlockState) (c ilen copyBits copyBase : Nat) (bs : List Bool) :
    rest w m K (.copyLength s ic c ilen copyBits copyBase) bs = if s.remaining < ilen then none
      else readInt copyBits bs >>= fun p => rest w m K (.literals s ic c ilen (copyBase + p.1) ilen s.literal s.output) p.2 := by
  rw [rest_copyLength]
  by_cases hc : s.remaining < ilen
  · rw [ite_eq_left hc]
    cases readInt copyBits bs with
    | none => rfl
    | some p => exact ite_eq_left hc
  · rw [ite_eq_right hc]
    cases readInt copyBits bs with
    | none => rfl
    | some p => exact ite_eq_right hc

private theorem rest_literals_succ (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (ic : BlockState) (c ilen clen n : Nat) (lit : BlockState) (out : List Nat) (bs : List Bool) :
    rest w m K (.literals s ic c ilen clen (n + 1) lit out) bs = if lit.count = 0 then
        nextElement m.literal lit bs >>= fun p => rest w m K (.literals s ic c ilen clen (n + 1) { p.1 with count := p.1.count + 1 } out) p.2
      else rest w m K (.literalSymbol s ic c ilen clen n { lit with count := lit.count - 1 } out) bs := by
  by_cases h0 : lit.count = 0
  · rw [ite_eq_left h0, rest_literal]
    cases nextElement m.literal lit bs with
    | none => rfl
    | some p =>
      obtain ⟨l', b⟩ := p
      show rest w m K (.literalSymbol s ic c ilen clen n l' out) b = rest w m K (.literals s ic c ilen clen (n + 1) { l' with count := l'.count + 1 } out) b
      rw [rest_literal, nextElement_count b (show ({ l' with count := l'.count + 1 } : BlockState).count ≠ 0 by simp)]
      show _ = rest w m K (.literalSymbol s ic c ilen clen n { { l' with count := l'.count + 1 } with count := l'.count + 1 - 1 } out) b
      rw [Nat.add_sub_cancel]
  · rw [ite_eq_right h0, rest_literal, nextElement_count bs h0]
    rfl

private theorem rest_distance_parts (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (c clen : Nat) (bs : List Bool) :
    rest w m K (.distance s c clen) bs = if s.remaining = 0 then rest w m K (.command s) bs
      else if implicitZeroDistance c = true then
        distanceOf m.npostfix m.ndirect s.distances 0 0 >>= fun d => copyPhase w s clen 0 d >>= fun q => rest w m K q bs
      else nextElement m.distance s.distance bs >>= fun p => rest w m K (.distanceSymbol s clen p.1) p.2 := by
  by_cases h0 : s.remaining = 0
  · rw [ite_eq_left h0, rest_distance_end bs h0]
  · rw [ite_eq_right h0]
    by_cases hc : implicitZeroDistance c = true
    · rw [ite_eq_left hc, rest_distance_implicit bs h0 hc]
    · rw [ite_eq_right hc, rest_distance_switch bs h0 (by simpa using hc)]

private theorem rest_distanceSymbol_parts (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α) (s : CommandState)
    (clen : Nat) (dist : BlockState) (bs : List Bool) :
    rest w m K (.distanceSymbol s clen dist) bs =
      distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen) >>= fun index =>
      m.distanceCodes[index]? >>= fun code =>
      readDistanceParts m.npostfix m.ndirect code bs >>= fun v =>
      distanceOf m.npostfix m.ndirect s.distances v.1.1 v.1.2 >>= fun d =>
      copyPhase w { s with distance := dist } clen v.1.1 d >>= fun q => rest w m K q v.2 := by
  cases hi : distancePrefixCodeIndex m.distanceMap dist.types.cur (distanceContextId clen) with
  | none => simp only [rest, hi, bind, Option.bind]
  | some tree =>
    cases hc : m.distanceCodes[tree]? with
    | none => simp only [rest, hi, hc, bind, Option.bind]
    | some code =>
      cases hd : decodeSymbol code bs with
      | none =>
        rw [rest_distanceSymbol_none hi hc hd]
        simp only [bind, Option.bind, readDistanceParts, hd, hc]
      | some p =>
        obtain ⟨dc, r⟩ := p
        rw [rest_distanceSymbol hi hc hd]
        simp only [bind, Option.bind, readDistanceParts, hd, hc]
        cases readInt (distanceExtraBits m.npostfix m.ndirect dc) r with
        | none => rfl
        | some q => rfl

/-- Each step of the commands read in order says what the spec says. -/
theorem cAgree (w : Nat) (m : MetaBlockHeader) (A : StreamState → List Bool → Option α) :
    ∀ p, Agrees (rest w m (cmdK w A m)) (finishC A m) (cStep w m p) (rest w m (cmdK w A m) p)
  | .command s => agrees_congr (agrees_ite (agrees_exit s) (agrees_nextIn fun _ => agrees_next _)) fun bs => by
      show cmdK w A m s bs = _
      by_cases h0 : s.remaining = 0
      · rw [ite_eq_left h0, cmdK_stop s bs h0]
      · rw [ite_eq_right h0, cmdK_step s bs h0, readCommand_rest]
  | .insertCopy s ic => agrees_congr (agrees_lookIn fun _ => agrees_readIn fun _ => agrees_next _) fun bs =>
      rest_insertCopy_half w m _ s ic bs
  | .copyLength s ic c ilen copyBits copyBase => agrees_congr (agrees_ite agrees_bad (agrees_readIn fun _ => agrees_next _)) fun bs =>
      rest_copyLength_check w m _ s ic c ilen copyBits copyBase bs
  | .literals _ _ _ _ _ 0 _ _ => agrees_next _
  | .literals s ic c ilen clen (n + 1) lit out =>
    agrees_congr (agrees_ite (agrees_nextIn fun _ => agrees_next _) (agrees_next _)) fun bs =>
      rest_literals_succ w m _ s ic c ilen clen n lit out bs
  | .literalSymbol _ _ _ _ _ _ _ _ =>
    agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_readIn fun _ => agrees_next _
  | .distance s c clen =>
    agrees_congr (agrees_ite (agrees_next _) (agrees_ite (agrees_lookIn fun _ => agrees_lookIn fun q => agrees_next q)
      (agrees_nextIn fun _ => agrees_next _))) fun bs => rest_distance_parts w m _ s c clen bs
  | .distanceSymbol s clen dist =>
    agrees_congr (agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_readIn fun _ =>
      agrees_lookIn fun _ => agrees_lookIn fun q => agrees_next q) fun bs => rest_distanceSymbol_parts w m _ s clen dist bs
  | .copy _ _ 0 => agrees_next _
  | .copy _ _ (_ + 1) => agrees_next _
  | .word _ [] => agrees_congr (agrees_next _) fun bs => rest_word_end w m _ _ bs
  | .word _ (_ :: _) => agrees_congr (agrees_next _) fun bs => rest_word w m _ _ _ _ bs

end

/-! ### A header -/

section
variable {P E : Type}

/-- A step that goes on, or ends, the same way whatever bits follow what it took. -/
def UFaith (k : List Bool → ORes P E) : Prop :=
  (∀ bs q r, k bs = .next q r → ∃ u, bs = u ++ r ∧ ∀ t, k (u ++ t) = .next q t) ∧
  (∀ bs e r, k bs = .exit e r → ∃ u, bs = u ++ r ∧ ∀ t, k (u ++ t) = .exit e t)

theorem ufaith_next (q : P) : UFaith (fun bs => (.next q bs : ORes P E)) :=
  ⟨(fun _ _ _ h => by cases h; exact ⟨[], rfl, fun _ => rfl⟩), (fun _ _ _ h => by cases h)⟩

theorem ufaith_exit (e : E) : UFaith (fun bs => (.exit e bs : ORes P E)) :=
  ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h; exact ⟨[], rfl, fun _ => rfl⟩)⟩

theorem ufaith_bad : UFaith (fun _ => (.bad : ORes P E)) := ⟨(fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩

theorem ufaith_ite {c : Prop} [Decidable c] {k1 k2 : List Bool → ORes P E} (h1 : UFaith k1) (h2 : UFaith k2) :
    UFaith (fun bs => if c then k1 bs else k2 bs) := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using h1
  · simpa only [h, ↓reduceIte] using h2

theorem ufaith_readIn {A : Type} {room : Nat} {rd : List Bool → Option (A × List Bool)} {k : A → List Bool → ORes P E}
    (hf : Faith rd) (h : ∀ a, UFaith (k a)) : UFaith (fun bs => readIn room rd bs k) := by
  have hk0 : ∀ bs, readIn room rd bs k = match rd bs with | some (v, b) => k v b | none => if bs.length < room then .short else .bad :=
    fun _ => rfl
  refine ⟨fun bs q r hn => ?_, fun bs x r hx => ?_⟩
  · dsimp only at hn
    cases e : rd bs with
    | none =>
      rw [hk0, e] at hn
      dsimp only at hn
      split at hn <;> cases hn
    | some p =>
      obtain ⟨v, b⟩ := p
      rw [hk0, e] at hn
      obtain ⟨u1, hb, hk⟩ := (h v).1 b q r hn
      obtain ⟨u0, hu0, hr⟩ := hf bs v b e
      refine ⟨u0 ++ u1, by rw [hu0, hb, List.append_assoc], fun t => ?_⟩
      show readIn room rd (u0 ++ u1 ++ t) k = _
      rw [List.append_assoc, readIn_some (hr (u1 ++ t))]
      exact hk t
  · dsimp only at hx
    cases e : rd bs with
    | none =>
      rw [hk0, e] at hx
      dsimp only at hx
      split at hx <;> cases hx
    | some p =>
      obtain ⟨v, b⟩ := p
      rw [hk0, e] at hx
      obtain ⟨u1, hb, hk⟩ := (h v).2 b x r hx
      obtain ⟨u0, hu0, hr⟩ := hf bs v b e
      refine ⟨u0 ++ u1, by rw [hu0, hb, List.append_assoc], fun t => ?_⟩
      show readIn room rd (u0 ++ u1 ++ t) k = _
      rw [List.append_assoc, readIn_some (hr (u1 ++ t))]
      exact hk t

/-- Reading the first bits of a stream follows the reading of the whole until it can't go on. -/
theorem reach_cut {step : P → List Bool → ORes P E} (hs : ∀ p, UFaith (step p)) {s t : P} {A R c : List Bool}
    (h : Reach step s (A ++ R) t c) (hc : c.length < R.length) :
    ∃ s' c', Reach step s A s' c' ∧ (∀ q r, step s' c' ≠ .next q r) ∧ Reach step s (A ++ R) s' (c' ++ R) ∧
      Reach step s' (c' ++ R) t c := by
  generalize hB : A ++ R = B at h
  induction h generalizing A with
  | refl =>
    subst hB
    rw [List.length_append] at hc
    omega
  | @next p0 b0 p1 b1 q c' hst hr ih =>
    subst hB
    cases e : step p0 A with
    | next s1 a1 =>
      obtain ⟨u, hu, hk⟩ := (hs p0).1 A s1 a1 e
      have e2 : step p0 (A ++ R) = .next s1 (a1 ++ R) := by rw [hu, List.append_assoc, hk]
      rw [e2] at hst
      cases hst
      obtain ⟨s', c'', h1, h2, h3, h4⟩ := ih (A := a1) hc rfl
      exact ⟨s', c'', .next e h1, h2, .next e2 h3, h4⟩
    | exit _ _ => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩
    | bad => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩
    | short => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩

/-- The same, for a step that keeps to whole bytes: the bits after the first are whole bytes. -/
theorem reach_cut8 {step : P → List Bool → ORes P E} (hs : ∀ p, NFaith (step p)) {s t : P} {A R c : List Bool}
    (h : Reach step s (A ++ R) t c) (hc : c.length < R.length) (hR : R.length % 8 = 0) :
    ∃ s' c', Reach step s A s' c' ∧ (∀ q r, step s' c' ≠ .next q r) ∧ Reach step s (A ++ R) s' (c' ++ R) ∧
      Reach step s' (c' ++ R) t c := by
  generalize hB : A ++ R = B at h
  induction h generalizing A with
  | refl =>
    subst hB
    rw [List.length_append] at hc
    omega
  | @next p0 b0 p1 b1 q c' hst hr ih =>
    subst hB
    cases e : step p0 A with
    | next s1 a1 =>
      obtain ⟨u, hu, hk⟩ := hs p0 A s1 a1 e
      have e2 : step p0 (A ++ R) = .next s1 (a1 ++ R) := by
        rw [hu, List.append_assoc, hk _ (by rw [List.length_append]; omega)]
      rw [e2] at hst
      cases hst
      obtain ⟨s', c'', h1, h2, h3, h4⟩ := ih (A := a1) hc rfl
      exact ⟨s', c'', .next e h1, h2, .next e2 h3, h4⟩
    | exit _ _ => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩
    | bad => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩
    | short => exact ⟨p0, A, .refl _ _, (fun _ _ h => by rw [e] at h; cases h), .refl _ _, .next hst hr⟩

end

/-- A header's steps go on whatever bits follow what they took: its readers take no notice of the bits after them. -/
theorem ufaith_hStep (g : Gh) : ∀ p, UFaith (hStepP (g, p))
  | .cat _ => ufaith_readIn faith_readVarLen fun _ => ufaith_ite (ufaith_next _) (ufaith_next _)
  | .code _ _ =>
    ufaith_readIn (faith_readInt 2) fun _ => ufaith_ite (ufaith_readIn (faith_simpleChain _ _) fun _ => ufaith_next _) (ufaith_next _)
  | .clens _ _ [] _ _ => ufaith_ite (ufaith_next _) ufaith_bad
  | .clens _ _ (_ :: _) _ _ =>
    ufaith_readIn faith_readCodeLengthCodeLength fun _ =>
      ufaith_ite (ufaith_next _) (ufaith_ite (ufaith_next _) (ufaith_ite ufaith_bad (ufaith_next _)))
  | .syms _ _ _ _ =>
    ufaith_ite ufaith_bad (ufaith_ite (ufaith_next _) (ufaith_ite ufaith_bad
      (ufaith_readIn (faith_lenSym _) fun _ => ufaith_ite ufaith_bad (ufaith_ite ufaith_bad (ufaith_next _)))))
  | .first _ _ _ _ => ufaith_readIn (faith_readBlockCount _) fun _ => ufaith_next _
  | .np => ufaith_readIn faith_readNp fun _ => ufaith_next _
  | .modes _ 0 => ufaith_next _
  | .modes _ (_ + 1) => ufaith_readIn (faith_readInt 2) fun _ => ufaith_next _
  | .trees _ => ufaith_readIn faith_readVarLen fun _ => ufaith_ite (ufaith_next _) (ufaith_next _)
  | .rlemax _ _ => ufaith_readIn faith_readRLEMAX fun _ => ufaith_next _
  | .vals _ _ rlemax code _ _ => ufaith_ite (ufaith_next _) (by
      cases runOf rlemax code with
      | some _ => exact ufaith_next _
      | none => exact ufaith_readIn (faith_mapSym _ _) fun _ => ufaith_ite ufaith_bad (ufaith_next _))
  | .imtf _ _ _ => ufaith_readIn (faith_readInt 1) fun _ => ufaith_ite (ufaith_next _) ufaith_bad
  | .codes _ _ (_ + 1) => ufaith_next _
  | .codes .L _ 0 => ufaith_next _
  | .codes .I _ 0 => ufaith_next _
  | .codes .D _ 0 => ufaith_exit _

section
variable {α : Type} (K : HK α)

/-- A step of a header read in order that says what `f` says, up to the table the step completes, and completes the same
table whatever bits follow what it took. -/
def AgreesW (k : List Bool → ORes (Gh × HPhase) MetaBlockHeader) (f : List Bool → Option α) : Prop :=
  ∀ bs, (∀ q c, k bs = .next q c → ∃ oc u, bs = u ++ c ∧ ∀ t, k (u ++ t) = .next q t → f (u ++ t) = Wr K oc (hrest K q.1 q.2 t)) ∧
    (∀ e c, k bs = .exit e c → f bs = K.k e c) ∧ (k bs = .bad → f bs = none) ∧ (k bs = .short → f bs = none)

variable {K}

theorem agreesW_of {k : List Bool → ORes (Gh × HPhase) MetaBlockHeader} {f : List Bool → Option α}
    (h : Agrees (fun q bs => hrest K q.1 q.2 bs) K.k k f) (hu : UFaith k) : AgreesW K k f := fun bs =>
  ⟨fun q c e => by
    obtain ⟨u, e1, _⟩ := hu.1 bs q c e
    exact ⟨none, u, e1, fun t ht => (h (u ++ t)).1 q t ht⟩, (h bs).2.1, (h bs).2.2.1, (h bs).2.2.2⟩

theorem agreesW_ofH (g : Gh) {p : HPhase} {f : List Bool → Option α}
    (h : Agrees (fun q bs => hrest K q.1 q.2 bs) K.k (hStepP (g, p)) f) : AgreesW K (hStepP (g, p)) f :=
  agreesW_of h (ufaith_hStep g p)

theorem agreesW_congr {k : List Bool → ORes (Gh × HPhase) MetaBlockHeader} {f g : List Bool → Option α} (h : AgreesW K k f)
    (e : ∀ bs, g bs = f bs) : AgreesW K k g := by
  intro bs
  refine ⟨fun q c hn => ?_, fun x c hx => by rw [e]; exact (h bs).2.1 x c hx, fun hb => by rw [e]; exact (h bs).2.2.1 hb,
    fun hs => by rw [e]; exact (h bs).2.2.2 hs⟩
  obtain ⟨oc, u, e1, hk⟩ := (h bs).1 q c hn
  exact ⟨oc, u, e1, fun t ht => by rw [e]; exact hk t ht⟩

theorem agreesW_next (q : Gh × HPhase) (oc : Option Hook) :
    AgreesW K (fun bs => .next q bs) (fun bs => Wr K oc (hrest K q.1 q.2 bs)) := fun _ =>
  ⟨(fun _ _ h => by cases h; exact ⟨oc, [], rfl, fun t ht => by cases ht; rfl⟩), (fun _ _ h => by cases h), (fun h => by cases h),
    (fun h => by cases h)⟩

theorem agreesW_next0 (q : Gh × HPhase) : AgreesW K (fun bs => .next q bs) (hrest K q.1 q.2) :=
  agreesW_of (agrees_next q) (ufaith_next q)

theorem agreesW_bad : AgreesW K (fun _ => .bad) (fun _ => none) := agreesW_of agrees_bad ufaith_bad

theorem agreesW_ite {c : Prop} [Decidable c] {k1 k2 : List Bool → ORes (Gh × HPhase) MetaBlockHeader} {f1 f2 : List Bool → Option α}
    (h1 : AgreesW K k1 f1) (h2 : AgreesW K k2 f2) :
    AgreesW K (fun bs => if c then k1 bs else k2 bs) (fun bs => if c then f1 bs else f2 bs) := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using h1
  · simpa only [h, ↓reduceIte] using h2

theorem agreesW_readIn {A : Type} {room : Nat} {rd : List Bool → Option (A × List Bool)}
    {k : A → List Bool → ORes (Gh × HPhase) MetaBlockHeader} {f : A → List Bool → Option α} (hf : Faith rd)
    (h : ∀ a, AgreesW K (k a) (f a)) :
    AgreesW K (fun bs => readIn room rd bs k) (fun bs => rd bs >>= fun p => f p.1 p.2) := by
  intro bs
  dsimp only
  have hk0 : ∀ bs, readIn room rd bs k = match rd bs with | some (v, b) => k v b | none => if bs.length < room then .short else .bad :=
    fun _ => rfl
  cases e : rd bs with
  | none =>
    rw [hk0, e]
    by_cases hl : bs.length < room
    · rw [ite_eq_left hl]
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => rfl)⟩
    · rw [ite_eq_right hl]
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => rfl), (fun h => by cases h)⟩
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [hk0, e]
    obtain ⟨h1, h2, h3, h4⟩ := h a b
    refine ⟨fun q c hn => ?_, h2, h3, h4⟩
    obtain ⟨oc, u1, hb, hk⟩ := h1 q c hn
    obtain ⟨u0, hu0, hr⟩ := hf bs a b e
    refine ⟨oc, u0 ++ u1, by rw [hu0, hb, List.append_assoc], fun t ht => ?_⟩
    have e3 : rd (u0 ++ u1 ++ t) = some (a, u1 ++ t) := by rw [List.append_assoc]; exact hr (u1 ++ t)
    have ht' : k a (u1 ++ t) = .next q t := (readIn_some e3).symm.trans ht
    show (rd (u0 ++ u1 ++ t) >>= fun p => f p.1 p.2) = _
    rw [e3]
    exact hk t ht'

/-- The hook at a context map's end: the groups' reservation, after the distance context map. -/
def mapHook (g : Gh) : Bool → Option Hook
  | true => none
  | false => some (.res g)

variable (K)

theorem mapR_eq (g : Gh) (isL : Bool) (x : Option α) : mapR K g isL x = Wr K (mapHook g isL) x := by
  cases isL <;> rfl

/-- What follows a prefix code is the place its owner goes on to. -/
theorem ownerK_place (g : Gh) (o : Owner) (c : PrefixCode) (bs : List Bool) : ownerK K g o c bs = hrest K g (ownerPlace g o c) bs := by
  cases o <;> rfl

end

section
variable {α : Type} (K : HK α) (hw : ∀ g x, K.r g x = x)
include hw

omit hw in
private theorem hrest_syms_over (g : Gh) (o : Owner) (size : Nat) (clc : PrefixCode) (st : LengthState) (bs : List Bool)
    (h : size < st.lens.length) : hrest K g (.syms o size clc st) bs = none := by
  show (symsFrom size clc st bs >>= _) = none
  unfold symsFrom
  rw [show size + 1 - st.lens.length = 0 by omega]
  rfl

omit hw in
/-- Each step of a header read in order says what the spec says, with the table it completes. -/
theorem hAgreeW (g : Gh) : ∀ p, AgreesW K (hStepP (g, p)) (hrest K g p)
  | .cat i => agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_ite (agrees_next _) (agrees_next _)) fun bs => by
      rw [hrest_cat]
      congr 1
      funext p
      rw [afterCat_eq] <;> rfl)
  | .code o size => agreesW_congr (agreesW_readIn (faith_readInt 2) fun _ =>
      agreesW_ite (agreesW_readIn (faith_simpleChain _ _) fun _ => agreesW_next0 _)
      (agreesW_next0 _)) fun bs => by
      rw [hrest_code]
      congr 1
      funext h
      simp only [ownerK_place K]
  | .clens o size [] acc sum => agreesW_ofH g (agrees_congr (agrees_ite (agrees_next _) agrees_bad) fun bs => hrest_clens_nil K g o size acc sum bs)
  | .clens o size (x :: rest) acc sum =>
    agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_ite (agrees_next _) (agrees_ite (agrees_next _) (agrees_ite agrees_bad (agrees_next _))))
      fun bs => hrest_clens_cons K g o size x rest acc sum bs)
  | .syms o size clc st =>
    agreesW_congr (agreesW_ite agreesW_bad (agreesW_ite (agreesW_next0 _)
      (agreesW_ite agreesW_bad (agreesW_readIn (faith_lenSym _) fun _ => agreesW_ite agreesW_bad (agreesW_ite agreesW_bad (agreesW_next0 _)))))) fun bs => by
      by_cases h1 : size < st.lens.length
      · rw [ite_eq_left h1]
        exact hrest_syms_over K g o size clc st bs h1
      · rw [ite_eq_right h1]
        by_cases h2 : lengthSum st.lens = 32768
        · rw [ite_eq_left h2, hrest_syms_done K g o size clc st bs (by omega) h2, ownerK_place K]
        · rw [ite_eq_right h2]
          by_cases h3 : st.lens.length = size
          · rw [ite_eq_left h3, hrest_syms_full K g o size clc st bs h3 h2]
          · rw [ite_eq_right h3, hrest_syms_step K g o size clc st bs (by omega) h2]
  | .first i n tc cc => agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => by
      show oCount K g i n tc cc bs = _
      unfold oCount
      congr 1
      funext q
      rw [afterCat_eq] <;> rfl)
  | .np => agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => by
      rw [hrest_np]
      unfold readNp
      cases readInt 2 bs with
      | none => rfl
      | some p =>
        show (readInt 4 p.2 >>= _) = (readInt 4 p.2 >>= _) >>= _
        cases readInt 4 p.2 with
        | none => rfl
        | some q => rfl)
  | .modes done 0 => agreesW_ofH g (agrees_congr (agrees_next _) fun bs => hrest_modes_zero K g done bs)
  | .modes done (n + 1) => agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => hrest_modes_succ K g done n bs)
  | .trees isL => agreesW_congr (agreesW_readIn faith_readVarLen fun v =>
      agreesW_ite (agreesW_next _ (mapHook (g.setMap isL v (List.replicate (mapSize g isL) 0)) isL)) (agreesW_next0 _)) fun bs => by
      rw [hrest_trees]
      congr 1
      funext p
      rw [afterMap_eq, mapR_eq] <;> rfl
  | .rlemax _ _ => agreesW_ofH g (agrees_congr (agrees_readIn fun _ => agrees_next _) fun _ => rfl)
  | .vals isL ntrees rlemax code done left => by
    cases hr : runOf rlemax code with
    | some v =>
      exact agreesW_ofH g (agrees_kcongr (k := fun bs => if left = 0 then ORes.next (g, HPhase.imtf isL ntrees done) bs
          else ORes.next (g, HPhase.vals isL ntrees rlemax code (done ++ List.replicate left v) 0) bs)
        (fun bs => by simp only [hStepP, hStep, hr])
        (agrees_congr (agrees_ite (agrees_next _) (agrees_next _)) fun bs => by
          by_cases h0 : left = 0
          · subst h0
            rw [ite_eq_left rfl, hrest_vals_zero]
          · rw [ite_eq_right h0, hrest_vals_run K g isL ntrees rlemax code done left hr]))
    | none =>
      exact agreesW_ofH g (agrees_kcongr (k := fun bs => if left = 0 then ORes.next (g, HPhase.imtf isL ntrees done) bs
          else readIn 31 (mapSym rlemax code) bs fun v b =>
            if left < v.2 then .bad else .next (g, .vals isL ntrees rlemax code (done ++ List.replicate v.2 v.1) (left - v.2)) b)
        (fun bs => by simp only [hStepP, hStep, hr])
        (agrees_congr (agrees_ite (agrees_next _) (agrees_readIn fun _ => agrees_ite agrees_bad (agrees_next _)))
          fun bs => by
            by_cases h0 : left = 0
            · subst h0
              rw [ite_eq_left rfl, hrest_vals_zero]
            · rw [ite_eq_right h0, hrest_vals_step K g isL ntrees rlemax code done left bs h0]))
  | .imtf isL ntrees vals => agreesW_congr (agreesW_readIn (faith_readInt 1) fun im =>
      agreesW_ite (agreesW_next _ (mapHook (g.setMap isL ntrees (if im = 0 then vals else inverseMoveToFront vals)) isL))
        agreesW_bad) fun bs => by
      show afterVals K g isL ntrees vals bs = _
      unfold afterVals
      congr 1
      funext im
      rw [afterMap_eq, mapR_eq] <;> rfl
  | .codes k done (n + 1) => agreesW_ofH g (agrees_congr (agrees_next _) fun bs => hrest_codes_succ K k g done n bs)
  | .codes .L done 0 => agreesW_ofH g (agrees_congr (agrees_next _) fun bs => hrest_codes_L K g done bs)
  | .codes .I done 0 => agreesW_ofH g (agrees_congr (agrees_next _) fun bs => hrest_codes_I K g done bs)
  | .codes .D done 0 => agreesW_ofH g (agrees_congr (agrees_exit _) fun bs => hrest_codes_D K g done bs)

/-- Each step of a header read in order says what the spec says. -/
theorem hAgree (g : Gh) (p : HPhase) : Agrees (fun q bs => hrest K q.1 q.2 bs) K.k (hStepP (g, p)) (hrest K g p) := fun bs => by
  obtain ⟨h1, h2, h3, h4⟩ := hAgreeW K g p bs
  refine ⟨fun q c e => ?_, h2, h3, h4⟩
  obtain ⟨oc, u, hu, hk⟩ := h1 q c e
  subst hu
  rw [hk c e, Wr_id hw]

end

/-! ### The stream -/

private theorem skipK_succ {α : Type} (A : StreamState → List Bool → Option α) (st : StreamState) (n : Nat) (bs : List Bool) :
    skipK A st (n + 1) bs = readInt 8 bs >>= fun p => skipK A st n p.2 := by
  by_cases hl : 8 ≤ bs.length
  · obtain ⟨v, hv⟩ := readInt_of_le 8 bs hl
    rw [hv]
    show skipK A st (n + 1) bs = skipK A st n (bs.drop 8)
    have := skipK_drop A st (n := n + 1) (m := 1) (bs := bs) (by omega) (by omega)
    simpa using this
  · have hn : readInt 8 bs = none := by
      cases e : readInt 8 bs with
      | none => rfl
      | some p =>
        obtain ⟨v, r⟩ := p
        have := readInt_length 8 bs v r e
        omega
    rw [hn]
    show (if bs.length < (n + 1) * 8 then none else _) = none
    rw [ite_eq_left (by omega)]

/-- The fill bits leave whole bytes. -/
private theorem readFill_whole {bs b : List Bool} (h : readFill bs = some b) : b.length % 8 = 0 := by
  unfold readFill at h
  cases e : readInt (bs.length % 8) bs with
  | none => rw [e] at h; simp at h
  | some p =>
    obtain ⟨v, r⟩ := p
    rw [e] at h
    have hl := readInt_length _ bs v r e
    dsimp only [bind, Option.bind] at h
    by_cases hv : v = 0
    · rw [ite_eq_left hv] at h
      cases h
      omega
    · rw [ite_eq_right hv] at h
      cases h

/-- On whole bytes, the fill bits are none. -/
private theorem readFill_of_whole {bs : List Bool} (h : bs.length % 8 = 0) : readFill bs = some bs := by
  unfold readFill
  rw [h]
  rfl

private theorem srest_afterBlock (w : Nat) (last : Bool) (st : StreamState) (bs : List Bool) :
    srest specSem (afterBlock w last st) bs = amK w last st bs := by
  cases last <;> rfl

private theorem startAgree (w : Nat) (st : StreamState) :
    ∀ ms, Agrees (srest specSem) (fun y _ => some y) (startPlace w st ms) (afterStart w (amK w) st ms)
  | .lastEmpty => agrees_congr (agrees_next (SPhase.ended st)) fun _ => rfl
  | .metadata last skip => agrees_fill (.skip w st last skip) (fun _ => rfl) (fun _ => rfl)
  | .data last mlen _ =>
    agrees_congr (agrees_ite (agrees_fill (.raw w st last mlen) (fun _ => rfl) (fun _ => rfl))
      (agrees_congr (agrees_next (SPhase.hdr (blockWindow w st last mlen) st last mlen Gh.start (.cat .L))) fun bs =>
        (readCompressed_eq w (amK w last) st mlen Gh.start bs).trans
          (srest_blockWindow specSem w st last mlen Gh.start (.cat .L) bs))) fun _ => rfl

/-- Each step of the stream read in order says what the spec says. -/
theorem sAgree : ∀ p, Agrees (srest specSem) (fun y _ => some y) (sStep p) (srest specSem p)
  | .wbits => agrees_congr (agrees_readIn fun _ => agrees_next _) fun _ => rfl
  | .mblock w st => agrees_congr (agrees_readIn (startAgree w st)) fun bs => metaK_start w st bs
  | .skip w st last 0 => agrees_congr (agrees_next _) fun bs => by
      rw [srest_afterBlock]
      show (if bs.length < 0 * 8 then none else amK w last st (bs.drop (0 * 8))) = _
      simp
  | .skip w st last (n + 1) => agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => skipK_succ _ st n bs
  | .raw w st last 0 => agrees_congr (agrees_next _) fun bs => by
      rw [srest_afterBlock]
      rfl
  | .raw w st last (n + 1) => agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => rawK_succ _ st n bs
  | .hdr w st last mlen g p => fun bs => by
    obtain ⟨hn, hx, hb, hs⟩ := hAgree (hdrK w (amK w last) st mlen) (fun _ _ => rfl) g p bs
    cases e : hStepP (g, p) bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by
        simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hn q' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hx m' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hb e), (fun h => by cases h)⟩
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => hs e)⟩
  | .cmds w last m p => fun bs => by
    obtain ⟨hn, hx, hb, hs⟩ := cAgree w m (amK w last) p bs
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hn p' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | exit s b =>
      have hf := hx s b e
      unfold finishC at hf
      by_cases hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance) = true
      · have h' : sStep (.cmds w last m p) bs = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b := by
          simp only [sStep, e, hc, ↓reduceIte]
        rw [ite_eq_left hc] at hf
        rw [h']
        refine ⟨(fun _ _ h => ?_), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
        cases h
        rw [srest_afterBlock]
        exact hf
      · have h' : sStep (.cmds w last m p) bs = .bad := by
          simp only [sStep, e]
          exact ite_eq_right hc
        rw [ite_eq_right hc] at hf
        rw [h']
        exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hf), (fun h => by cases h)⟩
    | bad =>
      have h' : sStep (.cmds w last m p) bs = .bad := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hb e), (fun h => by cases h)⟩
    | short =>
      have h' : sStep (.cmds w last m p) bs = .short := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => hs e)⟩
  | .ended st => fun bs => by
    show (∀ q c, sStep (.ended st) bs = .next q c → endOf st bs = srest specSem q c) ∧ _
    by_cases hm : bs.length % 8 = 0
    · have h' : sStep (.ended st) bs = if bs.isEmpty then .exit (st.output.reverse.map Nat.toUInt8) bs else .bad := by
        simp only [sStep, hm, ↓reduceIte]
      have hf := readFill_of_whole hm
      rw [h']
      cases hb : bs.isEmpty with
      | true =>
        have e0 : bs = [] := List.isEmpty_iff.mp hb
        subst e0
        exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h; rfl), (fun h => by cases h), (fun h => by cases h)⟩
      | false =>
        refine ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => ?_), (fun h => by cases h)⟩
        show (readEnd bs >>= _) = none
        unfold readEnd
        rw [hf]
        show ((if bs.isEmpty = true then some () else none) >>= _) = none
        rw [hb]
        rfl
    · cases e : readFill bs with
      | none =>
        have h' : sStep (.ended st) bs = .bad := by simp only [sStep, hm, ↓reduceIte, e]
        rw [h']
        refine ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => ?_), (fun h => by cases h)⟩
        show (readEnd bs >>= _) = none
        unfold readEnd
        rw [e]
        rfl
      | some b =>
        have h' : sStep (.ended st) bs = .next (.ended st) b := by simp only [sStep, hm, ↓reduceIte, e]
        rw [h']
        refine ⟨(fun _ _ h => ?_), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
        cases h
        show (readEnd bs >>= _) = (readEnd b >>= _)
        unfold readEnd
        rw [e, readFill_of_whole (readFill_whole e)]

/-! ### Any worth along the reading in order

A step of the reading in order that goes on keeps what a place is worth on leaving it, for any worth whose value at the
stream's end ignores the fill bits. A worth that isn't the output can drop at a meta-block's start, where leaving is worth
less than arriving: the demand counts the header's tables only on arriving. -/

section
variable {α : Type} (S : Sem α)

private theorem srest_afterBlockS (w : Nat) (last : Bool) (st : StreamState) (bs : List Bool) :
    srest S (afterBlock w last st) bs = S.after w last st bs := by
  cases last
  · exact (S.after_false w st bs).symm
  · exact (S.after_true w st bs).symm

private theorem startAgreeS (w : Nat) (st : StreamState) :
    ∀ ms, Agrees (srest S) (fun _ _ => none) (startPlace w st ms) (afterStart w (S.after w) st ms)
  | .lastEmpty => agrees_congr (agrees_next (SPhase.ended st)) fun bs => S.after_true w st bs
  | .metadata last skip => agrees_fill (.skip w st last skip) (fun _ => rfl) (fun _ => rfl)
  | .data last mlen _ =>
    agrees_congr (agrees_ite (agrees_fill (.raw w st last mlen) (fun _ => rfl) (fun _ => rfl))
      (agrees_congr (agrees_next (SPhase.hdr (blockWindow w st last mlen) st last mlen Gh.start (.cat .L))) fun bs =>
        (readCompressed_eq w (S.after w last) st mlen Gh.start bs).trans
          (srest_blockWindow S w st last mlen Gh.start (.cat .L) bs))) fun _ => rfl

/-- Each step of the reading in order away from the stream's end says what leaving its place is worth. -/
theorem sAgreeS : ∀ p, (∀ st, p ≠ .ended st) → Agrees (srest S) (fun _ _ => none) (sStep p) (sLeave S p)
  | .wbits, _ => agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => S.first_eq bs
  | .mblock w st, _ => agrees_readIn (startAgreeS S w st)
  | .skip w st last 0, _ => agrees_congr (agrees_next _) fun bs => by
      show skipK (S.after w last) st 0 bs = srest S (afterBlock w last st) bs
      rw [srest_afterBlockS]
      show (if bs.length < 0 * 8 then none else S.after w last st (bs.drop (0 * 8))) = _
      simp
  | .skip w st last (n + 1), _ => agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => skipK_succ _ st n bs
  | .raw w st last 0, _ => agrees_congr (agrees_next _) fun bs => by
      show rawK (S.after w last) st 0 bs = srest S (afterBlock w last st) bs
      rw [srest_afterBlockS]
      rfl
  | .raw w st last (n + 1), _ => agrees_congr (agrees_readIn fun _ => agrees_next _) fun bs => rawK_succ _ st n bs
  | .hdr w st last mlen g p, _ => fun bs => by
    obtain ⟨hn, hx, hb, hs⟩ := hAgree (hdrK w (S.after w last) st mlen) (fun _ _ => rfl) g p bs
    cases e : hStepP (g, p) bs with
    | next q' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.hdr w st last mlen q'.1 q'.2) b := by
        simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hn q' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | exit m' b =>
      have h' : sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m' (.command (startState st mlen m'))) b := by
        simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hx m' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | bad =>
      have h' : sStep (.hdr w st last mlen g p) bs = .bad := by simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hb e), (fun h => by cases h)⟩
    | short =>
      have h' : sStep (.hdr w st last mlen g p) bs = .short := by simp only [sStep, show hStep g p bs = _ from e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => hs e)⟩
  | .cmds w last m p, _ => fun bs => by
    obtain ⟨hn, hx, hb, hs⟩ := cAgree w m (S.after w last) p bs
    cases e : cStep w m p bs with
    | next p' b =>
      have h' : sStep (.cmds w last m p) bs = .next (.cmds w last m p') b := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h; exact hn p' b e), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
    | exit s b =>
      have hf := hx s b e
      unfold finishC at hf
      by_cases hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy &&
          usesEveryType m.distance s.distance) = true
      · have h' : sStep (.cmds w last m p) bs = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b := by
          simp only [sStep, e, hc, ↓reduceIte]
        rw [ite_eq_left hc] at hf
        rw [h']
        refine ⟨(fun _ _ h => ?_), (fun _ _ h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩
        cases h
        rw [srest_afterBlockS]
        exact hf
      · have h' : sStep (.cmds w last m p) bs = .bad := by
          simp only [sStep, e]
          exact ite_eq_right hc
        rw [ite_eq_right hc] at hf
        rw [h']
        exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hf), (fun h => by cases h)⟩
    | bad =>
      have h' : sStep (.cmds w last m p) bs = .bad := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ => hb e), (fun h => by cases h)⟩
    | short =>
      have h' : sStep (.cmds w last m p) bs = .short := by simp only [sStep, e]
      rw [h']
      exact ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun h => by cases h), (fun _ => hs e)⟩
  | .ended st, h => absurd rfl (h st)

/-- A worth whose value at the stream's end ignores the fill bits. -/
def FillFree : Prop := ∀ st bs b, readFill bs = some b → S.finish st bs = S.finish st b

/-- A step of the reading in order that goes on goes from what leaving its place is worth to what arriving at the next is. -/
theorem sNext (hf : FillFree S) {p q : SPhase} {bs c : List Bool} (h : sStep p bs = .next q c) : sLeave S p bs = srest S q c := by
  cases p
  case ended st =>
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
        exact hf st bs _ e
  all_goals exact ((sAgreeS S _ (fun _ e => SPhase.noConfusion e)) bs).1 q c h

end

/-- What the demand counts ignores the fill bits at the stream's end. -/
theorem demand_fillFree : FillFree demandSem := fun _ _ _ _ => rfl

/-- The demand of what the reading in order has still to read never grows as it goes on. -/
theorem demand_reach {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) :
    (srest demandSem q c).getD 0 ≤ (srest demandSem p bs).getD 0 := by
  induction h with
  | refl => exact Nat.le_refl _
  | @next p0 b0 p1 b1 _ _ hs _ ih =>
    refine Nat.le_trans ih ?_
    rw [← sNext demandSem demand_fillFree hs]
    cases p0 with
    | mblock w st => exact leave_le w st b0
    | _ => exact Nat.le_refl _

/-! ### What the reading in order says about `decode` -/

/-- The reading in order keeps what the spec still has to do. -/
theorem reach_srest {p q : SPhase} {bs c : List Bool} (h : Reach sStep p bs q c) : srest specSem p bs = srest specSem q c := by
  induction h with
  | refl => rfl
  | next hs _ ih => exact ((sAgree _ _).1 _ _ hs).trans ih

/-- The reading in order of a stream's bytes reaches only places worth what `decode` gives for them. -/
theorem decode_reach {x : List UInt8} {q : SPhase} {c : List Bool} (h : Reach sStep .wbits (bits x) q c) :
    decode x = srest specSem q c := by
  rw [decode_srest]
  exact reach_srest h

/-- The reading in order's end is `decode`'s output. -/
theorem decode_of_exit {x : List UInt8} {q : SPhase} {c c' : List Bool} {y : List UInt8} (h : Reach sStep .wbits (bits x) q c)
    (he : sStep q c = .exit y c') : decode x = some y :=
  (decode_reach h).trans ((sAgree q c).2.1 y c' he)

/-- Where the reading in order rejects, `decode` rejects. -/
theorem decode_of_bad {x : List UInt8} {q : SPhase} {c : List Bool} (h : Reach sStep .wbits (bits x) q c)
    (hb : sStep q c = .bad) : decode x = none :=
  (decode_reach h).trans ((sAgree q c).2.2.1 hb)

/-- Where the reading in order has too few bits, `decode` rejects the bytes at hand. -/
theorem decode_of_short {x : List UInt8} {q : SPhase} {c : List Bool} (h : Reach sStep .wbits (bits x) q c)
    (hs : sStep q c = .short) : decode x = none :=
  (decode_reach h).trans ((sAgree q c).2.2.2 hs)

/-- The reading in order reaches, with whole bytes after its bits, what it reaches without them. -/
theorem reach_extend {P E : Type} {step : P → List Bool → ORes P E} (hs : ∀ p, NFaith (step p)) {p q : P} {A B : List Bool}
    (h : Reach step p A q B) {F : List Bool} (hF : F.length % 8 = 0) : Reach step p (A ++ F) q (B ++ F) := by
  induction h with
  | refl => exact .refl _ _
  | @next p A p' A' q B hst _ ih =>
    obtain ⟨u, hu, hk⟩ := hs p A p' A' hst
    refine .next ?_ ih
    rw [hu, List.append_assoc]
    exact hk (A' ++ F) (by simp only [List.length_append]; omega)

/-! ### Too few bits, within one read -/

section
variable {A P E : Type}

/-- A step that never has too few bits. -/
def NoShort (k : List Bool → ORes P E) : Prop := ∀ bs, k bs ≠ .short

/-- A step that has too few bits only on fewer than `n` bits. -/
def KShort (n : Nat) (k : List Bool → ORes P E) : Prop := ∀ bs, k bs = .short → bs.length < n

theorem noShort_next (q : P) : NoShort fun bs => (.next q bs : ORes P E) := fun _ h => by cases h

theorem noShort_exit (e : E) : NoShort fun bs => (.exit e bs : ORes P E) := fun _ h => by cases h

theorem noShort_bad : NoShort fun _ => (.bad : ORes P E) := fun _ h => by cases h

theorem noShort_ite {c : Prop} [Decidable c] {f g : List Bool → ORes P E} (hf : NoShort f) (hg : NoShort g) :
    NoShort fun bs => if c then f bs else g bs := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf
  · simpa only [h, ↓reduceIte] using hg

theorem noShort_lookIn {o : Option A} {k : A → List Bool → ORes P E} (h : ∀ a, NoShort (k a)) :
    NoShort fun bs => lookIn o fun a => k a bs := by
  cases o with
  | none => exact noShort_bad
  | some a => exact h a

theorem kshort_of {n : Nat} {k : List Bool → ORes P E} (h : NoShort k) : KShort n k := fun bs e => absurd e (h bs)

theorem kshort_ite {n : Nat} {c : Prop} [Decidable c] {f g : List Bool → ORes P E} (hf : KShort n f) (hg : KShort n g) :
    KShort n fun bs => if c then f bs else g bs := by
  by_cases h : c
  · simpa only [h, ↓reduceIte] using hf
  · simpa only [h, ↓reduceIte] using hg

theorem kshort_lookIn {n : Nat} {o : Option A} {k : A → List Bool → ORes P E} (h : ∀ a, KShort n (k a)) :
    KShort n fun bs => lookIn o fun a => k a bs := by
  cases o with
  | none => exact kshort_of noShort_bad
  | some a => exact h a

theorem kshort_readIn {n room : Nat} {rd : List Bool → Option (A × List Bool)} {k : A → List Bool → ORes P E} (h1 : room ≤ n)
    (hk : ∀ a, NoShort (k a)) : KShort n fun bs => readIn room rd bs k := by
  intro bs h
  have h' : readIn room rd bs k = .short := h
  cases e : rd bs with
  | none =>
    unfold readIn at h'
    rw [e] at h'
    by_cases hl : bs.length < room
    · omega
    · rw [ite_eq_right hl] at h'
      cases h'
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [readIn_some e] at h'
    exact absurd h' (hk a b)

/-- Two bits, then a step that has too few bits only on fewer than `m`. -/
theorem kshort_readInt2 {n m : Nat} {k : Nat → List Bool → ORes P E} (hk : ∀ a, KShort m (k a)) (h2 : 2 + m ≤ n) :
    KShort n fun bs => readIn 2 (readInt 2) bs k := by
  intro bs h
  have h' : readIn 2 (readInt 2) bs k = .short := h
  cases e : readInt 2 bs with
  | none =>
    unfold readIn at h'
    rw [e] at h'
    by_cases hl : bs.length < 2
    · omega
    · rw [ite_eq_right hl] at h'
      cases h'
  | some p =>
    obtain ⟨a, b⟩ := p
    rw [readIn_some e] at h'
    have := hk a b h'
    have := readInt_length 2 bs a b e
    omega

theorem kshort_nextIn {c : BlockCategory} {st : BlockState} {k : BlockState → List Bool → ORes P E} (hk : ∀ a, NoShort (k a)) :
    KShort 54 fun bs => nextIn c st bs k := by
  show KShort 54 fun bs => if st.count = 0 ∧ c.n < 2 then .bad else readIn 54 (nextElement c st) bs k
  exact kshort_ite (kshort_of noShort_bad) (kshort_readIn (Nat.le_refl _) hk)

end

theorem kshort_cStep (w : Nat) (m : MetaBlockHeader) : ∀ p, KShort 54 (cStep w m p)
  | .command s => kshort_ite (kshort_of (noShort_exit s)) (kshort_nextIn fun _ => noShort_next _)
  | .insertCopy _ _ => kshort_lookIn fun _ => kshort_readIn (by omega) fun _ => noShort_next _
  | .copyLength _ _ _ _ _ _ => kshort_ite (kshort_of noShort_bad) (kshort_readIn (by omega) fun _ => noShort_next _)
  | .literals _ _ _ _ _ 0 _ _ => kshort_of (noShort_next _)
  | .literals _ _ _ _ _ (_ + 1) _ _ => kshort_ite (kshort_nextIn fun _ => noShort_next _) (kshort_of (noShort_next _))
  | .literalSymbol _ _ _ _ _ _ _ _ =>
    kshort_lookIn fun _ => kshort_lookIn fun _ => kshort_lookIn fun _ => kshort_readIn (by omega) fun _ => noShort_next _
  | .distance _ _ _ =>
    kshort_ite (kshort_of (noShort_next _))
      (kshort_ite (kshort_of (noShort_lookIn fun _ => noShort_lookIn fun q => noShort_next q)) (kshort_nextIn fun _ => noShort_next _))
  | .distanceSymbol _ _ _ =>
    kshort_lookIn fun _ => kshort_lookIn fun _ => kshort_readIn (by omega) fun _ =>
      noShort_lookIn fun _ => noShort_lookIn fun q => noShort_next q
  | .copy _ _ 0 => kshort_of (noShort_next _)
  | .copy _ _ (_ + 1) => kshort_of (noShort_next _)
  | .word _ [] => kshort_of (noShort_next _)
  | .word _ (_ :: _) => kshort_of (noShort_next _)

theorem kshort_hStep (g : Gh) : ∀ p, KShort 54 (hStepP (g, p))
  | .cat _ => kshort_readIn (by omega) fun _ => noShort_ite (noShort_next _) (noShort_next _)
  | .code _ _ =>
    kshort_readInt2 (m := 43) (fun _ => kshort_ite (kshort_readIn (Nat.le_refl _) fun _ => noShort_next _) (kshort_of (noShort_next _)))
      (by omega)
  | .clens _ _ [] _ _ => kshort_of (noShort_ite (noShort_next _) noShort_bad)
  | .clens _ _ (_ :: _) _ _ =>
    kshort_readIn (by omega) fun _ => noShort_ite (noShort_next _) (noShort_ite (noShort_next _) (noShort_ite noShort_bad (noShort_next _)))
  | .syms _ _ _ _ =>
    kshort_ite (kshort_of noShort_bad) (kshort_ite (kshort_of (noShort_next _)) (kshort_ite (kshort_of noShort_bad)
      (kshort_readIn (by omega) fun _ => noShort_ite noShort_bad (noShort_ite noShort_bad (noShort_next _)))))
  | .first _ _ _ _ => kshort_readIn (by omega) fun _ => noShort_next _
  | .np => kshort_readIn (by omega) fun _ => noShort_next _
  | .modes _ 0 => kshort_of (noShort_next _)
  | .modes _ (_ + 1) => kshort_readIn (by omega) fun _ => noShort_next _
  | .trees _ => kshort_readIn (by omega) fun _ => noShort_ite (noShort_next _) (noShort_next _)
  | .rlemax _ _ => kshort_readIn (by omega) fun _ => noShort_next _
  | .vals _ _ rlemax code _ _ => kshort_ite (kshort_of (noShort_next _)) (by
      cases runOf rlemax code with
      | some _ => exact kshort_of (noShort_next _)
      | none => exact kshort_readIn (by omega) fun _ => noShort_ite noShort_bad (noShort_next _))
  | .imtf _ _ _ => kshort_readIn (by omega) fun _ => noShort_ite (noShort_next _) noShort_bad
  | .codes _ _ (_ + 1) => kshort_of (noShort_next _)
  | .codes .L _ 0 => kshort_of (noShort_next _)
  | .codes .I _ 0 => kshort_of (noShort_next _)
  | .codes .D _ 0 => kshort_of (noShort_exit _)

private theorem noShort_fill {P E : Type} {k : List Bool → ORes P E} (q : P)
    (hk : ∀ bs, k bs = match readFill bs with | some b => .next q b | none => .bad) : NoShort k := by
  intro bs h
  rw [hk] at h
  revert h
  cases readFill bs <;> intro h <;> cases h

private theorem noShort_startPlace (w : Nat) (st : StreamState) : ∀ ms, NoShort (startPlace w st ms)
  | .lastEmpty => noShort_next _
  | .metadata last skip => noShort_fill (SPhase.skip w st last skip) fun _ => rfl
  | .data last mlen _ => noShort_ite (noShort_fill (SPhase.raw w st last mlen) fun _ => rfl) (noShort_next _)

/-- The stream read in order has too few bits only within one read, on fewer than 54 bits. -/
theorem kshort_sStep : ∀ p, KShort 54 (sStep p)
  | .wbits => kshort_readIn (by omega) fun _ => noShort_next _
  | .mblock w st => kshort_readIn (by omega) (noShort_startPlace w st)
  | .skip _ _ _ 0 => kshort_of (noShort_next _)
  | .skip _ _ _ (_ + 1) => kshort_readIn (by omega) fun _ => noShort_next _
  | .raw _ _ _ 0 => kshort_of (noShort_next _)
  | .raw _ _ _ (_ + 1) => kshort_readIn (by omega) fun _ => noShort_next _
  | .hdr w st last mlen g p => fun bs h => by
    cases e : hStepP (g, p) bs with
    | short => exact kshort_hStep g p bs e
    | next q' b => simp only [sStep, show hStep g p bs = _ from e] at h; cases h
    | exit m' b => simp only [sStep, show hStep g p bs = _ from e] at h; cases h
    | bad => simp only [sStep, show hStep g p bs = _ from e] at h; cases h
  | .cmds w last m p => fun bs h => by
    cases e : cStep w m p bs with
    | short => exact kshort_cStep w m p bs e
    | next p' b => simp only [sStep, e] at h; cases h
    | exit s b =>
      simp only [sStep, e] at h
      split at h <;> cases h
    | bad => simp only [sStep, e] at h; cases h
  | .ended st => fun bs h => by
    by_cases hm : bs.length % 8 = 0
    · simp only [sStep, hm, ↓reduceIte] at h
      split at h <;> cases h
    · cases e : readFill bs with
      | none => simp only [sStep, hm, ↓reduceIte, e] at h; cases h
      | some b => simp only [sStep, hm, ↓reduceIte, e] at h; cases h

/-! ### The decoder, paused for input -/

/-- A decoder that needs input stands at the place the spec's reading in order of exactly the bytes it has used reaches,
holding the bits that reading has left. Whatever bytes follow, `decode` of them after the bytes used is the spec's remaining
work from that place. Every byte the reading in order has produced has been handed out. From that place the reading in
order, producing nothing more, comes to a read with fewer than 54 of its bits at hand, or to the stream's valid end. -/
theorem decoder_pausesInOrder {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R)
    (hs : R.status = .needsInput) :
    ∃ p, Reach sStep .wbits (bits (x.take R.read)) p R.state.val.held ∧ p.out.reverse.map Nat.toUInt8 = R.emitted ∧
      (∀ t : List UInt8, decode (x.take R.read ++ t) = srest specSem p (R.state.val.held ++ bits t)) ∧
      ∃ q c, Reach sStep p R.state.val.held q c ∧ q.out = p.out ∧
        ((sStep q c = .short ∧ c.length < 54) ∨ ∃ y, sStep q c = .exit y [] ∧ decode (x.take R.read) = some y) := by
  obtain ⟨p, h1, ⟨q, c, h2, h3, h4⟩, h5⟩ := decoder_inOrder h hs
  refine ⟨p, h1, h5, fun t => ?_, q, c, h2, h3, ?_⟩
  · rw [decode_srest, bits_append]
    exact reach_srest (reach_extend nfaith_sStep h1 (by rw [bits_length]; omega))
  · rcases h4 with h4 | ⟨y, h4⟩
    · exact Or.inl ⟨h4, kshort_sStep q c h4⟩
    · exact Or.inr ⟨y, h4, decode_of_exit (h1.trans h2) h4⟩

/-! ### The decoder, rejecting -/

/-- The bytes between two places in a call's chunk. -/
theorem chunk_between {x : List UInt8} {R : Run DState} {c : Call} (h : R.read + c.size ≤ x.length) {i j : Nat} (hij : i ≤ j)
    (hj : j ≤ c.size) :
    chunk (R.input x c) (c.pre.length + i) (c.pre.length + j) = ((x.drop R.read).take j).drop i := by
  have e1 := chunk_input (R := R) (c := c) h (show i ≤ c.size by omega)
  have e2 : chunk (R.input x c) (c.pre.length + i) (c.pre.length + j) =
      (chunk (R.input x c) (c.pre.length + i) (c.pre.length + c.size)).take (j - i) := by
    unfold chunk
    rw [List.take_take]
    congr 1
    omega
  rw [e2, e1]
  simp only [List.drop_take, List.take_take]
  congr 1
  omega

/-- A stream's first bytes, cut at a place within a run of bytes taken from a place further back. -/
private theorem take_cut (x : List UInt8) (r : Nat) {k s : Nat} (hk : k ≤ s) :
    x.take (r + s) = x.take (r + k) ++ ((x.drop r).take s).drop k := by
  rw [List.take_add, List.take_add, List.append_assoc]
  congr 1
  conv => lhs; rw [← List.take_append_drop k ((x.drop r).take s)]
  rw [List.take_take, Nat.min_eq_left hk]

/-- A rejection tells the truth about the input it used. Either the end was signalled with the whole stream used, or every
continuation of the bytes used is invalid and the spec's reading in order of some of those bytes got through all but at
most 64 bits of them without rejecting, so that the bytes used run at most 64 bits past where the reading in order is. -/
theorem decoder_rejectsAt {limit : Nat} {x : List UInt8} {R : Run DState} (h : Reaches decoder limit x R) (hs : R.status = .rejected) :
    (R.ended = true ∧ R.read = x.length) ∨
    ((∀ t : List UInt8, decode (x.take R.read ++ t) = none) ∧
      ∃ (n : Nat) (q : SPhase) (cb : List Bool), n ≤ R.read ∧ Reach sStep .wbits (bits (x.take n)) q cb ∧
        8 * R.read + cb.length ≤ 8 * n + 64) := by
  cases h with
  | start =>
    exfalso
    change (decStart limit).2 = .rejected at hs
    unfold decStart at hs
    split at hs <;> simp at hs
  | @call R0 c hR ha =>
    have hin := ha.inside
    have hfit := ha.fits
    obtain ⟨p, hrel, hE, hro, hreach, _⟩ := (order_inv hR).running ha.running
    obtain ⟨o, _, e2, _, e4, hok⟩ := reply_ok ha hrel hE
    have hdec := hok.decided
    have hst : o.status = .rejected := by rw [← e4]; exact hs
    have hstop : (USize.ofNat (c.pre.length + c.size)).toNat = c.pre.length + c.size := usize_of (by omega)
    have hpos0 : (atPos R0.state.val c.pre.length).pos.toNat = c.pre.length := usize_of (by omega)
    have hread : (R0.after decoder x c).read = R0.read + (o.pos.toNat - c.pre.length) := by
      show R0.read + (R0.reply decoder x c).used = _
      rw [e2]
    rcases hdec hst with ⟨hf, hq⟩ | ⟨p1, h1, pos1, d1, d2, d3, d4, d5, d6⟩
    · left
      refine ⟨by simp [Run.after, hf], ?_⟩
      rw [hread, hq, hstop]
      have := ha.whole hf
      omega
    · right
      rw [hpos0] at d1
      rw [hstop] at d3
      generalize hk1 : pos1.toNat - c.pre.length = k1
      generalize hkq : o.pos.toNat - c.pre.length = kq at hread
      have hp1 : pos1.toNat = c.pre.length + k1 := by omega
      have hpq : o.pos.toNat = c.pre.length + kq := by omega
      have hk1q : k1 ≤ kq := by omega
      have hkqs : kq ≤ c.size := by omega
      rw [hread]
      -- The reading in order up to where the call starts, then any bytes.
      have hstart : ∀ v : List UInt8, Reach sStep .wbits (bits (x.take R0.read ++ v)) p (R0.state.val.held ++ bits v) := by
        intro v
        rw [bits_append]
        exact reach_extend nfaith_sStep (reach_used hro hreach) (by rw [bits_length]; omega)
      -- Then through the call's chunk to where the rejecting step began.
      have hglob : ∀ t : List UInt8, Reach sStep .wbits (bits (x.take (R0.read + c.size) ++ t)) p1
          (h1 ++ bits (((x.drop R0.read).take c.size).drop k1 ++ t)) := by
        intro t
        have hj := d5 t
        dsimp only at hj
        rw [bits_at' hin (atPos R0.state.val c.pre.length) (hpos0.trans (Nat.add_zero _).symm) (Nat.zero_le _) hstop t] at hj
        unfold chunkBits at hj
        rw [hp1, hstop, chunk_input hin (show k1 ≤ c.size by omega), ← bits_append, List.drop_zero] at hj
        have e0 : (atPos R0.state.val c.pre.length).held = R0.state.val.held := rfl
        rw [e0] at hj
        rw [List.take_add, List.append_assoc]
        exact (hstart _).trans hj
      have htight : Reach sStep .wbits (bits (x.take (R0.read + k1))) p1 h1 := by
        have g := hglob []
        simp only [List.append_nil] at g
        rw [take_cut x R0.read (show k1 ≤ c.size by omega), bits_append] at g
        exact reach_restrict nfaith_sStep g _ _ _ rfl rfl (by rw [bits_length]; omega)
      refine ⟨fun t => ?_, R0.read + k1, p1, h1, by omega, htight, by omega⟩
      have g := reach_extend nfaith_sStep htight (F := bits (((x.drop R0.read).take kq).drop k1 ++ t)) (by rw [bits_length]; omega)
      rw [← bits_append, ← List.append_assoc, ← take_cut x R0.read hk1q] at g
      rw [decode_reach g]
      have hl := d6 t
      dsimp only at hl
      unfold chunkBits at hl
      rw [hp1, hpq, chunk_between hin hk1q hkqs, ← bits_append] at hl
      exact hl

end Brotli.Decoder
