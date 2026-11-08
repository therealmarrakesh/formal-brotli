module

public import Brotli.Decoder.StreamRest
public import Brotli.Decoder.Order
public import Brotli.Decoder.StepRead

@[expose] public section

/-!
# A step of the commands read in order says what the spec says

`Agrees` and its combinators tie a step of the reading in order to the spec's remaining work from where it is. For the
commands: `cAgree`, with the continuation the stream gives a meta-block's commands, and `cAgreeK`, with any continuation,
for the steps other than a command's start. So a step inside a command that goes on keeps `rest` (`cStep_rest`).
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

/-- Each step of the commands read in order other than a command's start says what the spec says, whatever follows the
commands. -/
theorem cAgreeK (w : Nat) (m : MetaBlockHeader) (K : CommandState → List Bool → Option α)
    (X : CommandState → List Bool → Option α) : ∀ p, (∀ s, p ≠ .command s) → Agrees (rest w m K) X (cStep w m p) (rest w m K p)
  | .command s, h => absurd rfl (h s)
  | .insertCopy s ic, _ => agrees_congr (agrees_lookIn fun _ => agrees_readIn fun _ => agrees_next _) fun bs =>
      rest_insertCopy_half w m _ s ic bs
  | .copyLength s ic c ilen copyBits copyBase, _ =>
    agrees_congr (agrees_ite agrees_bad (agrees_readIn fun _ => agrees_next _)) fun bs =>
      rest_copyLength_check w m _ s ic c ilen copyBits copyBase bs
  | .literals _ _ _ _ _ 0 _ _, _ => agrees_next _
  | .literals s ic c ilen clen (n + 1) lit out, _ =>
    agrees_congr (agrees_ite (agrees_nextIn fun _ => agrees_next _) (agrees_next _)) fun bs =>
      rest_literals_succ w m _ s ic c ilen clen n lit out bs
  | .literalSymbol _ _ _ _ _ _ _ _, _ =>
    agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_readIn fun _ => agrees_next _
  | .distance s c clen, _ =>
    agrees_congr (agrees_ite (agrees_next _) (agrees_ite (agrees_lookIn fun _ => agrees_lookIn fun q => agrees_next q)
      (agrees_nextIn fun _ => agrees_next _))) fun bs => rest_distance_parts w m _ s c clen bs
  | .distanceSymbol s clen dist, _ =>
    agrees_congr (agrees_lookIn fun _ => agrees_lookIn fun _ => agrees_readIn fun _ =>
      agrees_lookIn fun _ => agrees_lookIn fun q => agrees_next q) fun bs => rest_distanceSymbol_parts w m _ s clen dist bs
  | .copy _ _ 0, _ => agrees_next _
  | .copy _ _ (_ + 1), _ => agrees_next _
  | .word _ [], _ => agrees_congr (agrees_next _) fun bs => rest_word_end w m _ _ bs
  | .word _ (_ :: _), _ => agrees_congr (agrees_next _) fun bs => rest_word w m _ _ _ _ bs

/-- A step inside a command that goes on keeps what the spec still has to do, whatever follows the commands. -/
theorem cStep_rest {w : Nat} {m : MetaBlockHeader} (K : CommandState → List Bool → Option α) {p q : Phase}
    {bs c : List Bool} (hp : ∀ s, p ≠ .command s) (h : cStep w m p bs = .next q c) : rest w m K p bs = rest w m K q c :=
  (cAgreeK w m K (fun _ _ => none) p hp bs).1 q c h

end

end Brotli.Decoder
