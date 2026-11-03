import Brotli.Decoder.StreamRest
import Brotli.Decoder.HeaderOrder

/-!
# The stream's places, and the stream read in order

The places a stream can pause, and the spec's reading of a whole stream in order from each: WBITS, a meta-block's start,
a byte of metadata or of uncompressed data, a header's or the commands' own step, and the end.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The places a stream can pause. -/
inductive SPhase where
  | wbits
  | mblock (w : Nat) (st : StreamState)
  | skip (w : Nat) (st : StreamState) (last : Bool) (n : Nat)
  | raw (w : Nat) (st : StreamState) (last : Bool) (n : Nat)
  | hdr (w : Nat) (st : StreamState) (last : Bool) (mlen : Nat) (g : Gh) (p : HPhase)
  | cmds (w : Nat) (last : Bool) (m : MetaBlockHeader) (p : Phase)
  | ended (st : StreamState)

/-- The bytes a place has produced so far, most recent first. -/
def SPhase.out : SPhase → List Nat
  | .wbits => []
  | .mblock _ st => st.output
  | .skip _ st _ _ => st.output
  | .raw _ st _ _ => st.output
  | .hdr _ st _ _ _ _ => st.output
  | .cmds _ _ _ p => p.out
  | .ended st => st.output

/-- The ghost record a header starts from. -/
def Gh.start : Gh :=
  ⟨⟨⟨0, .single 0, .single 0, 0⟩, ⟨0, .single 0, .single 0, 0⟩, ⟨0, .single 0, .single 0, 0⟩, 0, 0, [], [], [], [], [], []⟩, 0, 0⟩

/-- The place after a meta-block, by whether it was the last. -/
def afterBlock (w : Nat) (last : Bool) (st : StreamState) : SPhase := if last then .ended st else .mblock w st

/-- The place a meta-block's start leads to, with the fill bits read before metadata and uncompressed bytes. -/
def startPlace (w : Nat) (st : StreamState) (ms : MetaStart) (bs : List Bool) : ORes SPhase (List UInt8) :=
  match ms with
  | .lastEmpty => .next (.ended st) bs
  | .metadata last skip =>
    match readFill bs with
    | some b => .next (.skip w st last skip) b
    | none => .bad
  | .data last mlen unc =>
    if unc then
      match readFill bs with
      | some b => .next (.raw w st last mlen) b
      | none => .bad
    else .next (.hdr w st last mlen Gh.start (.cat .L)) bs

/-- A step of the stream read in order, from each place: WBITS, a meta-block's start, a byte of metadata or of
uncompressed data, a header's or the commands' own step, and the end, which is the fill bits, then nothing. The
commands' end checks that every block type occurred. A meta-block's start is at most 31 bits. -/
def sStep : SPhase → List Bool → ORes SPhase (List UInt8)
  | .wbits, bs => readIn 7 readWBITS bs fun v b => .next (.mblock (windowSize v) ⟨[], 0, initialDistances⟩) b
  | .mblock w st, bs => readIn 31 metaStart bs fun ms b => startPlace w st ms b
  | .skip w st last 0, bs => .next (afterBlock w last st) bs
  | .skip w st last (n + 1), bs => readIn 8 (readInt 8) bs fun _ b => .next (.skip w st last n) b
  | .raw w st last 0, bs => .next (afterBlock w last st) bs
  | .raw w st last (n + 1), bs => readIn 8 (readInt 8) bs fun v b =>
    .next (.raw w ⟨v :: st.output, st.produced + 1, st.distances⟩ last n) b
  | .hdr w st last mlen g p, bs =>
    match hStep g p bs with
    | .next q b => .next (.hdr w st last mlen q.1 q.2) b
    | .exit m b => .next (.cmds w last m (.command (startState st mlen m))) b
    | .bad => .bad
    | .short => .short
  | .cmds w last m p, bs =>
    match cStep w m p bs with
    | .next p' b => .next (.cmds w last m p') b
    | .exit s b =>
      if usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy && usesEveryType m.distance s.distance then
        .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) b
      else .bad
    | .bad => .bad
    | .short => .short
  | .ended st, bs =>
    if bs.length % 8 = 0 then
      if bs.isEmpty then .exit (st.output.reverse.map Nat.toUInt8) bs else .bad
    else
      match readFill bs with
      | some b => .next (.ended st) b
      | none => .bad

/-- From a place with its bits, the stream's reading in order comes, producing nothing more, to a place where it has
too few bits. -/
def SShort (p : SPhase) (bs : List Bool) : Prop := ∃ q c, Reach sStep p bs q c ∧ sStep q c = .short ∧ q.out = p.out

/-- From a place with its bits, the stream's reading in order comes, producing nothing more, to a place where it has too
few bits, or to the stream's end with nothing after it, where the stream is valid if no more bits come. -/
def SPause (p : SPhase) (bs : List Bool) : Prop :=
  ∃ q c, Reach sStep p bs q c ∧ q.out = p.out ∧ (sStep q c = .short ∨ ∃ y, sStep q c = .exit y [])

theorem SShort.pause {p : SPhase} {bs : List Bool} (h : SShort p bs) : SPause p bs := by
  obtain ⟨q, c, h1, h2, h3⟩ := h
  exact ⟨q, c, h1, h3, Or.inl h2⟩

/-- The commands' reading in order is the stream's. -/
theorem reach_cmds {w : Nat} {last : Bool} {m : MetaBlockHeader} {p q : Phase} {bs c : List Bool} (h : Reach (cStep w m) p bs q c) :
    Reach sStep (.cmds w last m p) bs (.cmds w last m q) c := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next (by simp only [sStep, hs]) ih

theorem short_cmds {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {bs : List Bool} (h : CShort w m p bs) :
    SShort (.cmds w last m p) bs := by
  obtain ⟨q, c, h1, h2, h3⟩ := h
  exact ⟨_, c, reach_cmds h1, by simp only [sStep, h2], h3⟩

/-- The commands' end, when every block type occurred. -/
theorem sStep_cmds_end {w : Nat} {last : Bool} {m : MetaBlockHeader} {s : CommandState} (bs : List Bool) (h0 : s.remaining = 0)
    (hc : (usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy && usesEveryType m.distance s.distance) = true) :
    sStep (.cmds w last m (.command s)) bs = .next (afterBlock w last ⟨s.output, s.produced, s.distances⟩) bs := by
  simp only [sStep, cStep, h0, ↓reduceIte, hc]

/-- A header's reading in order is the stream's. -/
theorem reach_hdr {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {q q' : Gh × HPhase} {bs c : List Bool}
    (h : Reach hStepP q bs q' c) : Reach sStep (.hdr w st last mlen q.1 q.2) bs (.hdr w st last mlen q'.1 q'.2) c := by
  induction h with
  | refl => exact .refl _ _
  | next hs _ ih => exact .next (by simp only [sStep, show hStep _ _ _ = _ from hs]) ih

theorem short_hdr {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {bs : List Bool}
    (h : hStepP (g, p) bs = .short) : sStep (.hdr w st last mlen g p) bs = .short := by
  simp only [sStep, show hStep g p bs = _ from h]

theorem exit_hdr {w : Nat} {st : StreamState} {last : Bool} {mlen : Nat} {g : Gh} {p : HPhase} {bs b : List Bool} {m : MetaBlockHeader}
    (h : hStepP (g, p) bs = .exit m b) :
    sStep (.hdr w st last mlen g p) bs = .next (.cmds w last m (.command (startState st mlen m))) b := by
  simp only [sStep, show hStep g p bs = _ from h]

/-- An integer's bits, when they are there. -/
theorem readInt_of_le : ∀ (k : Nat) (bs : List Bool), k ≤ bs.length → ∃ v, readInt k bs = some (v, bs.drop k)
  | 0, bs, _ => ⟨0, by simp [readInt]⟩
  | _ + 1, [], h => absurd h (by simp)
  | k + 1, b :: bs, h => by
    obtain ⟨v, hv⟩ := readInt_of_le k bs (by simp at h; omega)
    exact ⟨b.toNat + 2 * v, by simp only [readInt, hv, Option.map_some, List.drop_succ_cons]⟩

/-- Metadata, `m` bytes at a time. -/
theorem reach_skip {w : Nat} {st : StreamState} {last : Bool} : ∀ (m n : Nat) (bs : List Bool), m ≤ n → m * 8 ≤ bs.length →
    Reach sStep (.skip w st last n) bs (.skip w st last (n - m)) (bs.drop (m * 8))
  | 0, n, bs, _, _ => by simpa using Reach.refl _ _
  | m + 1, n + 1, bs, h1, h2 => by
    obtain ⟨v, hv⟩ := readInt_of_le 8 bs (by omega)
    refine .next (show readIn 8 (readInt 8) bs _ = _ by rw [readIn_some hv]) ?_
    have := reach_skip (w := w) (st := st) (last := last) m n (bs.drop 8) (by omega) (by simp; omega)
    have e : (bs.drop 8).drop (m * 8) = bs.drop ((m + 1) * 8) := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [show n + 1 - (m + 1) = n - m by omega, ← e]
    exact this
  | _ + 1, 0, _, h1, _ => absurd h1 (by omega)

/-- Uncompressed bytes, as many as are read. -/
theorem reach_raw {w : Nat} {last : Bool} : ∀ (j n : Nat) (st : StreamState) (bs : List Bool) (vs : List Nat) (b : List Bool),
    j ≤ n → readBytes j bs = some (vs, b) →
    Reach sStep (.raw w st last n) bs (.raw w ⟨vs.reverse ++ st.output, st.produced + j, st.distances⟩ last (n - j)) b
  | 0, n, st, bs, vs, b, _, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simpa using Reach.refl _ _
  | j + 1, n + 1, st, bs, vs, b, h1, h => by
    simp only [readBytes] at h
    cases hv : readInt 8 bs with
    | none => rw [hv] at h; cases h
    | some p =>
      obtain ⟨v, b1⟩ := p
      rw [hv] at h
      cases hr : readBytes j b1 with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨vs1, b2⟩ := q
        simp only [hr, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine .next (show readIn 8 (readInt 8) bs _ = _ by rw [readIn_some hv]) ?_
        have := reach_raw (w := w) (last := last) j n ⟨v :: st.output, st.produced + 1, st.distances⟩ b1 vs1 b2 (by omega) hr
        have e1 : vs1.reverse ++ v :: st.output = (v :: vs1).reverse ++ st.output := by simp
        rw [e1, show st.produced + 1 + j = st.produced + (j + 1) by omega, show n - j = n + 1 - (j + 1) by omega] at this
        exact this
  | _ + 1, 0, _, _, _, _, h1, _ => absurd h1 (by omega)

end Brotli.Decoder
