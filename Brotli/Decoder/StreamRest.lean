module

public import Brotli.Decoder.HeaderDone
public import Brotli.Decoder.Loop

@[expose] public section

/-!
# What the spec still has to do in a stream

The bridge's `rest` for the whole stream: for each place the decoder can pause, what the spec still has to do, down to the
output. It uses `hrest` and `rest` for the places inside a header and a meta-block's commands.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The stream's end. -/
def endOf (st : StreamState) (bs : List Bool) : Option (List UInt8) :=
  readEnd bs >>= fun _ => some (st.output.reverse.map Nat.toUInt8)

/-- The meta-blocks from here, then the end. -/
def metaK (w : Nat) (st : StreamState) (bs : List Bool) : Option (List UInt8) :=
  metaBlocksFrom w st bs >>= fun p => endOf p.1 p.2

/-- What follows a meta-block. -/
def amK (w : Nat) (last : Bool) (st : StreamState) (bs : List Bool) : Option (List UInt8) :=
  if last then endOf st bs else metaK w st bs

/-- `decode`, in these terms. -/
theorem decode_metaK (input : List UInt8) :
    decode input = readWBITS (bits input) >>= fun p => metaK (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2 := by
  rw [decode_eq]
  cases readWBITS (bits input) with
  | none => rfl
  | some p => rfl

/-- One meta-block, then what follows it. -/
theorem metaK_step (w : Nat) (st : StreamState) (bs : List Bool) :
    metaK w st bs = readMetaBlock w st bs >>= fun p => amK w p.1.2 p.1.1 p.2 := by
  unfold metaK
  rw [metaBlocksFrom_step]
  cases readMetaBlock w st bs with
  | none => rfl
  | some p =>
    obtain ⟨⟨st1, last⟩, b⟩ := p
    show ((if last then some (st1, b) else metaBlocksFrom w st1 b) >>= _) = amK w last st1 b
    unfold amK
    cases last <;> rfl

section
variable {α : Type}

/-- What follows a meta-block's commands, with `A` what follows the meta-block. -/
def finishC (A : StreamState → List Bool → Option α) (m : MetaBlockHeader) (s : CommandState) (bs : List Bool) : Option α :=
  if usesEveryType m.literal s.literal && usesEveryType m.insertCopy s.insertCopy && usesEveryType m.distance s.distance then
    A ⟨s.output, s.produced, s.distances⟩ bs
  else none

/-- The commands from a state, and on. -/
def cmdK (w : Nat) (A : StreamState → List Bool → Option α) (m : MetaBlockHeader) (s : CommandState) (bs : List Bool) : Option α :=
  commandsFrom w m s bs >>= fun p => finishC A m p.1 p.2

/-- A meta-block's commands from their start. -/
def startState (st : StreamState) (mlen : Nat) (m : MetaBlockHeader) : CommandState :=
  ⟨st.output, st.produced, st.distances, mlen, .initial m.insertCopy, .initial m.literal, .initial m.distance⟩

/-- What follows a header, with its tables doing nothing. -/
def hdrK (w : Nat) (A : StreamState → List Bool → Option α) (st : StreamState) (mlen : Nat) : HK α :=
  ⟨fun m bs => cmdK w A m (startState st mlen m) bs, fun _ x => x⟩

/-- The commands' step lemma in these terms. -/
theorem cmdK_step {w : Nat} {A : StreamState → List Bool → Option α} {m : MetaBlockHeader} (s : CommandState) (bs : List Bool) (h0 : s.remaining ≠ 0) :
    cmdK w A m s bs = readCommand w m s bs >>= fun (s1, b) => cmdK w A m s1 b := by
  unfold cmdK
  rw [commandsFrom_step bs h0, bind_assoc]

/-- At MLEN, the commands are done. -/
theorem cmdK_stop {w : Nat} {A : StreamState → List Bool → Option α} {m : MetaBlockHeader} (s : CommandState) (bs : List Bool) (h0 : s.remaining = 0) :
    cmdK w A m s bs = finishC A m s bs := by
  unfold cmdK
  rw [commandsFrom_stop bs h0]
  rfl

end

/-- A compressed meta-block with the fuel settled. -/
private theorem readCompressed_form (w : Nat) (st : StreamState) (mlen : Nat) (bs : List Bool) :
    readCompressed w st mlen bs = readMetaBlockHeader bs >>= fun p => commandsFrom w p.1 (startState st mlen p.1) p.2 >>= fun q =>
      if usesEveryType p.1.literal q.1.literal && usesEveryType p.1.insertCopy q.1.insertCopy && usesEveryType p.1.distance q.1.distance then
        some ((⟨q.1.output, q.1.produced, q.1.distances⟩ : StreamState), q.2)
      else none := by
  simp only [readCompressed, commandsFrom, startState]

/-- A compressed meta-block in these terms. -/
theorem readCompressed_eq {α : Type} (w : Nat) (A : StreamState → List Bool → Option α) (st : StreamState) (mlen : Nat) (g : Gh) (bs : List Bool) :
    (readCompressed w st mlen bs >>= fun p => A p.1 p.2) = hrest (hdrK w A st mlen) g (.cat .L) bs := by
  show _ = hCatL (hdrK w A st mlen) g bs
  rw [← header_eq (hdrK w A st mlen) (fun _ _ => rfl), readCompressed_form, bind_assoc]
  congr 1
  funext p
  rw [bind_assoc]
  show _ = commandsFrom w p.1 (startState st mlen p.1) p.2 >>= _
  congr 1
  funext q
  obtain ⟨s, b2⟩ := q
  unfold finishC
  dsimp only
  generalize (usesEveryType p.1.literal s.literal && usesEveryType p.1.insertCopy s.insertCopy && usesEveryType p.1.distance s.distance) = c
  cases c <;> rfl

/-! ### The start of a meta-block -/

/-- What the start of a meta-block says. -/
inductive MetaStart where
  /-- ISLAST and ISLASTEMPTY set. -/
  | lastEmpty
  /-- A metadata block of `skip` bytes. -/
  | metadata (last : Bool) (skip : Nat)
  /-- A meta-block of `mlen` bytes, uncompressed or not. -/
  | data (last : Bool) (mlen : Nat) (unc : Bool)

/-- From ISUNCOMPRESSED. -/
def msUnc (last : Bool) (mlen : Nat) (bs : List Bool) : Option (MetaStart × List Bool) :=
  if last then some (.data true mlen false, bs)
  else readInt 1 bs >>= fun u => some (.data false mlen (u.1 = 1), u.2)

/-- From MLEN's bits. -/
def msLen (last : Bool) (mn : Nat) (bs : List Bool) : Option (MetaStart × List Bool) :=
  readInt (mn * 4) bs >>= fun v =>
    if 4 < mn ∧ v.1 >>> ((mn - 1) * 4) = 0 then none else msUnc last (v.1 + 1) v.2

/-- From MSKIPLEN's bits. -/
def msSkip (last : Bool) (n : Nat) (bs : List Bool) : Option (MetaStart × List Bool) :=
  readInt (n * 8) bs >>= fun v =>
    if 1 < n ∧ v.1 >>> ((n - 1) * 8) = 0 then none
    else some (.metadata last (if n = 0 then 0 else v.1 + 1), v.2)

/-- From MNIBBLES. -/
def msBody (last : Bool) (bs : List Bool) : Option (MetaStart × List Bool) :=
  readInt 2 bs >>= fun v =>
    if v.1 = 3 then
      readInt 1 v.2 >>= fun r =>
        if r.1 ≠ 0 then none else readInt 2 r.2 >>= fun n => msSkip last n.1 n.2
    else msLen last (v.1 + 4) v.2

/-- The start of a meta-block. -/
def metaStart (bs : List Bool) : Option (MetaStart × List Bool) :=
  readInt 1 bs >>= fun l =>
    if l.1 = 0 then msBody false l.2
    else readInt 1 l.2 >>= fun e => if e.1 = 1 then some (.lastEmpty, e.2) else msBody true e.2

/-- What follows the start of a meta-block, with `T` what follows the meta-block, by whether it is the last. -/
def afterStart {α : Type} (w : Nat) (T : Bool → StreamState → List Bool → Option α) (st : StreamState) (h : MetaStart) (bs : List Bool) : Option α :=
  match h with
  | .lastEmpty => T true st bs
  | .metadata last skip =>
    readFill bs >>= fun b => if b.length < skip * 8 then none else T last st (b.drop (skip * 8))
  | .data last mlen unc =>
    if unc then
      readFill bs >>= fun b => readBytes mlen b >>= fun p =>
        T last ⟨p.1.reverse ++ st.output, st.produced + mlen, st.distances⟩ p.2
    else readCompressed w st mlen bs >>= fun p => T last p.1 p.2

private theorem body_eq {α : Type} (w : Nat) (T : Bool → StreamState → List Bool → Option α) (st : StreamState) (last : Bool) (bs : List Bool) :
    (readMetaBlockBody w st last bs >>= fun p => T last p.1 p.2) = msBody last bs >>= fun p => afterStart w T st p.1 p.2 := by
  unfold readMetaBlockBody readMNIBBLES msBody
  show ((readInt 2 bs >>= _) >>= _) >>= _ = (readInt 2 bs >>= _) >>= _
  cases readInt 2 bs with
  | none => rfl
  | some v =>
    obtain ⟨v, b1⟩ := v
    by_cases h3 : v = 3
    · subst h3
      show (readMetadata b1 >>= fun b => some (st, b)) >>= _ = (readInt 1 b1 >>= _) >>= _
      unfold readMetadata
      show ((readInt 1 b1 >>= _) >>= _) >>= _ = (readInt 1 b1 >>= _) >>= _
      cases readInt 1 b1 with
      | none => rfl
      | some r =>
        obtain ⟨r, b2⟩ := r
        by_cases hr : r = 0
        · subst hr
          show ((readInt 2 b2 >>= _) >>= _) >>= _ = (readInt 2 b2 >>= _) >>= _
          cases readInt 2 b2 with
          | none => rfl
          | some n =>
            obtain ⟨n, b3⟩ := n
            show ((readInt (n * 8) b3 >>= _) >>= _) >>= _ = (readInt (n * 8) b3 >>= _) >>= _
            cases readInt (n * 8) b3 with
            | none => rfl
            | some q =>
              obtain ⟨x, b4⟩ := q
              by_cases hc : 1 < n ∧ x >>> ((n - 1) * 8) = 0
              · show ((if 1 < n ∧ x >>> ((n - 1) * 8) = 0 then none else _) >>= _) >>= _ =
                  ((if 1 < n ∧ x >>> ((n - 1) * 8) = 0 then none else _) >>= _)
                rw [ite_eq_left hc, ite_eq_left hc]
                rfl
              · show ((if 1 < n ∧ x >>> ((n - 1) * 8) = 0 then none else _) >>= _) >>= _ =
                  ((if 1 < n ∧ x >>> ((n - 1) * 8) = 0 then none else _) >>= _)
                rw [ite_eq_right hc, ite_eq_right hc]
                show ((readFill b4 >>= _) >>= _) >>= _ = readFill b4 >>= _
                cases readFill b4 with
                | none => rfl
                | some b5 =>
                  generalize (if n = 0 then 0 else x + 1) = sk
                  show ((if b5.length < sk * 8 then none else some (b5.drop (sk * 8))) >>= fun b => some (st, b)) >>=
                      (fun p => T last p.1 p.2) = (if b5.length < sk * 8 then none else T last st (b5.drop (sk * 8)))
                  by_cases hl : b5.length < sk * 8
                  · rw [ite_eq_left hl, ite_eq_left hl]
                    rfl
                  · rw [ite_eq_right hl, ite_eq_right hl]
                    rfl
        · show ((if r ≠ 0 then none else _) >>= _) >>= _ = ((if r ≠ 0 then none else _) >>= _)
          rw [ite_eq_left hr, ite_eq_left hr]
          rfl
    · have hne : ¬ (if v = 3 then 0 else v + 4) = 0 := by
        rw [ite_eq_right h3]
        omega
      show ((if (if v = 3 then 0 else v + 4) = 0 then _ else _) >>= _) = ((if v = 3 then _ else _) >>= _)
      rw [ite_eq_right hne, ite_eq_right h3, ite_eq_right h3]
      unfold readMLEN msLen
      show ((readInt ((v + 4) * 4) b1 >>= _) >>= _) >>= _ = (readInt ((v + 4) * 4) b1 >>= _) >>= _
      cases readInt ((v + 4) * 4) b1 with
      | none => rfl
      | some q =>
        obtain ⟨x, b2⟩ := q
        by_cases hc : 4 < v + 4 ∧ x >>> ((v + 4 - 1) * 4) = 0
        · show ((if 4 < v + 4 ∧ x >>> ((v + 4 - 1) * 4) = 0 then none else _) >>= _) >>= _ =
            ((if 4 < v + 4 ∧ x >>> ((v + 4 - 1) * 4) = 0 then none else _) >>= _)
          rw [ite_eq_left hc, ite_eq_left hc]
          rfl
        · show ((if 4 < v + 4 ∧ x >>> ((v + 4 - 1) * 4) = 0 then none else _) >>= _) >>= _ =
            ((if 4 < v + 4 ∧ x >>> ((v + 4 - 1) * 4) = 0 then none else _) >>= _)
          rw [ite_eq_right hc, ite_eq_right hc]
          show ((readIsUncompressed last b2 >>= _) >>= _) = (msUnc last (x + 1) b2 >>= _)
          unfold readIsUncompressed msUnc
          cases last with
          | true => rfl
          | false =>
            show ((readInt 1 b2 >>= _) >>= _) = (readInt 1 b2 >>= _) >>= _
            cases readInt 1 b2 with
            | none => rfl
            | some u =>
              obtain ⟨u, b3⟩ := u
              by_cases h1 : u = 1
              · subst h1
                show ((readFill b3 >>= _) >>= _) = readFill b3 >>= _
                cases readFill b3 with
                | none => rfl
                | some b4 =>
                  show ((readBytes (x + 1) b4 >>= _) >>= _) = readBytes (x + 1) b4 >>= _
                  cases readBytes (x + 1) b4 with
                  | none => rfl
                  | some b5 => rfl
              · show ((if u = 1 then _ else _) >>= _) = afterStart w T st (.data false (x + 1) (decide (u = 1))) b3
                rw [ite_eq_right h1]
                unfold afterStart
                simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]

/-- One meta-block and what follows it, as a meta-block's start and what follows that. -/
theorem block_start {α : Type} (w : Nat) (T : Bool → StreamState → List Bool → Option α) (st : StreamState) (bs : List Bool) :
    (readMetaBlock w st bs >>= fun p => T p.1.2 p.1.1 p.2) = metaStart bs >>= fun p => afterStart w T st p.1 p.2 := by
  unfold readMetaBlock metaStart
  show ((readInt 1 bs >>= _) >>= _) = (readInt 1 bs >>= _) >>= _
  cases readInt 1 bs with
  | none => rfl
  | some l =>
    obtain ⟨l, b1⟩ := l
    by_cases h0 : l = 0
    · subst h0
      show ((readMetaBlockBody w st false b1 >>= _) >>= _) = (msBody false b1 >>= _)
      rw [← body_eq, bind_assoc]
      congr 1
    · show ((if l = 0 then _ else _) >>= _) = ((if l = 0 then _ else _) >>= _)
      rw [ite_eq_right h0, ite_eq_right h0]
      show ((readInt 1 b1 >>= _) >>= _) = (readInt 1 b1 >>= _) >>= _
      cases readInt 1 b1 with
      | none => rfl
      | some e =>
        obtain ⟨e, b2⟩ := e
        by_cases h1 : e = 1
        · subst h1
          rfl
        · show ((if e = 1 then _ else _) >>= _) = ((if e = 1 then _ else _) >>= _)
          rw [ite_eq_right h1, ite_eq_right h1, ← body_eq, bind_assoc]
          congr 1

/-- The meta-blocks from here, as a meta-block's start and what follows it. -/
theorem metaK_start (w : Nat) (st : StreamState) (bs : List Bool) :
    metaK w st bs = metaStart bs >>= fun p => afterStart w (amK w) st p.1 p.2 := by
  rw [metaK_step, block_start]

end Brotli.Decoder
