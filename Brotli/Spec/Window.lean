module

public import Brotli.Spec.Stream

@[expose] public section

/-!
# A meta-block under another window

The window enters a meta-block only through `copyCommand`'s `maxBackwardDistance w s.produced`, which is
`min w s.produced`, and `produced + remaining` stays the same over a meta-block's commands (`readCommand_output`). So a
compressed meta-block whose output fits two windows decodes the same under either.
-/

namespace Brotli.Spec

/-- A copy with at most `w` and `w'` bytes produced is the same under either window. -/
theorem copyCommand_window {w w' : Nat} {s : CommandState} {clen dcode d : Nat} (h : s.produced ≤ w)
    (h' : s.produced ≤ w') : copyCommand w s clen dcode d = copyCommand w' s clen dcode d := by
  unfold copyCommand maxBackwardDistance
  rw [Nat.min_eq_right h, Nat.min_eq_right h']

private theorem bind_congr' {α β : Type} {o : Option α} {f g : α → Option β} (h : ∀ a, f a = g a) :
    o.bind f = o.bind g := by
  cases o <;> simp [h]

/-- A command whose meta-block's output fits both windows is the same under either. -/
theorem readCommand_window {w w' : Nat} (m : MetaBlockHeader) (s : CommandState) (bs : List Bool)
    (h : s.produced + s.remaining ≤ w) (h' : s.produced + s.remaining ≤ w') :
    readCommand w m s bs = readCommand w' m s bs := by
  unfold readCommand
  refine bind_congr' fun x => ?_
  refine bind_congr' fun code => ?_
  refine bind_congr' fun y => ?_
  obtain ⟨⟨c, ilen, clen⟩, bs2⟩ := y
  dsimp only
  split
  · rfl
  rename_i hle
  refine bind_congr' fun z => ?_
  obtain ⟨lit, out, bs3⟩ := z
  dsimp only
  split
  · rfl
  refine bind_congr' fun t => ?_
  obtain ⟨⟨dst, dcode, d⟩, bs4⟩ := t
  dsimp only
  rw [copyCommand_window (w := w) (w' := w') (by dsimp only; omega) (by dsimp only; omega)]

/-- The commands of a meta-block whose output fits both windows are the same under either. -/
theorem readCommandsWith_window {w w' : Nat} (m : MetaBlockHeader) (out : Option (CommandState × List Bool))
    (fuel : Nat) : ∀ (s : CommandState) (bs : List Bool), s.produced + s.remaining ≤ w → s.produced + s.remaining ≤ w' →
      readCommandsWith w m out fuel s bs = readCommandsWith w' m out fuel s bs := by
  induction fuel with
  | zero => intro s bs _ _; rfl
  | succ f ih =>
    intro s bs h h'
    simp only [readCommandsWith]
    split
    · rfl
    rw [readCommand_window m s bs h h']
    cases hc : readCommand w' m s bs with
    | none => rfl
    | some p =>
      obtain ⟨s1, bs1⟩ := p
      obtain ⟨a, _, hl, hp⟩ := readCommand_output hc
      show readCommandsWith w m out f s1 bs1 = readCommandsWith w' m out f s1 bs1
      exact ih s1 bs1 (by omega) (by omega)

/-- A compressed meta-block whose output fits both windows is the same under either. -/
theorem readCompressed_window {w w' : Nat} (st : StreamState) (mlen : Nat) (bs : List Bool)
    (h : st.produced + mlen ≤ w) (h' : st.produced + mlen ≤ w') :
    readCompressed w st mlen bs = readCompressed w' st mlen bs := by
  unfold readCompressed readCommands
  simp (disch := (dsimp only; omega)) only [readCommandsWith_window (w := w) (w' := w')]

end Brotli.Spec
