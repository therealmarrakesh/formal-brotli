module

public import Brotli.Decoder.StreamRun

@[expose] public section

/-!
# A place's output is the start of the stream's

If the spec gets to an output from a place, that output starts with what the place has produced so far. Prefix soundness rests on this,
since a run that hits the memory limit never reaches an output of its own.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The bytes so far, most recent first, are the start of `y`. -/
def Ext (l : List Nat) (y : List UInt8) : Prop := l.reverse.map Nat.toUInt8 <+: y

/-- More bytes on the front of the output keep the start. -/
theorem Ext.front {l a : List Nat} {y : List UInt8} (h : Ext (a ++ l) y) : Ext l y := by
  unfold Ext at h ⊢
  rw [List.reverse_append, List.map_append] at h
  exact (List.prefix_append _ _).trans h

/-! ### Through a header -/

private theorem bind_some {β γ : Type} {x : Option β} {f : β → Option γ} {z : γ} (h : (x >>= f) = some z) : ∃ v, x = some v ∧ f v = some z :=
  Option.bind_eq_some_iff.mp h

section
variable {α : Type} {K : HK α} {y : α}

private theorem hCodesD_out {g : Gh} {done : List PrefixCode} {left : Nat} {bs : List Bool} (h : hCodesD K g done left bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCodesD, hCodesR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact ⟨_, _, h⟩

private theorem hCodesI_out {g : Gh} {done : List PrefixCode} {left : Nat} {bs : List Bool} (h : hCodesI K g done left bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCodesI, hCodesR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact hCodesD_out h

private theorem hCodesL_out {g : Gh} {done : List PrefixCode} {left : Nat} {bs : List Bool} (h : hCodesL K g done left bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCodesL, hCodesR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact hCodesI_out h

private theorem hCodes_out {k : CK} {g : Gh} {done : List PrefixCode} {left : Nat} {bs : List Bool} (h : hCodes K k g done left bs = some y) : ∃ m b, K.k m b = some y := by
  cases k with
  | L => exact hCodesL_out h
  | I => exact hCodesI_out h
  | D => exact hCodesD_out h

variable (hw : ∀ g x, K.r g x = x)
include hw

private theorem afterMap_out {g : Gh} {isL : Bool} {ntrees : Nat} {cmap : List Nat} {bs : List Bool} (h : afterMap K g isL ntrees cmap bs = some y) : ∃ m b, K.k m b = some y := by
  unfold afterMap at h
  cases isL with
  | true =>
    obtain ⟨p, _, h⟩ := bind_some h
    rw [hw] at h
    exact hCodesL_out h
  | false =>
    rw [ite_eq_right (by decide), hw] at h
    exact hCodesL_out h

private theorem hMap_out {g : Gh} {isL : Bool} {bs : List Bool} (h : hMap K g isL bs = some y) : ∃ m b, K.k m b = some y := by
  obtain ⟨p, _, h⟩ := bind_some h
  exact afterMap_out hw h

private theorem hModes_out {g : Gh} {done : List Nat} {left : Nat} {bs : List Bool} (h : hModes K g done left bs = some y) : ∃ m b, K.k m b = some y := by
  obtain ⟨p, _, h⟩ := bind_some h
  exact hMap_out hw h

private theorem hNp_out {g : Gh} {bs : List Bool} (h : hNp K g bs = some y) : ∃ m b, K.k m b = some y := by
  obtain ⟨p, _, h⟩ := bind_some h
  obtain ⟨q, _, h⟩ := bind_some h
  exact hModes_out hw h

private theorem hCatD_out {g : Gh} {bs : List Bool} (h : hCatD K g bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCatD, hCatR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact hNp_out hw h

private theorem hCatI_out {g : Gh} {bs : List Bool} (h : hCatI K g bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCatI, hCatR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact hCatD_out hw h

private theorem hCatL_out {g : Gh} {bs : List Bool} (h : hCatL K g bs = some y) : ∃ m b, K.k m b = some y := by
  rw [hCatL, hCatR_id] at h
  obtain ⟨p, _, h⟩ := bind_some h
  exact hCatI_out hw h

private theorem afterCat_out {g : Gh} {i : Cat} {c : BlockCategory} {bs : List Bool} (h : afterCat K g i c bs = some y) : ∃ m b, K.k m b = some y := by
  cases i with
  | L => exact hCatI_out hw h
  | I => exact hCatD_out hw h
  | D => exact hNp_out hw h

private theorem oCount_out {g : Gh} {i : Cat} {n : Nat} {tc cc : PrefixCode} {bs : List Bool} (h : oCount K g i n tc cc bs = some y) : ∃ m b, K.k m b = some y := by
  obtain ⟨p, _, h⟩ := bind_some h
  exact afterCat_out hw h

private theorem afterVals_out {g : Gh} {isL : Bool} {ntrees : Nat} {vals : List Nat} {bs : List Bool} (h : afterVals K g isL ntrees vals bs = some y) : ∃ m b, K.k m b = some y := by
  obtain ⟨p, _, h⟩ := bind_some h
  generalize (if p.1 = 0 then vals else inverseMoveToFront vals) = v at h
  split at h
  · exact afterMap_out hw h
  · cases h

private theorem ownerK_out {g : Gh} {o : Owner} {c : PrefixCode} {bs : List Bool} (h : ownerK K g o c bs = some y) : ∃ m b, K.k m b = some y := by
  cases o with
  | type i n =>
    simp only [ownerK] at h
    obtain ⟨p, _, h⟩ := bind_some h
    exact oCount_out hw h
  | count i n tc =>
    simp only [ownerK] at h
    exact oCount_out hw h
  | map isL ntrees rlemax =>
    obtain ⟨p, _, h⟩ := bind_some h
    exact afterVals_out hw h
  | codes k done left =>
    simp only [ownerK] at h
    exact hCodes_out h

/-- From a place in a header, the only way to an output is through what follows the header. -/
theorem hrest_out {g : Gh} {p : HPhase} {bs : List Bool} (h : hrest K g p bs = some y) : ∃ m b, K.k m b = some y := by
  cases p with
  | cat i =>
    cases i with
    | L => exact hCatL_out hw h
    | I => exact hCatI_out hw h
    | D => exact hCatD_out hw h
  | code o size =>
    obtain ⟨q, _, h⟩ := bind_some h
    exact ownerK_out hw h
  | clens o size order acc sum =>
    obtain ⟨q, _, h⟩ := bind_some h
    obtain ⟨r, _, h⟩ := bind_some h
    exact ownerK_out hw h
  | syms o size clc st =>
    obtain ⟨q, _, h⟩ := bind_some h
    exact ownerK_out hw h
  | first i n tc cc => exact oCount_out hw h
  | np => exact hNp_out hw h
  | modes done left => exact hModes_out hw h
  | trees isL => exact hMap_out hw h
  | rlemax isL ntrees =>
    obtain ⟨q, _, h⟩ := bind_some h
    obtain ⟨r, _, h⟩ := bind_some h
    exact ownerK_out hw h
  | vals isL ntrees rlemax code done left =>
    obtain ⟨q, _, h⟩ := bind_some h
    exact afterVals_out hw h
  | imtf isL ntrees vals => exact afterVals_out hw h
  | codes k done left => exact hCodes_out h

end

/-! ### Through a command -/

section
variable {α : Type}

private theorem afterLiterals_out {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option (List UInt8)} {y : List UInt8}
    (hK : ∀ s b, K s b = some y → Ext s.output y) {s : CommandState} {c clen : Nat} {bs : List Bool} (h : afterLiterals w m K s c clen bs = some y) :
    Ext s.output y := by
  unfold afterLiterals at h
  split at h
  · exact hK _ _ h
  · obtain ⟨⟨⟨dst, dcode, d⟩, b⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h1, h⟩ := bind_some h
    obtain ⟨a, ha, _⟩ := copyCommand_output h1
    have := hK _ _ h
    rw [ha] at this
    exact this.front

/-- From a place in a meta-block's commands, the output starts with what the place has produced, given that it does from what follows. -/
theorem rest_out {w : Nat} {m : MetaBlockHeader} {K : CommandState → List Bool → Option (List UInt8)} {y : List UInt8}
    (hK : ∀ s b, K s b = some y → Ext s.output y) {p : Phase} {bs : List Bool} (h : rest w m K p bs = some y) : Ext p.out y := by
  have hlit : ∀ {s : CommandState} {ic : BlockState} {c ilen clen n : Nat} {lit : BlockState} {out : List Nat} {b : List Bool},
      (readLiterals m n lit out b >>= fun (x : BlockState × List Nat × List Bool) => afterLiterals w m K (withLiterals s ic x.1 x.2.1 ilen) c clen x.2.2) = some y → Ext out y := by
    intro s ic c ilen clen n lit out b hh
    obtain ⟨⟨lit2, out2, b2⟩, h1, hh⟩ := bind_some hh
    obtain ⟨a, ha, _⟩ := readLiterals_output _ _ _ _ _ _ _ _ h1
    have := afterLiterals_out hK hh
    have e : (withLiterals s ic lit2 out2 ilen).output = out2 := rfl
    rw [e, ha] at this
    exact this.front
  cases p with
  | command s => exact hK _ _ h
  | insertCopy s ic =>
    obtain ⟨code, _, h⟩ := bind_some h
    obtain ⟨⟨⟨c, ilen, clen⟩, b⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · cases h
    · exact hlit h
  | copyLength s ic c ilen copyBits copyBase =>
    obtain ⟨⟨e, b⟩, _, h⟩ := bind_some h
    dsimp only at h
    split at h
    · cases h
    · exact hlit h
  | literals s ic c ilen clen n lit out => exact hlit h
  | literalSymbol s ic c ilen clen n lit out =>
    obtain ⟨mode, _, h⟩ := bind_some h
    obtain ⟨index, _, h⟩ := bind_some h
    obtain ⟨code, _, h⟩ := bind_some h
    obtain ⟨⟨byte, b⟩, _, h⟩ := bind_some h
    dsimp only at h
    exact (show Ext ([byte] ++ out) y from hlit h).front
  | distance s c clen => exact afterLiterals_out hK h
  | distanceSymbol s clen dist =>
    obtain ⟨index, _, h⟩ := bind_some h
    obtain ⟨code, _, h⟩ := bind_some h
    obtain ⟨⟨⟨dcode, d⟩, b⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h1, h⟩ := bind_some h
    obtain ⟨a, ha, _⟩ := copyCommand_output h1
    have := hK _ _ h
    rw [ha] at this
    exact this.front
  | copy s d n =>
    have := hK _ _ h
    obtain ⟨a, ha, _⟩ := copyBytes_output d n s.output
    rw [show ({ s with output := copyBytes d n s.output } : CommandState).output = copyBytes d n s.output from rfl, ha] at this
    exact this.front
  | word s pending =>
    have := hK _ _ h
    rw [show ({ s with output := pending.reverse ++ s.output } : CommandState).output = pending.reverse ++ s.output from rfl] at this
    exact this.front

end

/-! ### Through the stream -/

/-- The stream's end gives its output. -/
theorem endOf_out {st : StreamState} {bs : List Bool} {y : List UInt8} (h : endOf st bs = some y) : Ext st.output y := by
  obtain ⟨_, _, h⟩ := bind_some h
  have e : some (st.output.reverse.map Nat.toUInt8) = some y := h
  rw [Option.some.injEq] at e
  rw [Ext, e]
  exact List.prefix_refl _

/-- The meta-blocks from here, and on. -/
theorem metaK_out (w : Nat) : ∀ (n : Nat) (st : StreamState) (bs : List Bool) (y : List UInt8), bs.length = n → metaK w st bs = some y → Ext st.output y := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro st bs y hn h
    rw [metaK_step] at h
    obtain ⟨⟨⟨st1, l⟩, b⟩, h1, h⟩ := bind_some h
    have hlt := readMetaBlock_lt h1
    obtain ⟨a, ha, _⟩ := readMetaBlock_output h1
    have hE : Ext st1.output y := by
      dsimp only at h
      unfold amK at h
      cases l with
      | true => exact endOf_out h
      | false => exact ih b.length (by omega) st1 b y rfl h
    rw [ha] at hE
    exact hE.front

/-- What follows a meta-block. -/
theorem amK_out {w : Nat} {l : Bool} {st : StreamState} {bs : List Bool} {y : List UInt8} (h : amK w l st bs = some y) : Ext st.output y := by
  unfold amK at h
  cases l with
  | true => exact endOf_out h
  | false => exact metaK_out w _ st bs y rfl h

/-- The commands from a state, and on. -/
theorem cmdK_out {w : Nat} {l : Bool} {m : MetaBlockHeader} {s : CommandState} {bs : List Bool} {y : List UInt8} (h : cmdK w (amK w l) m s bs = some y) : Ext s.output y := by
  obtain ⟨⟨s1, b⟩, h1, h⟩ := bind_some h
  obtain ⟨_, _, a, ha, _⟩ := readCommands_output _ _ _ _ _ _ _ h1
  have hE : Ext s1.output y := by
    unfold finishC at h
    split at h
    · exact amK_out h
    · cases h
  rw [ha] at hE
  exact hE.front

/-- From a place, the output starts with what the place has produced. -/
theorem srest_out {p : SPhase} {bs : List Bool} {y : List UInt8} (h : srest specSem p bs = some y) : Ext p.out y := by
  cases p with
  | wbits => exact List.nil_prefix
  | mblock w st => exact metaK_out w _ st bs y rfl h
  | skip w st l n =>
    have h' : skipK (amK w l) st n bs = some y := h
    unfold skipK at h'
    split at h'
    · cases h'
    · exact amK_out h'
  | raw w st l n =>
    obtain ⟨⟨bytes, r⟩, _, h⟩ := bind_some h
    exact (amK_out h : Ext (bytes.reverse ++ st.output) y).front
  | hdr w st l mlen g q =>
    obtain ⟨m, b, h⟩ := hrest_out (fun _ _ => rfl) h
    exact (cmdK_out h : Ext (startState st mlen m).output y)
  | cmds w l m q => exact rest_out (fun _ _ hh => cmdK_out hh) h
  | ended st => exact endOf_out h

end Brotli.Decoder
