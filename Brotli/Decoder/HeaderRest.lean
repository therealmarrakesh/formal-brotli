module

public import Brotli.Decoder.SmallRead
public import Brotli.Decoder.FastEq

@[expose] public section

/-!
# What the spec still has to do in a header

For each place the decoder can pause in a meta-block's header, what the spec still has to do from there, written with the
spec's own readers. `K` is what follows the header. The header read so far is a ghost record `Gh`, whose fields not yet read
hold whatever it started with. Each equation below takes one small read from one place to the next.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- The header so far, with the numbers of trees that the record of a header doesn't keep. -/
structure Gh where
  m : MetaBlockHeader
  treesL : Nat
  treesD : Nat

/-- A category of blocks. -/
inductive Cat where
  | L
  | I
  | D
  deriving DecidableEq

fast_deceq Cat [L, I, D]

/-- A group of prefix codes. -/
inductive CK where
  | L
  | I
  | D
  deriving DecidableEq

fast_deceq CK [L, I, D]

/-- What a header's reading goes on to, and what the groups of codes do to it once both context maps, and so every group's
number of trees, are read. For the spec's own reading, the second does nothing. For the memory demand, it adds what the
decoder reserves for the groups' tables. -/
structure HK (α : Type) where
  k : MetaBlockHeader → List Bool → Option α
  r : Gh → Option α → Option α

section

variable {α : Type} (K : HK α)

/-- A group of `left` codes, then `G` with the group. -/
def hCodesR (size : Nat) (G : List PrefixCode → List Bool → Option α) : List PrefixCode → Nat → List Bool → Option α
  | done, 0, bs => G done bs
  | done, n + 1, bs => readPrefixCode size bs >>= fun p => hCodesR size G (done ++ [p.1]) n p.2

/-- The distance codes, then what follows the header. -/
def hCodesD (g : Gh) (done : List PrefixCode) (left : Nat) (bs : List Bool) : Option α :=
  hCodesR (distanceAlphabetSize g.m.npostfix g.m.ndirect) (fun cs b => K.k { g.m with distanceCodes := cs } b) done left bs

/-- The insert-and-copy codes, and on. -/
def hCodesI (g : Gh) (done : List PrefixCode) (left : Nat) (bs : List Bool) : Option α :=
  hCodesR insertCopyAlphabetSize (fun cs b => hCodesD K { g with m := { g.m with insertCopyCodes := cs } } [] g.treesD b) done left bs

/-- The literal codes, and on. -/
def hCodesL (g : Gh) (done : List PrefixCode) (left : Nat) (bs : List Bool) : Option α :=
  hCodesR literalAlphabetSize (fun cs b => hCodesI K { g with m := { g.m with literalCodes := cs } } [] g.m.insertCopy.n b) done left bs

/-- A group of codes, and on. -/
def hCodes : CK → Gh → List PrefixCode → Nat → List Bool → Option α
  | .L, g, done, left, bs => hCodesL K g done left bs
  | .I, g, done, left, bs => hCodesI K g done left bs
  | .D, g, done, left, bs => hCodesD K g done left bs

/-- The alphabet of a group of codes. -/
def ckSize : CK → Gh → Nat
  | .L, _ => literalAlphabetSize
  | .I, _ => insertCopyAlphabetSize
  | .D, g => distanceAlphabetSize g.m.npostfix g.m.ndirect

/-- What follows a group of codes. -/
def ckAfter (g : Gh) (k : CK) (cs : List PrefixCode) (bs : List Bool) : Option α :=
  match k with
  | .L => hCodesI K { g with m := { g.m with literalCodes := cs } } [] g.m.insertCopy.n bs
  | .I => hCodesD K { g with m := { g.m with insertCopyCodes := cs } } [] g.treesD bs
  | .D => K.k { g.m with distanceCodes := cs } bs

/-- What follows a context map. -/
def afterMap (g : Gh) (isL : Bool) (ntrees : Nat) (cmap : List Nat) (bs : List Bool) : Option α :=
  if isL then
    (readTreesAndMap (distanceContextMapSize g.m.distance.n) bs >>= fun p =>
      K.r { g with m := { g.m with literalMap := cmap, distanceMap := p.1.2 }, treesL := ntrees, treesD := p.1.1 }
        (hCodesL K { g with m := { g.m with literalMap := cmap, distanceMap := p.1.2 }, treesL := ntrees, treesD := p.1.1 } [] ntrees p.2))
  else K.r { g with m := { g.m with distanceMap := cmap }, treesD := ntrees }
    (hCodesL K { g with m := { g.m with distanceMap := cmap }, treesD := ntrees } [] g.treesL bs)

/-- A context map's size. -/
def mapSize (g : Gh) (isL : Bool) : Nat :=
  if isL then literalContextMapSize g.m.literal.n else distanceContextMapSize g.m.distance.n

/-- A context map's trees and map, and on. -/
def hMap (g : Gh) (isL : Bool) (bs : List Bool) : Option α :=
  readTreesAndMap (mapSize g isL) bs >>= fun p => afterMap K g isL p.1.1 p.1.2 p.2

/-- The context modes, and on. -/
def hModes (g : Gh) (done : List Nat) (left : Nat) (bs : List Bool) : Option α :=
  readContextModes left bs >>= fun p => hMap K { g with m := { g.m with contextModes := done ++ p.1 } } true p.2

/-- NPOSTFIX and NDIRECT, and on. -/
def hNp (g : Gh) (bs : List Bool) : Option α :=
  readInt 2 bs >>= fun np => readInt 4 np.2 >>= fun nd =>
    hModes K { g with m := { g.m with npostfix := np.1, ndirect := nd.1 <<< np.1 } } [] g.m.literal.n nd.2

/-- A block category, then `N` with it. -/
def hCatR (N : BlockCategory → List Bool → Option α) (bs : List Bool) : Option α :=
  readVarLen bs >>= fun p =>
    if p.1 < 2 then N ⟨p.1, .single 0, .single 0, 16777216⟩ p.2
    else readPrefixCode (blockTypeAlphabetSize p.1) p.2 >>= fun q => readPrefixCode blockCountAlphabetSize q.2 >>= fun u =>
      readBlockCount u.1 u.2 >>= fun v => N ⟨p.1, q.1, u.1, v.1⟩ v.2

/-- The categories, and on. -/
def hCatD (g : Gh) (bs : List Bool) : Option α :=
  hCatR (fun c b => hNp K { g with m := { g.m with distance := c } } b) bs

/-- The categories, and on. -/
def hCatI (g : Gh) (bs : List Bool) : Option α :=
  hCatR (fun c b => hCatD K { g with m := { g.m with insertCopy := c } } b) bs

/-- The categories, and on. -/
def hCatL (g : Gh) (bs : List Bool) : Option α :=
  hCatR (fun c b => hCatI K { g with m := { g.m with literal := c } } b) bs

/-- From a category, and on. -/
def hCat : Cat → Gh → List Bool → Option α
  | .L, g, bs => hCatL K g bs
  | .I, g, bs => hCatI K g bs
  | .D, g, bs => hCatD K g bs

/-- What follows a category. -/
def afterCat (g : Gh) (i : Cat) (c : BlockCategory) (bs : List Bool) : Option α :=
  match i with
  | .L => hCatI K { g with m := { g.m with literal := c } } bs
  | .I => hCatD K { g with m := { g.m with insertCopy := c } } bs
  | .D => hNp K { g with m := { g.m with distance := c } } bs

private theorem codes_succ {β : Type} (size n : Nat) (bs : List Bool) (F : List PrefixCode × List Bool → Option β) :
    (readPrefixCodes size (n + 1) bs >>= F) =
      readPrefixCode size bs >>= fun p => readPrefixCodes size n p.2 >>= fun q => F (p.1 :: q.1, q.2) := by
  simp only [readPrefixCodes]
  cases readPrefixCode size bs with
  | none => rfl
  | some p =>
    show (readPrefixCodes size n p.2 >>= _) >>= _ = readPrefixCodes size n p.2 >>= _
    cases readPrefixCodes size n p.2 with
    | none => rfl
    | some q => rfl

private theorem append_cons' {β : Type} (done : List β) (p : β) (l : List β) : done ++ p :: l = done ++ [p] ++ l := by
  simp

section
variable {K}

/-- A group of codes is what `readPrefixCodes` reads. -/
theorem hCodesR_id (size : Nat) (G : List PrefixCode → List Bool → Option α) : ∀ (left : Nat) (done : List PrefixCode) (bs : List Bool),
    hCodesR size G done left bs = readPrefixCodes size left bs >>= fun p => G (done ++ p.1) p.2
  | 0, done, bs => by
    show G done bs = G (done ++ []) bs
    rw [List.append_nil]
  | n + 1, done, bs => by
    rw [codes_succ]
    show (readPrefixCode size bs >>= fun p => hCodesR size G (done ++ [p.1]) n p.2) = _
    congr 1
    funext p
    rw [hCodesR_id size G n]
    have e : (fun q : List PrefixCode × List Bool => G (done ++ [p.1] ++ q.1) q.2) = (fun q => G (done ++ p.1 :: q.1) q.2) := by
      funext q
      rw [append_cons' done p.1 q.1]
    rw [e]

/-- A category is what `readBlockCategory` reads. -/
theorem hCatR_id (N : BlockCategory → List Bool → Option α) (bs : List Bool) :
    hCatR N bs = readBlockCategory bs >>= fun p => N p.1 p.2 := by
  unfold hCatR readBlockCategory
  cases readVarLen bs with
  | none => rfl
  | some p =>
    obtain ⟨n, b1⟩ := p
    show (if n < 2 then _ else _) = ((if n < 2 then some ((⟨n, .single 0, .single 0, 16777216⟩ : BlockCategory), b1) else _) >>= _)
    by_cases hn : n < 2
    · rw [ite_eq_left hn, ite_eq_left hn]
      rfl
    · rw [ite_eq_right hn, ite_eq_right hn]
      show (readPrefixCode (blockTypeAlphabetSize n) b1 >>= fun q => readPrefixCode blockCountAlphabetSize q.2 >>= fun u =>
        readBlockCount u.1 u.2 >>= fun v => N ⟨n, q.1, u.1, v.1⟩ v.2) = (readPrefixCode (blockTypeAlphabetSize n) b1 >>= _) >>= _
      cases readPrefixCode (blockTypeAlphabetSize n) b1 with
      | none => rfl
      | some q =>
        obtain ⟨tc, b2⟩ := q
        show (readPrefixCode blockCountAlphabetSize b2 >>= fun u => readBlockCount u.1 u.2 >>= fun v => N ⟨n, tc, u.1, v.1⟩ v.2) =
          (readPrefixCode blockCountAlphabetSize b2 >>= _) >>= _
        cases readPrefixCode blockCountAlphabetSize b2 with
        | none => rfl
        | some u =>
          obtain ⟨cc, b3⟩ := u
          show (readBlockCount cc b3 >>= fun v => N ⟨n, tc, cc, v.1⟩ v.2) = (readBlockCount cc b3 >>= _) >>= _
          cases readBlockCount cc b3 with
          | none => rfl
          | some x => rfl

end

/-- The header, as `readMetaBlockHeader` reads it, is the chain from the first category, from any record to start with. -/
theorem header_eq (hr : ∀ g x, K.r g x = x) (g : Gh) (bs : List Bool) :
    (readMetaBlockHeader bs >>= fun p => K.k p.1 p.2) = hCatL K g bs := by
  unfold readMetaBlockHeader hCatL
  rw [hCatR_id]
  cases h1 : readBlockCategory bs with
  | none => rfl
  | some p1 =>
    obtain ⟨c1, b1⟩ := p1
    show (readBlockCategory b1 >>= _) >>= _ = hCatI K _ b1
    unfold hCatI
    rw [hCatR_id]
    show (readBlockCategory b1 >>= _) >>= _ = readBlockCategory b1 >>= _
    cases h2 : readBlockCategory b1 with
    | none => rfl
    | some p2 =>
      obtain ⟨c2, b2⟩ := p2
      show (readBlockCategory b2 >>= _) >>= _ = hCatD K _ b2
      unfold hCatD
      rw [hCatR_id]
      show (readBlockCategory b2 >>= _) >>= _ = readBlockCategory b2 >>= _
      cases h3 : readBlockCategory b2 with
      | none => rfl
      | some p3 =>
        obtain ⟨c3, b3⟩ := p3
        show (readInt 2 b3 >>= _) >>= _ = hNp K _ b3
        unfold hNp
        show (readInt 2 b3 >>= _) >>= _ = readInt 2 b3 >>= _
        cases h4 : readInt 2 b3 with
        | none => rfl
        | some p4 =>
          obtain ⟨np, b4⟩ := p4
          show (readInt 4 b4 >>= _) >>= _ = readInt 4 b4 >>= _
          cases h5 : readInt 4 b4 with
          | none => rfl
          | some p5 =>
            obtain ⟨nd, b5⟩ := p5
            show (readContextModes c1.n b5 >>= _) >>= _ = hModes K _ [] _ b5
            unfold hModes
            show (readContextModes c1.n b5 >>= _) >>= _ = readContextModes c1.n b5 >>= _
            cases h6 : readContextModes c1.n b5 with
            | none => rfl
            | some p6 =>
              obtain ⟨ms, b6⟩ := p6
              show (readTreesAndMap (literalContextMapSize c1.n) b6 >>= _) >>= _ = hMap K _ true b6
              unfold hMap mapSize
              show (readTreesAndMap (literalContextMapSize c1.n) b6 >>= _) >>= _ =
                readTreesAndMap (literalContextMapSize c1.n) b6 >>= _
              cases h7 : readTreesAndMap (literalContextMapSize c1.n) b6 with
              | none => rfl
              | some p7 =>
                obtain ⟨⟨tl, ml⟩, b7⟩ := p7
                show (readTreesAndMap (distanceContextMapSize c3.n) b7 >>= _) >>= _ =
                  readTreesAndMap (distanceContextMapSize c3.n) b7 >>= _
                cases h8 : readTreesAndMap (distanceContextMapSize c3.n) b7 with
                | none => rfl
                | some p8 =>
                  obtain ⟨⟨td, md⟩, b8⟩ := p8
                  show (readPrefixCodes literalAlphabetSize tl b8 >>= _) >>= _ = K.r _ (hCodesL K _ [] tl b8)
                  rw [hr]
                  unfold hCodesL
                  rw [hCodesR_id]
                  show (readPrefixCodes literalAlphabetSize tl b8 >>= _) >>= _ =
                    readPrefixCodes literalAlphabetSize tl b8 >>= _
                  cases h9 : readPrefixCodes literalAlphabetSize tl b8 with
                  | none => rfl
                  | some p9 =>
                    obtain ⟨cl, b9⟩ := p9
                    show (readPrefixCodes insertCopyAlphabetSize c2.n b9 >>= _) >>= _ = hCodesI K _ [] c2.n b9
                    unfold hCodesI
                    rw [hCodesR_id]
                    show (readPrefixCodes insertCopyAlphabetSize c2.n b9 >>= _) >>= _ =
                      readPrefixCodes insertCopyAlphabetSize c2.n b9 >>= _
                    cases h10 : readPrefixCodes insertCopyAlphabetSize c2.n b9 with
                    | none => rfl
                    | some p10 =>
                      obtain ⟨ci, b10⟩ := p10
                      show (readPrefixCodes (distanceAlphabetSize np (nd <<< np)) td b10 >>= _) >>= _ = hCodesD K _ [] td b10
                      unfold hCodesD
                      rw [hCodesR_id]
                      show (readPrefixCodes (distanceAlphabetSize np (nd <<< np)) td b10 >>= _) >>= _ =
                        readPrefixCodes (distanceAlphabetSize np (nd <<< np)) td b10 >>= _
                      cases h11 : readPrefixCodes (distanceAlphabetSize np (nd <<< np)) td b10 with
                      | none => rfl
                      | some p11 => rfl

/-- A group of codes when no more are left. -/
theorem hCodes_zero (k : CK) (g : Gh) (done : List PrefixCode) (bs : List Bool) :
    hCodes K k g done 0 bs = ckAfter K g k done bs := by
  cases k <;> rfl

/-- A group of codes when more are left. -/
theorem hCodes_succ (k : CK) (g : Gh) (done : List PrefixCode) (n : Nat) (bs : List Bool) :
    hCodes K k g done (n + 1) bs =
      readPrefixCode (ckSize k g) bs >>= fun p => hCodes K k g (done ++ [p.1]) n p.2 := by
  cases k <;> rfl

/-- The context modes when none are left. -/
theorem hModes_zero (g : Gh) (done : List Nat) (bs : List Bool) :
    hModes K g done 0 bs = hMap K { g with m := { g.m with contextModes := done } } true bs := by
  show hMap K { g with m := { g.m with contextModes := done ++ [] } } true bs = _
  rw [List.append_nil]

/-- The context modes when more are left. -/
theorem hModes_succ (g : Gh) (done : List Nat) (n : Nat) (bs : List Bool) :
    hModes K g done (n + 1) bs = readInt 2 bs >>= fun p => hModes K g (done ++ [p.1]) n p.2 := by
  simp only [hModes, readContextModes]
  cases readInt 2 bs with
  | none => rfl
  | some q =>
    show (readContextModes n q.2 >>= _) >>= _ = readContextModes n q.2 >>= _
    cases readContextModes n q.2 with
    | none => rfl
    | some t =>
      show hMap K { g with m := { g.m with contextModes := done ++ q.1 :: t.1 } } true t.2 =
        hMap K { g with m := { g.m with contextModes := done ++ [q.1] ++ t.1 } } true t.2
      rw [append_cons']

/-! ### Reading a prefix code's lengths, without fuel -/

private theorem syms_fuel (size : Nat) (clc : PrefixCode) : ∀ (f f' : Nat) (st : LengthState) (bs : List Bool),
    st.lens.length ≤ size → size < st.lens.length + f → size < st.lens.length + f' →
    readSymbolLengths size clc f st bs = readSymbolLengths size clc f' st bs
  | 0, _, _, _, hle, h, _ => by omega
  | _ + 1, 0, _, _, hle, _, h => by omega
  | f + 1, f' + 1, st, bs, _, h1, h2 => by
    simp only [readSymbolLengths, readSymbolLengthsWith]
    split
    · rfl
    split
    · rfl
    cases hd : decodeSymbol clc bs with
    | none => rfl
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      dsimp only [bind, Option.bind]
      cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
      | none => rfl
      | some q =>
        obtain ⟨e, bs2⟩ := q
        dsimp only
        have hgrow := applyCodeLength_length st sym e
        split
        · rfl
        split
        · rfl
        rename_i hsize _
        exact syms_fuel size clc f f' _ bs2 (by omega) (by omega) (by omega)

/-- The code lengths still to read, with the fuel settled. -/
def symsFrom (size : Nat) (clc : PrefixCode) (st : LengthState) (bs : List Bool) : Option (List Nat × List Bool) :=
  readSymbolLengths size clc (size + 1 - st.lens.length) st bs

/-- At the start of a code's lengths, the fuel is what `symsFrom` gives. -/
theorem symsFrom_start (size : Nat) (clc : PrefixCode) (bs : List Bool) :
    readSymbolLengths size clc (size + 1) ⟨[], 8, none⟩ bs = symsFrom size clc ⟨[], 8, none⟩ bs := rfl

/-- The lengths are done when the space is used up. -/
theorem symsFrom_done {size : Nat} {clc : PrefixCode} {st : LengthState} (bs : List Bool) (hle : st.lens.length ≤ size)
    (h : lengthSum st.lens = 32768) : symsFrom size clc st bs = some (st.lens ++ List.replicate (size - st.lens.length) 0, bs) := by
  unfold symsFrom
  obtain ⟨f, hf⟩ : ∃ f, size + 1 - st.lens.length = f + 1 := ⟨size - st.lens.length, by omega⟩
  rw [hf]
  simp only [readSymbolLengths, readSymbolLengthsWith, h, ↓reduceIte]

/-- With all the lengths read and space left, the code is invalid. -/
theorem symsFrom_full {size : Nat} {clc : PrefixCode} {st : LengthState} (bs : List Bool) (h : lengthSum st.lens ≠ 32768)
    (hlen : st.lens.length = size) : symsFrom size clc st bs = none := by
  unfold symsFrom
  rw [hlen, show size + 1 - size = 0 + 1 by omega]
  simp only [readSymbolLengths, readSymbolLengthsWith, h, ↓reduceIte, hlen]

/-- Otherwise one more symbol. -/
theorem symsFrom_step {size : Nat} {clc : PrefixCode} {st : LengthState} (bs : List Bool) (hlt : st.lens.length < size)
    (h : lengthSum st.lens ≠ 32768) :
    symsFrom size clc st bs = lenSym clc bs >>= fun p =>
      if size < (applyCodeLength st p.1.1 p.1.2).lens.length then none
      else if 32768 < lengthSum (applyCodeLength st p.1.1 p.1.2).lens then none
      else symsFrom size clc (applyCodeLength st p.1.1 p.1.2) p.2 := by
  unfold symsFrom lenSym
  obtain ⟨f, hf⟩ : ∃ f, size + 1 - st.lens.length = f + 1 := ⟨size - st.lens.length, by omega⟩
  rw [hf]
  have hne : st.lens.length ≠ size := by omega
  simp only [readSymbolLengths, readSymbolLengthsWith, h, ↓reduceIte, hne]
  cases hd : decodeSymbol clc bs with
  | none => rfl
  | some p =>
    obtain ⟨sym, bs1⟩ := p
    show (readInt _ bs1 >>= _) = (readInt _ bs1 >>= _) >>= _
    cases readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
    | none => rfl
    | some q =>
      obtain ⟨e, bs2⟩ := q
      show (if size < (applyCodeLength st sym e).lens.length then none
        else if 32768 < lengthSum (applyCodeLength st sym e).lens then none
        else readSymbolLengthsWith size clc none f (applyCodeLength st sym e) bs2) = _
      show _ = (if size < (applyCodeLength st sym e).lens.length then none
        else if 32768 < lengthSum (applyCodeLength st sym e).lens then none
        else readSymbolLengths size clc (size + 1 - (applyCodeLength st sym e).lens.length) (applyCodeLength st sym e) bs2)
      split
      · rfl
      split
      · rfl
      rename_i hsize _
      have hgrow := applyCodeLength_length st sym e
      exact syms_fuel size clc f _ _ bs2 (by omega) (by omega) (by omega)

/-! ### A context map's values, without fuel -/

private theorem vals_fuel (rlemax : Nat) (code : PrefixCode) : ∀ (f f' left : Nat) (bs : List Bool), left < f → left < f' →
    readContextMapValues rlemax code f left bs = readContextMapValues rlemax code f' left bs
  | 0, _, _, _, h, _ => by omega
  | _ + 1, 0, _, _, _, h => by omega
  | f + 1, f' + 1, left, bs, h1, h2 => by
    simp only [readContextMapValues, readContextMapValuesWith]
    split
    · rfl
    rename_i hleft
    cases hd : decodeSymbol code bs with
    | none => rfl
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      dsimp only [bind, Option.bind]
      split
      · have := vals_fuel rlemax code f f' (left - 1) bs1 (by omega) (by omega)
        simp only [readContextMapValues] at this
        rw [this]
      · cases hx : readInt sym bs1 with
        | none => rfl
        | some q =>
          obtain ⟨e, bs2⟩ := q
          dsimp only
          split
          · rfl
          · have hpos : 0 < 1 <<< sym := by
              rw [Nat.shiftLeft_eq, Nat.one_mul]
              exact Nat.two_pow_pos _
            have := vals_fuel rlemax code f f' (left - ((1 <<< sym) + e)) bs2 (by omega) (by omega)
            simp only [readContextMapValues] at this
            rw [this]

/-- The values still to read of a context map, with the fuel settled. -/
def valsFrom (rlemax : Nat) (code : PrefixCode) (left : Nat) (bs : List Bool) : Option (List Nat × List Bool) :=
  readContextMapValues rlemax code (left + 1) left bs

/-- With none left, the values are done. -/
theorem valsFrom_zero (rlemax : Nat) (code : PrefixCode) (bs : List Bool) : valsFrom rlemax code 0 bs = some ([], bs) := rfl

/-- Otherwise one more symbol. -/
theorem valsFrom_step {rlemax : Nat} {code : PrefixCode} {left : Nat} (bs : List Bool) (h0 : left ≠ 0) :
    valsFrom rlemax code left bs = mapSym rlemax code bs >>= fun p =>
      if left < p.1.2 then none
      else valsFrom rlemax code (left - p.1.2) p.2 >>= fun q => some (List.replicate p.1.2 p.1.1 ++ q.1, q.2) := by
  unfold valsFrom mapSym
  simp only [readContextMapValues, readContextMapValuesWith, h0, ↓reduceIte]
  cases hd : decodeSymbol code bs with
  | none => rfl
  | some p =>
    obtain ⟨sym, bs1⟩ := p
    show (match contextMapValue rlemax sym with
      | some v => (readContextMapValuesWith rlemax code none left (left - 1) bs1 >>= fun x => some (v :: x.1, x.2))
      | none => _) = (match contextMapValue rlemax sym with
        | some v => some ((v, 1), bs1)
        | none => _) >>= _
    cases hv : contextMapValue rlemax sym with
    | some v =>
      show (readContextMapValuesWith rlemax code none left (left - 1) bs1 >>= fun x => some (v :: x.1, x.2)) =
        (if left < 1 then none else readContextMapValues rlemax code (left - 1 + 1) (left - 1) bs1 >>= fun q =>
          some (List.replicate 1 v ++ q.1, q.2))
      rw [ite_eq_right (by omega)]
      have := vals_fuel rlemax code left (left - 1 + 1) (left - 1) bs1 (by omega) (by omega)
      simp only [readContextMapValues] at this
      rw [this]
      rfl
    | none =>
      show (readInt sym bs1 >>= _) = (readInt sym bs1 >>= _) >>= _
      cases readInt sym bs1 with
      | none => rfl
      | some q =>
        obtain ⟨e, bs2⟩ := q
        show (if left < (1 <<< sym) + e then none else
          (readContextMapValuesWith rlemax code none left (left - ((1 <<< sym) + e)) bs2 >>= fun x =>
            some (List.replicate ((1 <<< sym) + e) 0 ++ x.1, x.2))) =
          (if left < (1 <<< sym) + e then none else
          (readContextMapValues rlemax code (left - ((1 <<< sym) + e) + 1) (left - ((1 <<< sym) + e)) bs2 >>= fun x =>
            some (List.replicate ((1 <<< sym) + e) 0 ++ x.1, x.2)))
        split
        · rfl
        · have hpos : 0 < 1 <<< sym := by
            rw [Nat.shiftLeft_eq, Nat.one_mul]
            exact Nat.two_pow_pos _
          have := vals_fuel rlemax code left (left - ((1 <<< sym) + e) + 1) (left - ((1 <<< sym) + e)) bs2 (by omega) (by omega)
          simp only [readContextMapValues] at this
          rw [this]
          rfl

/-- The value a context map's code gives without reading a bit, if it gives one: a single symbol that stands for a value. -/
def runOf (rlemax : Nat) : PrefixCode → Option Nat
  | .single sym => contextMapValue rlemax sym
  | .canonical _ => none

/-- Such a code gives its value with a run of 1, reading nothing. -/
theorem mapSym_of_run {rlemax : Nat} {code : PrefixCode} {v : Nat} (h : runOf rlemax code = some v) (bs : List Bool) :
    mapSym rlemax code bs = some ((v, 1), bs) := by
  cases code with
  | single sym =>
    have h' : contextMapValue rlemax sym = some v := h
    simp only [mapSym, decodeSymbol, bind, Option.bind, h']
  | canonical => exact absurd h (by simp [runOf])

/-- With such a code, every value left is that one. -/
theorem valsFrom_run {rlemax : Nat} {code : PrefixCode} {v : Nat} (h : runOf rlemax code = some v) :
    ∀ left bs, valsFrom rlemax code left bs = some (List.replicate left v, bs) := by
  intro left
  induction left with
  | zero => intro bs; rfl
  | succ left ih =>
    intro bs
    rw [valsFrom_step bs (Nat.succ_ne_zero _), mapSym_of_run h]
    show (if left + 1 < 1 then none else valsFrom rlemax code (left + 1 - 1) bs >>= _) = _
    rw [ite_eq_right (by omega), Nat.add_sub_cancel, ih]
    rfl

/-- A canonical code reads at least one bit. -/
theorem decodeLengths_reads (lens : List Nat) (bs : List Bool) : ∀ (k len : Nat), 1 ≤ len → ∀ s r,
    decodeLengths lens bs len k = some (s, r) → r.length < bs.length
  | 0, _, _, _, _, h => by simp [decodeLengths] at h
  | k + 1, len, hl, s, r, h => by
    simp only [decodeLengths] at h
    cases e : readCode len bs with
    | none => rw [e] at h; cases h
    | some p =>
      obtain ⟨c, rest⟩ := p
      rw [e] at h
      have hlen := readCode_length len bs c rest e
      dsimp only at h
      split at h
      · split at h
        · cases h
          omega
        · exact decodeLengths_reads lens bs k (len + 1) (by omega) s r h
      · exact decodeLengths_reads lens bs k (len + 1) (by omega) s r h

/-- A value read without a bit comes from a code that gives it without reading. -/
theorem mapSym_noRead {rlemax : Nat} {code : PrefixCode} {bs r : List Bool} {v n : Nat}
    (h : mapSym rlemax code bs = some ((v, n), r)) (hl : r.length = bs.length) : runOf rlemax code = some v ∧ n = 1 := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, bs1⟩ := p
    rw [hd] at h
    dsimp only [bind, Option.bind] at h
    have hb1 : bs1.length ≤ bs.length := by
      cases code with
      | single => simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at hd; rw [← hd.2]; exact Nat.le_refl _
      | canonical lens => exact Nat.le_of_lt (decodeLengths_reads lens bs 15 1 (Nat.le_refl _) sym bs1 hd)
    cases hv : contextMapValue rlemax sym with
    | some w =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      cases code with
      | single sym' =>
        simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, -⟩ := hd
        exact ⟨hv, rfl⟩
      | canonical lens => exact absurd hl (Nat.ne_of_lt (decodeLengths_reads lens bs 15 1 (Nat.le_refl _) sym _ hd))
    | none =>
      rw [hv] at h
      cases hx : readInt sym bs1 with
      | none => rw [hx] at h; cases h
      | some q =>
        rw [hx] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := readInt_length sym bs1 q.1 q.2 hx
        have hs : sym ≠ 0 := fun e => by simp [contextMapValue, e] at hv
        omega

/-! ### Who a prefix code is for -/

/-- Who a prefix code is for. -/
inductive Owner where
  /-- A category's block type code. -/
  | type (i : Cat) (n : Nat)
  /-- A category's block count code. -/
  | count (i : Cat) (n : Nat) (tc : PrefixCode)
  /-- A context map's code. -/
  | map (isL : Bool) (ntrees rlemax : Nat)
  /-- One of a group of codes. -/
  | codes (k : CK) (done : List PrefixCode) (left : Nat)

/-- After a context map's values. -/
def afterVals (g : Gh) (isL : Bool) (ntrees : Nat) (vals : List Nat) (bs : List Bool) : Option α :=
  readInt 1 bs >>= fun im =>
    if (List.range ntrees).all (if im.1 = 0 then vals else inverseMoveToFront vals).contains then
      afterMap K g isL ntrees (if im.1 = 0 then vals else inverseMoveToFront vals) im.2
    else none

/-- What follows a block count code: the category's first count. -/
def oCount (g : Gh) (i : Cat) (n : Nat) (tc cc : PrefixCode) (bs : List Bool) : Option α :=
  readBlockCount cc bs >>= fun q => afterCat K g i ⟨n, tc, cc, q.1⟩ q.2

/-- What follows a prefix code. -/
def ownerK (g : Gh) : Owner → PrefixCode → List Bool → Option α
  | .type i n, c, bs => readPrefixCode blockCountAlphabetSize bs >>= fun p => oCount K g i n c p.1 p.2
  | .count i n tc, c, bs => oCount K g i n tc c bs
  | .map isL ntrees rlemax, c, bs =>
    valsFrom rlemax c (mapSize g isL) bs >>= fun q => afterVals K g isL ntrees q.1 q.2
  | .codes k done left, c, bs => hCodes K k g (done ++ [c]) left bs

/-- The places a header can pause. -/
inductive HPhase where
  | cat (i : Cat)
  /-- At a prefix code's first bits. -/
  | code (o : Owner) (size : Nat)
  /-- In the code lengths of the code length alphabet. -/
  | clens (o : Owner) (size : Nat) (order : List Nat) (acc : List (Nat × Nat)) (sum : Nat)
  /-- In a prefix code's lengths. -/
  | syms (o : Owner) (size : Nat) (clc : PrefixCode) (st : LengthState)
  /-- At a category's first count. -/
  | first (i : Cat) (n : Nat) (tc cc : PrefixCode)
  | np
  | modes (done : List Nat) (left : Nat)
  /-- At a context map's number of trees. -/
  | trees (isL : Bool)
  | rlemax (isL : Bool) (ntrees : Nat)
  /-- In a context map's values. -/
  | vals (isL : Bool) (ntrees rlemax : Nat) (code : PrefixCode) (done : List Nat) (left : Nat)
  /-- At a context map's last bit. -/
  | imtf (isL : Bool) (ntrees : Nat) (vals : List Nat)
  /-- In a group of codes. -/
  | codes (k : CK) (done : List PrefixCode) (left : Nat)

/-- What the spec still has to do from a place in a header. -/
def hrest (g : Gh) : HPhase → List Bool → Option α
  | .cat i, bs => hCat K i g bs
  | .code o size, bs => readPrefixCode size bs >>= fun p => ownerK K g o p.1 p.2
  | .clens o size order acc sum, bs =>
    readCodeLengthCodeLengths order acc sum bs >>= fun p =>
      symsFrom size (codeLengthCode p.1) ⟨[], 8, none⟩ p.2 >>= fun q => ownerK K g o (.canonical q.1) q.2
  | .syms o size clc st, bs => symsFrom size clc st bs >>= fun q => ownerK K g o (.canonical q.1) q.2
  | .first i n tc cc, bs => oCount K g i n tc cc bs
  | .np, bs => hNp K g bs
  | .modes done left, bs => hModes K g done left bs
  | .trees isL, bs => hMap K g isL bs
  | .rlemax isL ntrees, bs =>
    readRLEMAX bs >>= fun r => readPrefixCode (contextMapAlphabetSize ntrees r.1) r.2 >>= fun p =>
      ownerK K g (.map isL ntrees r.1) p.1 p.2
  | .vals isL ntrees rlemax code done left, bs =>
    valsFrom rlemax code left bs >>= fun q => afterVals K g isL ntrees (done ++ q.1) q.2
  | .imtf isL ntrees vals, bs => afterVals K g isL ntrees vals bs
  | .codes k done left, bs => hCodes K k g done left bs

/-- The ghost record with a category settled. -/
def Gh.setCat (g : Gh) : Cat → BlockCategory → Gh
  | .L, c => { g with m := { g.m with literal := c } }
  | .I, c => { g with m := { g.m with insertCopy := c } }
  | .D, c => { g with m := { g.m with distance := c } }

/-- The place after a category. -/
def catNextPhase : Cat → HPhase
  | .L => .cat .I
  | .I => .cat .D
  | .D => .np

theorem afterCat_eq (g : Gh) (i : Cat) (c : BlockCategory) (bs : List Bool) :
    afterCat K g i c bs = hrest K (g.setCat i c) (catNextPhase i) bs := by
  cases i <;> rfl

/-- A category's number of block types, then its codes if it has two types or more. -/
theorem hrest_cat (g : Gh) (i : Cat) (bs : List Bool) :
    hrest K g (.cat i) bs = readVarLen bs >>= fun p =>
      if p.1 < 2 then afterCat K g i ⟨p.1, .single 0, .single 0, 16777216⟩ p.2
      else hrest K g (.code (.type i p.1) (blockTypeAlphabetSize p.1)) p.2 := by
  have key : hCat K i g bs = hCatR (fun c b => afterCat K g i c b) bs := by cases i <;> rfl
  rw [show hrest K g (.cat i) bs = hCat K i g bs from rfl, key]
  rfl

/-- NPOSTFIX and NDIRECT, then the context modes. -/
theorem hrest_np (g : Gh) (bs : List Bool) :
    hrest K g .np bs = readInt 2 bs >>= fun np => readInt 4 np.2 >>= fun nd =>
      hrest K { g with m := { g.m with npostfix := np.1, ndirect := nd.1 <<< np.1 } } (.modes [] g.m.literal.n) nd.2 := rfl

/-- The place after a context map. -/
def mapNextPhase (g : Gh) : Bool → HPhase
  | true => .trees false
  | false => .codes .L [] g.treesL

/-- The ghost record with a context map settled. -/
def Gh.setMap (g : Gh) (isL : Bool) (ntrees : Nat) (cmap : List Nat) : Gh :=
  match isL with
  | true => { g with m := { g.m with literalMap := cmap }, treesL := ntrees }
  | false => { g with m := { g.m with distanceMap := cmap }, treesD := ntrees }

/-- What the end of a context map does to the reading: after the distance context map, the groups' reservation. -/
def mapR (g : Gh) : Bool → Option α → Option α
  | true, x => x
  | false, x => K.r g x

theorem afterMap_eq (g : Gh) (isL : Bool) (ntrees : Nat) (cmap : List Nat) (bs : List Bool) :
    afterMap K g isL ntrees cmap bs =
      mapR K (g.setMap isL ntrees cmap) isL (hrest K (g.setMap isL ntrees cmap) (mapNextPhase (g.setMap isL ntrees cmap) isL) bs) := by
  cases isL <;> rfl

/-- A context map's number of trees, then the map if there are two trees or more. -/
theorem hrest_trees (g : Gh) (isL : Bool) (bs : List Bool) :
    hrest K g (.trees isL) bs = readVarLen bs >>= fun p =>
      if p.1 < 2 then afterMap K g isL p.1 (List.replicate (mapSize g isL) 0) p.2
      else hrest K g (.rlemax isL p.1) p.2 := by
  show (readTreesAndMap (mapSize g isL) bs >>= _) = _
  unfold readTreesAndMap
  cases readVarLen bs with
  | none => rfl
  | some p =>
    obtain ⟨n, b1⟩ := p
    show ((if n < 2 then some ((n, List.replicate (mapSize g isL) 0), b1) else _) >>= _) = (if n < 2 then _ else _)
    by_cases hn : n < 2
    · rw [ite_eq_left hn, ite_eq_left hn]
      rfl
    · rw [ite_eq_right hn, ite_eq_right hn]
      show ((readContextMap (mapSize g isL) n b1 >>= _) >>= _) = _
      unfold readContextMap
      show ((readRLEMAX b1 >>= _) >>= _) >>= _ = readRLEMAX b1 >>= _
      cases readRLEMAX b1 with
      | none => rfl
      | some r =>
        show ((readPrefixCode (contextMapAlphabetSize n r.1) r.2 >>= _) >>= _) >>= _ =
          readPrefixCode (contextMapAlphabetSize n r.1) r.2 >>= _
        cases readPrefixCode (contextMapAlphabetSize n r.1) r.2 with
        | none => rfl
        | some c =>
          show ((readContextMapValues r.1 c.1 (mapSize g isL + 1) (mapSize g isL) c.2 >>= _) >>= _) >>= _ =
            (valsFrom r.1 c.1 (mapSize g isL) c.2 >>= _)
          unfold valsFrom
          cases readContextMapValues r.1 c.1 (mapSize g isL + 1) (mapSize g isL) c.2 with
          | none => rfl
          | some v =>
            show ((readInt 1 v.2 >>= _) >>= _) >>= _ = readInt 1 v.2 >>= _
            cases readInt 1 v.2 with
            | none => rfl
            | some im =>
              show ((if (List.range n).all (if im.1 = 0 then v.1 else inverseMoveToFront v.1).contains then
                  some (if im.1 = 0 then v.1 else inverseMoveToFront v.1, im.2) else none) >>= _) >>= _ =
                if (List.range n).all (if im.1 = 0 then v.1 else inverseMoveToFront v.1).contains then _ else _
              generalize (if im.1 = 0 then v.1 else inverseMoveToFront v.1) = fin
              by_cases c : (List.range n).all fin.contains = true
              · rw [ite_eq_left c, ite_eq_left c]
                rfl
              · rw [ite_eq_right c, ite_eq_right c]
                rfl

/-- The context modes, when none are left. -/
theorem hrest_modes_zero (g : Gh) (done : List Nat) (bs : List Bool) :
    hrest K g (.modes done 0) bs = hrest K { g with m := { g.m with contextModes := done } } (.trees true) bs :=
  hModes_zero K g done bs

/-- The context modes, when more are left. -/
theorem hrest_modes_succ (g : Gh) (done : List Nat) (n : Nat) (bs : List Bool) :
    hrest K g (.modes done (n + 1)) bs = readInt 2 bs >>= fun p => hrest K g (.modes (done ++ [p.1]) n) p.2 :=
  hModes_succ K g done n bs

/-- A group of codes, when more are left. -/
theorem hrest_codes_succ (k : CK) (g : Gh) (done : List PrefixCode) (n : Nat) (bs : List Bool) :
    hrest K g (.codes k done (n + 1)) bs = hrest K g (.code (.codes k done n) (ckSize k g)) bs :=
  hCodes_succ K k g done n bs

/-- The ghost record with a group of codes settled. -/
def Gh.setCodes (g : Gh) : CK → List PrefixCode → Gh
  | .L, cs => { g with m := { g.m with literalCodes := cs } }
  | .I, cs => { g with m := { g.m with insertCopyCodes := cs } }
  | .D, cs => { g with m := { g.m with distanceCodes := cs } }

/-- A group of codes, when none are left and another group follows. -/
theorem hrest_codes_L (g : Gh) (done : List PrefixCode) (bs : List Bool) :
    hrest K g (.codes .L done 0) bs = hrest K (g.setCodes .L done) (.codes .I [] g.m.insertCopy.n) bs :=
  hCodes_zero K .L g done bs

/-- A group of codes, when none are left and another group follows. -/
theorem hrest_codes_I (g : Gh) (done : List PrefixCode) (bs : List Bool) :
    hrest K g (.codes .I done 0) bs = hrest K (g.setCodes .I done) (.codes .D [] g.treesD) bs :=
  hCodes_zero K .I g done bs

/-- The last group of codes ends the header. -/
theorem hrest_codes_D (g : Gh) (done : List PrefixCode) (bs : List Bool) :
    hrest K g (.codes .D done 0) bs = K.k (g.setCodes .D done).m bs :=
  hCodes_zero K .D g done bs

/-- A prefix code read from its first bits: simple or complex. -/
theorem hrest_code (g : Gh) (o : Owner) (size : Nat) (bs : List Bool) :
    hrest K g (.code o size) bs = readInt 2 bs >>= fun h =>
      if h.1 = 1 then simpleChain size (alphabetBits size) h.2 >>= fun p => ownerK K g o p.1 p.2
      else hrest K g (.clens o size (codeLengthOrder.drop h.1) [] 0) h.2 := by
  simp only [hrest, readPrefixCode]
  cases readInt 2 bs with
  | none => rfl
  | some h =>
    obtain ⟨hskip, r⟩ := h
    show ((if hskip = 1 then readSimple size r else readComplex size hskip r) >>= _) =
      (if hskip = 1 then _ else _)
    by_cases h1 : hskip = 1
    · rw [ite_eq_left h1, ite_eq_left h1, simpleChain_eq]
    · rw [ite_eq_right h1, ite_eq_right h1]
      unfold readComplex
      cases readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 r with
      | none => rfl
      | some p =>
        show (readSymbolLengths size _ (size + 1) ⟨[], 8, none⟩ p.2 >>= _) >>= _ = symsFrom size _ _ p.2 >>= _
        rw [symsFrom_start]
        cases symsFrom size (codeLengthCode p.1) ⟨[], 8, none⟩ p.2 with
        | none => rfl
        | some q => rfl

end

end Brotli.Decoder
