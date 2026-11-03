import Brotli.Decoder.HeaderRest
import Brotli.Decoder.Order

/-!
# A header's reading, in order

The spec's reading of a meta-block's header in order, from each place `hrest` names, one field at a time: the place and
header so far that follow a field, the end of the header, a rejection, or too few bits. A field here is what the spec
reads between two places: a number, a symbol with its extra bits, or a simple prefix code with its two first bits.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-- Where a header's reading goes on to once a prefix code is read, by what the code is for. -/
def ownerPlace (g : Gh) : Owner → PrefixCode → HPhase
  | .type i n, c => .code (.count i n c) blockCountAlphabetSize
  | .count i n tc, c => .first i n tc c
  | .map isL ntrees rlemax, c => .vals isL ntrees rlemax c [] (mapSize g isL)
  | .codes k done left, c => .codes k (done ++ [c]) left

/-- NPOSTFIX and the four bits of NDIRECT. -/
def readNp (bs : List Bool) : Option ((Nat × Nat) × List Bool) :=
  readInt 2 bs >>= fun p => readInt 4 p.2 >>= fun q => some ((p.1, q.1), q.2)

/-- A step of a header read in order, with `g` the header so far. A field is at most 45 bits: a simple prefix code with
its two first bits. -/
def hStep (g : Gh) : HPhase → List Bool → ORes (Gh × HPhase) MetaBlockHeader
  | .cat i, bs => readIn 11 readVarLen bs fun v b =>
    if v < 2 then .next (g.setCat i ⟨v, .single 0, .single 0, 16777216⟩, catNextPhase i) b
    else .next (g, .code (.type i v) (blockTypeAlphabetSize v)) b
  | .code o size, bs => readIn 2 (readInt 2) bs fun h b =>
    if h = 1 then readIn 43 (simpleChain size (alphabetBits size)) b fun c b => .next (g, ownerPlace g o c) b
    else .next (g, .clens o size (codeLengthOrder.drop h) [] 0) b
  | .clens o size [] acc _, bs =>
    if (acc.filter (·.2 != 0)).length = 1 then .next (g, .syms o size (codeLengthCode acc) ⟨[], 8, none⟩) bs else .bad
  | .clens o size (x :: rest) acc sum, bs => readIn 4 readCodeLengthCodeLength bs fun v b =>
    if v = 0 then .next (g, .clens o size rest (acc ++ [(x, v)]) sum) b
    else if sum + (32 >>> v) = 32 then .next (g, .syms o size (codeLengthCode (acc ++ [(x, v)])) ⟨[], 8, none⟩) b
    else if 32 < sum + (32 >>> v) then .bad
    else .next (g, .clens o size rest (acc ++ [(x, v)]) (sum + (32 >>> v))) b
  | .syms o size clc st, bs =>
    if size < st.lens.length then .bad
    else if lengthSum st.lens = 32768 then
      .next (g, ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) bs
    else if st.lens.length = size then .bad
    else readIn 18 (lenSym clc) bs fun v b =>
      if size < (applyCodeLength st v.1 v.2).lens.length then .bad
      else if 32768 < lengthSum (applyCodeLength st v.1 v.2).lens then .bad
      else .next (g, .syms o size clc (applyCodeLength st v.1 v.2)) b
  | .first i n tc cc, bs => readIn 39 (readBlockCount cc) bs fun v b => .next (g.setCat i ⟨n, tc, cc, v⟩, catNextPhase i) b
  | .np, bs => readIn 6 readNp bs fun v b =>
    .next ({ g with m := { g.m with npostfix := v.1, ndirect := v.2 <<< v.1 } }, .modes [] g.m.literal.n) b
  | .modes done 0, bs => .next ({ g with m := { g.m with contextModes := done } }, .trees true) bs
  | .modes done (n + 1), bs => readIn 2 (readInt 2) bs fun v b => .next (g, .modes (done ++ [v]) n) b
  | .trees isL, bs => readIn 11 readVarLen bs fun v b =>
    if v < 2 then
      .next (g.setMap isL v (List.replicate (mapSize g isL) 0), mapNextPhase (g.setMap isL v (List.replicate (mapSize g isL) 0)) isL) b
    else .next (g, .rlemax isL v) b
  | .rlemax isL ntrees, bs => readIn 5 readRLEMAX bs fun v b => .next (g, .code (.map isL ntrees v) (contextMapAlphabetSize ntrees v)) b
  | .vals isL ntrees rlemax code done left, bs =>
    if left = 0 then .next (g, .imtf isL ntrees done) bs
    else readIn 31 (mapSym rlemax code) bs fun v b =>
      if left < v.2 then .bad else .next (g, .vals isL ntrees rlemax code (done ++ List.replicate v.2 v.1) (left - v.2)) b
  | .imtf isL ntrees vals, bs => readIn 1 (readInt 1) bs fun im b =>
    if (List.range ntrees).all (if im = 0 then vals else inverseMoveToFront vals).contains then
      .next (g.setMap isL ntrees (if im = 0 then vals else inverseMoveToFront vals),
        mapNextPhase (g.setMap isL ntrees (if im = 0 then vals else inverseMoveToFront vals)) isL) b
    else .bad
  | .codes k done (n + 1), bs => .next (g, .code (.codes k done n) (ckSize k g)) bs
  | .codes .L done 0, bs => .next (g.setCodes .L done, .codes .I [] g.m.insertCopy.n) bs
  | .codes .I done 0, bs => .next (g.setCodes .I done, .codes .D [] g.treesD) bs
  | .codes .D done 0, bs => .exit (g.setCodes .D done).m bs

/-- A header's reading in order, on places with the header so far. -/
def hStepP (q : Gh × HPhase) (bs : List Bool) : ORes (Gh × HPhase) MetaBlockHeader := hStep q.1 q.2 bs

/-- A code's lengths, when they are all there. -/
theorem hStep_syms_done {g : Gh} {o : Owner} {size : Nat} {clc : PrefixCode} {st : LengthState} (bs : List Bool)
    (hle : st.lens.length ≤ size) (h : lengthSum st.lens = 32768) :
    hStepP (g, .syms o size clc st) bs = .next (g, ownerPlace g o (.canonical (st.lens ++ List.replicate (size - st.lens.length) 0))) bs := by
  show (if size < st.lens.length then _ else _) = _
  rw [ite_eq_right (by omega)]
  show (if lengthSum st.lens = 32768 then _ else _) = _
  rw [ite_eq_left h]

/-- A code's lengths, when one more is to be read. -/
theorem hStep_syms_step {g : Gh} {o : Owner} {size : Nat} {clc : PrefixCode} {st : LengthState} (bs : List Bool)
    (hlt : st.lens.length < size) (h : lengthSum st.lens ≠ 32768) :
    hStepP (g, .syms o size clc st) bs = readIn 18 (lenSym clc) bs fun v b =>
      if size < (applyCodeLength st v.1 v.2).lens.length then .bad
      else if 32768 < lengthSum (applyCodeLength st v.1 v.2).lens then .bad
      else .next (g, .syms o size clc (applyCodeLength st v.1 v.2)) b := by
  show (if size < st.lens.length then _ else _) = _
  rw [ite_eq_right (by omega)]
  show (if lengthSum st.lens = 32768 then _ else _) = _
  rw [ite_eq_right h]
  show (if st.lens.length = size then _ else _) = _
  rw [ite_eq_right (by omega)]

/-- A context map's values, when none are left. -/
theorem hStep_vals_zero {g : Gh} {isL : Bool} {ntrees rlemax : Nat} {code : PrefixCode} {done : List Nat} (bs : List Bool) :
    hStepP (g, .vals isL ntrees rlemax code done 0) bs = .next (g, .imtf isL ntrees done) bs := rfl

/-- A context map's values, when more are left. -/
theorem hStep_vals_step {g : Gh} {isL : Bool} {ntrees rlemax : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} (bs : List Bool)
    (h0 : left ≠ 0) :
    hStepP (g, .vals isL ntrees rlemax code done left) bs = readIn 31 (mapSym rlemax code) bs fun v b =>
      if left < v.2 then .bad else .next (g, .vals isL ntrees rlemax code (done ++ List.replicate v.2 v.1) (left - v.2)) b := by
  show (if left = 0 then _ else _) = _
  rw [ite_eq_right h0]

end Brotli.Decoder
