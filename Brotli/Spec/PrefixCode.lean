import Brotli.Spec.Bits

/-!
# Prefix codes

RFC 7932 §3.
-/

namespace Brotli.Spec

/-- A prefix code: a single symbol with a code of length zero, or a canonical code given by each
symbol's code length (§3.2). -/
inductive PrefixCode where
  | single (sym : Nat)
  | canonical (lens : List Nat)
  deriving DecidableEq

/-- `bl_count[N]`, the number of codes of length `N` (§3.2, step 1). -/
def blCount (lens : List Nat) (n : Nat) : Nat :=
  if n = 0 then 0 else (lens.filter (· == n)).length

/-- `next_code[bits]`, the smallest code of length `bits` (§3.2, step 2). -/
def nextCode (lens : List Nat) : Nat → Nat
  | 0 => 0
  | bits + 1 => (nextCode lens bits + blCount lens bits) <<< 1

/-- The code of symbol `n`; a code length of zero has none (§3.2, step 3). -/
def code (lens : List Nat) (n : Nat) : Option Nat :=
  match lens[n]? with
  | some len =>
    if len = 0 then none
    else some (nextCode lens len + ((lens.take n).filter (· == len)).length)
  | none => none

/-- The symbols of length `len`, in symbol order. -/
def symbolsOfLength (lens : List Nat) (len : Nat) : List Nat :=
  (lens.zipIdx.filter (·.1 == len)).map (·.2)

/-- Decoding with a canonical code, trying the `k` code lengths from `len` up. -/
def decodeLengths (lens : List Nat) (bs : List Bool) : Nat → Nat → Option (Nat × List Bool)
  | _, 0 => none
  | len, k + 1 =>
    match readCode len bs with
    | none => none
    | some (c, rest) =>
      if nextCode lens len ≤ c then
        match (symbolsOfLength lens len)[c - nextCode lens len]? with
        | some sym => some (sym, rest)
        | none => decodeLengths lens bs (len + 1) k
      else decodeLengths lens bs (len + 1) k

/-- Decoding one symbol. A single-symbol code reads no bits (§3.4, §3.5). -/
def decodeSymbol : PrefixCode → List Bool → Option (Nat × List Bool)
  | .single sym, bs => some (sym, bs)
  | .canonical lens, bs => decodeLengths lens bs 1 15

/-! ### Canonical prefix codes -/

private theorem filter_range_length (lens : List Nat) (l : Nat) : ∀ m,
    ((List.range m).filter fun k => lens[k]? == some l).length =
      ((lens.take m).filter (· == l)).length
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.take_add_one, List.filter_append, List.filter_append,
      List.length_append, List.length_append, filter_range_length lens l m]
    cases h : lens[m]? with
    | none => simp [h]
    | some v => by_cases hv : v = l <;> simp [h, hv]

private theorem getElem?_filter_range (p : Nat → Bool) : ∀ (n i s : Nat),
    ((List.range n).filter p)[i]? = some s →
      s < n ∧ p s = true ∧ ((List.range s).filter p).length = i
  | 0, _, _, h => by simp at h
  | n + 1, i, s, h => by
    rw [List.range_succ, List.filter_append] at h
    by_cases hi : i < ((List.range n).filter p).length
    · rw [List.getElem?_append_left hi] at h
      obtain ⟨h1, h2, h3⟩ := getElem?_filter_range p n i s h
      exact ⟨by omega, h2, h3⟩
    · rw [List.getElem?_append_right (by omega)] at h
      by_cases hp : p n = true
      · simp only [List.filter_cons, hp, ↓reduceIte, List.filter_nil] at h
        have hz : i - ((List.range n).filter p).length = 0 := by
          cases hk : i - ((List.range n).filter p).length with
          | zero => rfl
          | succ k => rw [hk] at h; simp at h
        rw [hz] at h
        simp only [List.getElem?_cons_zero, Option.some.injEq] at h
        subst h
        exact ⟨by omega, hp, by omega⟩
      · simp [hp] at h

private theorem filter_range_getElem? (p : Nat → Bool) : ∀ (n s : Nat), s < n → p s = true →
    ((List.range n).filter p)[((List.range s).filter p).length]? = some s
  | 0, _, h, _ => by omega
  | n + 1, s, h, hp => by
    rw [List.range_succ, List.filter_append]
    by_cases hs : s < n
    · have := filter_range_getElem? p n s hs hp
      have hlt : ((List.range s).filter p).length < ((List.range n).filter p).length := by
        refine Nat.lt_of_not_le fun hc => ?_
        rw [List.getElem?_eq_none hc] at this
        simp at this
      rw [List.getElem?_append_left hlt, this]
    · have : s = n := by omega
      subst this
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp [hp]

private theorem take_filter_le (lens : List Nat) (q : Nat → Bool) (m : Nat) :
    ((lens.take m).filter q).length ≤ (lens.filter q).length := by
  conv => rhs; rw [← List.take_append_drop m lens]
  rw [List.filter_append, List.length_append]
  omega

private theorem zipIdx_filter (len : Nat) : ∀ (lens : List Nat) (k : Nat),
    ((lens.zipIdx k).filter (·.1 == len)).map (·.2) =
      ((List.range lens.length).filter fun n => lens[n]? == some len).map (· + k)
  | [], _ => by simp
  | x :: xs, k => by
    rw [List.zipIdx_cons, List.length_cons, List.range_succ_eq_map, List.filter_cons,
      List.filter_cons, List.filter_map]
    have ih := zipIdx_filter len xs (k + 1)
    have hcomp : ((fun n => (x :: xs)[n]? == some len) ∘ (· + 1)) =
        fun n => xs[n]? == some len := by
      funext n
      simp
    rw [hcomp]
    by_cases hx : x = len
    · simp only [hx, beq_self_eq_true, ↓reduceIte, List.map_cons, List.getElem?_cons_zero,
        List.map_map]
      rw [ih]
      simp only [Function.comp_def, Nat.zero_add]
      congr 2
      funext n
      omega
    · have : (x == len) = false := by simpa using hx
      have : ((x :: xs)[0]? == some len) = false := by simpa using hx
      simp only [*, Bool.false_eq_true, ↓reduceIte, List.map_map]
      simp only [Function.comp_def]
      congr 1
      funext n
      omega

/-- `symbolsOfLength` as the symbols in order whose code length is `len`. -/
private theorem symbolsOfLength_eq (lens : List Nat) (len : Nat) :
    symbolsOfLength lens len = (List.range lens.length).filter fun n => lens[n]? == some len := by
  unfold symbolsOfLength
  rw [zipIdx_filter]
  simp

/-- The symbols of length `len ≠ 0` number `bl_count[len]`. -/
theorem symbolsOfLength_length (lens : List Nat) {len : Nat} (h : len ≠ 0) :
    (symbolsOfLength lens len).length = blCount lens len := by
  rw [symbolsOfLength_eq]
  unfold blCount
  rw [filter_range_length, List.take_length]
  simp [h]

/-- The end of the codes of length `l`, shifted to a longer length, is at most its first code. -/
theorem nextCode_shift (lens : List Nat) (l : Nat) : ∀ d,
    (nextCode lens l + blCount lens l) * 2 ^ (d + 1) ≤ nextCode lens (l + d + 1)
  | 0 => by simp [nextCode, Nat.shiftLeft_eq]
  | d + 1 => by
    have ih := nextCode_shift lens l d
    rw [show l + (d + 1) + 1 = (l + d + 1) + 1 by omega,
      show nextCode lens (l + d + 1 + 1) =
        (nextCode lens (l + d + 1) + blCount lens (l + d + 1)) <<< 1 from rfl, Nat.shiftLeft_eq]
    calc (nextCode lens l + blCount lens l) * 2 ^ (d + 1 + 1)
        = (nextCode lens l + blCount lens l) * 2 ^ (d + 1) * 2 := by
          rw [Nat.pow_succ, Nat.mul_assoc]
      _ ≤ nextCode lens (l + d + 1) * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ (nextCode lens (l + d + 1) + blCount lens (l + d + 1)) * 2 ^ 1 := by
          rw [Nat.pow_one]
          exact Nat.mul_le_mul_right 2 (Nat.le_add_right _ _)

/-- A symbol's code lies among the consecutive codes of its length. -/
theorem code_bounds {lens : List Nat} {s len c : Nat} (hs : lens[s]? = some len) (h0 : len ≠ 0)
    (hc : code lens s = some c) :
    nextCode lens len ≤ c ∧ c < nextCode lens len + blCount lens len := by
  unfold code at hc
  rw [hs] at hc
  simp only [h0, ↓reduceIte, Option.some.injEq] at hc
  subst hc
  refine ⟨Nat.le_add_right _ _, ?_⟩
  have hlt : ((lens.take s).filter (· == len)).length + 1 ≤
      ((lens.take (s + 1)).filter (· == len)).length := by
    rw [List.take_add_one, hs, List.filter_append, List.length_append]
    simp
  have := take_filter_le lens (· == len) (s + 1)
  unfold blCount
  simp only [h0, ↓reduceIte]
  omega

/-- Codes of one length are consecutive, in symbol order (§3.2). -/
theorem code_consecutive {lens : List Nat} {m n len : Nat} (hmn : m < n)
    (hm : lens[m]? = some len) (hn : lens[n]? = some len) (h0 : len ≠ 0)
    (hbetween : ∀ k, m < k → k < n → lens[k]? ≠ some len) :
    code lens n = (code lens m).map (· + 1) := by
  have step : ∀ k, ((lens.take (k + 1)).filter (· == len)).length =
      ((lens.take k).filter (· == len)).length + (if lens[k]? = some len then 1 else 0) := by
    intro k
    rw [List.take_add_one, List.filter_append, List.length_append]
    cases lens[k]? with
    | none => simp
    | some v => by_cases hv : v = len <;> simp [hv]
  have run : ∀ d, m + 1 + d ≤ n →
      ((lens.take (m + 1 + d)).filter (· == len)).length =
        ((lens.take m).filter (· == len)).length + 1 := by
    intro d
    induction d with
    | zero => intro _; rw [step, hm]; simp
    | succ d ih =>
      intro hd
      rw [show m + 1 + (d + 1) = (m + 1 + d) + 1 by omega, step,
        ite_eq_right (hbetween _ (by omega) (by omega)), ih (by omega)]
  have := run (n - (m + 1)) (by omega)
  rw [show m + 1 + (n - (m + 1)) = n by omega] at this
  unfold code
  rw [hm, hn]
  simp [h0, this, Nat.add_assoc]

/-- Shorter codes precede longer codes (§3.2). -/
theorem code_shorter_precedes {lens : List Nat} {a b la lb ca cb : Nat}
    (ha : lens[a]? = some la) (ha0 : la ≠ 0) (hb : lens[b]? = some lb) (hlt : la < lb)
    (hca : code lens a = some ca) (hcb : code lens b = some cb) :
    ca < cb / 2 ^ (lb - la) := by
  have ⟨_, hca2⟩ := code_bounds ha ha0 hca
  have ⟨hcb1, _⟩ := code_bounds hb (by omega) hcb
  have hshift := nextCode_shift lens la (lb - la - 1)
  rw [show la + (lb - la - 1) + 1 = lb by omega, show lb - la - 1 + 1 = lb - la by omega]
    at hshift
  have : nextCode lens la + blCount lens la ≤ cb / 2 ^ (lb - la) :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
  omega

/-- `decodeLengths` returns a symbol only when the bits read are its code word. -/
theorem decodeLengths_sound (lens : List Nat) : ∀ (k l : Nat) (bs : List Bool) (s : Nat)
    (rest : List Bool), 1 ≤ l → decodeLengths lens bs l k = some (s, rest) →
    ∃ len c w, lens[s]? = some len ∧ len ≠ 0 ∧ code lens s = some c ∧
      readCode len w = some (c, []) ∧ bs = w ++ rest
  | 0, _, _, _, _, _, h => by simp [decodeLengths] at h
  | k + 1, l, bs, s, rest, hl, h => by
    simp only [decodeLengths] at h
    cases hr : readCode l bs with
    | none => rw [hr] at h; simp at h
    | some p =>
      obtain ⟨c, r⟩ := p
      rw [hr] at h
      dsimp only at h
      split at h
      · rename_i hle
        split at h
        · rename_i sym hsym
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [symbolsOfLength_eq] at hsym
          obtain ⟨hslt, hps, hcount⟩ := getElem?_filter_range _ _ _ _ hsym
          have hlen : lens[sym]? = some l := by simpa using hps
          obtain ⟨w, hw, hcw⟩ := readCode_split l bs c r hr
          refine ⟨l, c, w, hlen, by omega, ?_, hcw, hw⟩
          unfold code
          rw [hlen]
          simp only [show l ≠ 0 by omega, ↓reduceIte, Option.some.injEq]
          rw [← filter_range_length lens l sym, hcount]
          omega
        · exact decodeLengths_sound lens k (l + 1) bs s rest (by omega) h
      · exact decodeLengths_sound lens k (l + 1) bs s rest (by omega) h

/-- `decodeLengths` returns every symbol whose code word the bits begin with, if its length is tried. -/
theorem decodeLengths_complete (lens : List Nat) {s len c : Nat} (hs : lens[s]? = some len)
    (h0 : len ≠ 0) (hc : code lens s = some c) {w : List Bool} (hw : readCode len w = some (c, []))
    (rest : List Bool) : ∀ (k l : Nat), 1 ≤ l → l ≤ len → len < l + k →
    decodeLengths lens (w ++ rest) l k = some (s, rest)
  | 0, _, _, hl, hk => by omega
  | k + 1, l, h1, hl, hk => by
    have hfull := readCode_append len w c rest hw
    have ⟨hc1, hc2⟩ := code_bounds hs h0 hc
    simp only [decodeLengths]
    by_cases heq : l = len
    · subst heq
      rw [hfull]
      dsimp only
      rw [ite_eq_left hc1]
      have hidx : c - nextCode lens l = ((List.range s).filter fun n => lens[n]? == some l).length := by
        unfold code at hc
        rw [hs] at hc
        simp only [h0, ↓reduceIte, Option.some.injEq] at hc
        rw [filter_range_length]
        omega
      have hslt : s < lens.length := by
        have := (List.getElem?_eq_some_iff.mp hs).1
        exact this
      rw [symbolsOfLength_eq, hidx, filter_range_getElem? _ _ _ hslt (by simp [hs])]
    · have hll : l < len := by omega
      have hsplit := readCode_add l (len - l) (w ++ rest)
      rw [show l + (len - l) = len by omega, hfull] at hsplit
      cases hr1 : readCode l (w ++ rest) with
      | none => rw [hr1] at hsplit; simp at hsplit
      | some p =>
        obtain ⟨v1, r1⟩ := p
        rw [hr1] at hsplit
        simp only [Option.bind_some] at hsplit
        cases hr2 : readCode (len - l) r1 with
        | none => rw [hr2] at hsplit; simp at hsplit
        | some q =>
          obtain ⟨v2, r2⟩ := q
          rw [hr2] at hsplit
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsplit
          have hv2 := readCode_lt _ _ _ _ hr2
          have hshift := nextCode_shift lens l (len - l - 1)
          rw [show l + (len - l - 1) + 1 = len by omega, show len - l - 1 + 1 = len - l by omega]
            at hshift
          have hv1 : nextCode lens l + blCount lens l ≤ v1 := by
            refine Nat.le_of_not_lt fun hcon => ?_
            have : (v1 + 1) * 2 ^ (len - l) ≤ (nextCode lens l + blCount lens l) * 2 ^ (len - l) :=
              Nat.mul_le_mul_right _ (by omega)
            rw [Nat.add_mul, Nat.one_mul] at this
            omega
          dsimp only
          have hnone : (symbolsOfLength lens l)[v1 - nextCode lens l]? = none := by
            apply List.getElem?_eq_none
            rw [symbolsOfLength_length lens (by omega)]
            omega
          split
          · rw [hnone]
            exact decodeLengths_complete lens hs h0 hc hw rest k (l + 1) (by omega) (by omega)
              (by omega)
          · exact decodeLengths_complete lens hs h0 hc hw rest k (l + 1) (by omega) (by omega)
              (by omega)

/-- Decoding with a canonical code reads exactly a symbol's code word (§3.1). -/
theorem decodeSymbol_canonical {lens : List Nat} (hmax : ∀ l ∈ lens, l ≤ 15) (bs : List Bool)
    (s : Nat) (rest : List Bool) :
    decodeSymbol (.canonical lens) bs = some (s, rest) ↔
      ∃ len c w, lens[s]? = some len ∧ len ≠ 0 ∧ code lens s = some c ∧
        readCode len w = some (c, []) ∧ bs = w ++ rest := by
  constructor
  · exact decodeLengths_sound lens 15 1 bs s rest (by decide)
  · rintro ⟨len, c, w, hs, h0, hc, hw, rfl⟩
    have : len ≤ 15 := hmax len (List.mem_of_getElem? hs)
    exact decodeLengths_complete lens hs h0 hc hw rest 15 1 (by omega) (by omega) (by omega)

/-- The prefix property: no code word begins another (§3.1). -/
theorem code_prefixFree {lens : List Nat} (hmax : ∀ l ∈ lens, l ≤ 15) {a b la lb ca cb : Nat}
    {wa wb t : List Bool} (ha : lens[a]? = some la) (ha0 : la ≠ 0) (hca : code lens a = some ca)
    (hwa : readCode la wa = some (ca, [])) (hb : lens[b]? = some lb) (hb0 : lb ≠ 0)
    (hcb : code lens b = some cb) (hwb : readCode lb wb = some (cb, [])) (hab : wb = wa ++ t) :
    a = b ∧ t = [] := by
  have hda := (decodeSymbol_canonical hmax (wa ++ t) a t).mpr ⟨la, ca, wa, ha, ha0, hca, hwa, rfl⟩
  have hdb := (decodeSymbol_canonical hmax wb b []).mpr ⟨lb, cb, wb, hb, hb0, hcb, hwb, by simp⟩
  rw [hab, hda] at hdb
  simp only [Option.some.injEq, Prod.mk.injEq] at hdb
  exact hdb

/-- `ALPHABET_BITS`, the least `b` with `size ≤ 2 ^ b` (§3.4). -/
def alphabetBits (size : Nat) : Nat :=
  ((List.range (size + 1)).find? fun b => size ≤ 2 ^ b).getD size

/-- The code lengths of an alphabet, from (symbol, code length) pairs; the rest are zero (§3.4). -/
def lengthsOf (size : Nat) (assigned : List (Nat × Nat)) : List Nat :=
  (List.range size).map fun n => ((assigned.find? (·.1 == n)).map (·.2)).getD 0

/-- The symbols of a simple prefix code; one outside the alphabet or repeated is invalid (§3.4). -/
def readSimpleSymbols (size bits : Nat) : Nat → List Nat → List Bool → Option (List Nat × List Bool)
  | 0, syms, bs => some (syms, bs)
  | n + 1, syms, bs => do
    let (v, bs) ← readInt bits bs
    if size ≤ v ∨ syms.contains v then none
    else readSimpleSymbols size bits n (syms ++ [v]) bs

/-- `readSimpleSymbols` returns the symbols it started with and `n` more. -/
theorem readSimpleSymbols_length (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (bs : List Bool) (out : List Nat) (r : List Bool),
    readSimpleSymbols size bits n syms bs = some (out, r) → out.length = syms.length + n
  | 0, _, _, _, _, h => by simp [readSimpleSymbols] at h; simp [h.1]
  | n + 1, syms, bs, out, r, h => by
    simp only [readSimpleSymbols] at h
    cases hv : readInt bits bs with
    | none => simp [hv] at h
    | some p =>
      obtain ⟨v, bs'⟩ := p
      rw [hv] at h
      dsimp only [bind, Option.bind] at h
      split at h
      · simp at h
      · have := readSimpleSymbols_length size bits n _ _ out r h
        simp at this
        omega

/-- The symbols of a simple prefix code are distinct (§3.4). -/
theorem readSimpleSymbols_nodup (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (bs : List Bool) (out : List Nat) (r : List Bool), syms.Nodup →
    readSimpleSymbols size bits n syms bs = some (out, r) → out.Nodup
  | 0, _, _, _, _, hs, h => by
    simp only [readSimpleSymbols, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  | n + 1, syms, bs, out, r, hs, h => by
    simp only [readSimpleSymbols] at h
    cases hv : readInt bits bs with
    | none => rw [hv] at h; simp at h
    | some p =>
      obtain ⟨v, bs1⟩ := p
      rw [hv] at h
      dsimp only [bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i hnot
        have hv' : v ∉ syms := by
          intro hm
          exact hnot (Or.inr (by simpa using hm))
        refine readSimpleSymbols_nodup size bits n _ bs1 out r ?_ h
        refine List.pairwise_append.mpr ⟨hs, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        simp only [List.mem_singleton] at hb
        subst hb
        intro hab
        exact hv' (hab ▸ ha)

/-- A simple prefix code has 1 to 4 symbols. -/
theorem readSimple_count {size nsym : Nat} {bs bs' r : List Bool} {syms : List Nat}
    (h1 : readInt 2 bs = some (nsym, bs'))
    (h2 : readSimpleSymbols size (alphabetBits size) (nsym + 1) [] bs' = some (syms, r)) :
    1 ≤ syms.length ∧ syms.length ≤ 4 := by
  have := readInt_lt 2 bs nsym bs' h1
  have := readSimpleSymbols_length size _ (nsym + 1) [] bs' syms r h2
  simp at *
  omega

/-- A simple prefix code, after its first two bits (§3.4). -/
def readSimple (size : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) := do
  let (nsym, bs) ← readInt 2 bs
  let (syms, bs) ← readSimpleSymbols size (alphabetBits size) (nsym + 1) [] bs
  match syms with
  | [s] => some (.single s, bs)
  | [s1, s2] => some (.canonical (lengthsOf size [(s1, 1), (s2, 1)]), bs)
  | [s1, s2, s3] => some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 2)]), bs)
  | [s1, s2, s3, s4] => do
    let (treeSelect, bs) ← readInt 1 bs
    if treeSelect = 0 then
      some (.canonical (lengthsOf size [(s1, 2), (s2, 2), (s3, 2), (s4, 2)]), bs)
    else
      some (.canonical (lengthsOf size [(s1, 1), (s2, 2), (s3, 3), (s4, 3)]), bs)
  | _ => none

/-- The code for the code lengths of the code length alphabet: symbol, number of bits, code as
printed, which is its bits read as an integer (§3.5). -/
def codeLengthCodeLengthCode : List (Nat × Nat × Nat) :=
  [(0, 2, 0b00), (1, 4, 0b0111), (2, 3, 0b011), (3, 2, 0b10), (4, 2, 0b01), (5, 4, 0b1111)]

/-- No code of `codeLengthCodeLengthCode`, as read, begins with another. -/
theorem codeLengthCodeLengthCode_prefixFree :
    ∀ e ∈ codeLengthCodeLengthCode, ∀ f ∈ codeLengthCodeLengthCode,
      e ≠ f → e.2.1 ≤ f.2.1 → f.2.2 % 2 ^ e.2.1 ≠ e.2.2 := by
  decide +kernel

/-- The code lengths of code length symbols are 0 to 5, in 2 to 4 bits (§3.5). -/
theorem codeLengthCodeLengthCode_fields :
    ∀ e ∈ codeLengthCodeLengthCode, e.1 ≤ 5 ∧ 2 ≤ e.2.1 ∧ e.2.1 ≤ 4 := by
  decide +kernel

/-- One code length of a code length symbol, by `codeLengthCodeLengthCode` (§3.5). -/
def readCodeLengthCodeLength (bs : List Bool) : Option (Nat × List Bool) :=
  codeLengthCodeLengthCode.findSome? fun (sym, n, printed) =>
    match readInt n bs with
    | some (v, rest) => if v = printed then some (sym, rest) else none
    | none => none

/-- The order in which the code lengths of the code length alphabet appear (§3.5). -/
def codeLengthOrder : List Nat :=
  [1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15]

/-- The code lengths of the code length alphabet, with `sum` the sum of `32 >> code length` so far
(§3.5). -/
def readCodeLengthCodeLengths :
    List Nat → List (Nat × Nat) → Nat → List Bool → Option (List (Nat × Nat) × List Bool)
  | [], acc, _, bs => if (acc.filter (·.2 != 0)).length = 1 then some (acc, bs) else none
  | sym :: order, acc, sum, bs => do
    let (len, bs) ← readCodeLengthCodeLength bs
    let acc := acc ++ [(sym, len)]
    if len = 0 then readCodeLengthCodeLengths order acc sum bs
    else
      let sum := sum + (32 >>> len)
      if sum = 32 then some (acc, bs)
      else if 32 < sum then none
      else readCodeLengthCodeLengths order acc sum bs

/-- Reading code length code lengths ends with exactly one non-zero length, or on a non-zero length. -/
private theorem readCodeLengthCodeLengths_end : ∀ (order : List Nat) (acc : List (Nat × Nat))
    (sum : Nat) (bs : List Bool) (pairs : List (Nat × Nat)) (r : List Bool),
    readCodeLengthCodeLengths order acc sum bs = some (pairs, r) →
    (pairs.filter (·.2 != 0)).length = 1 ∨ ∃ p, pairs.getLast? = some p ∧ p.2 ≠ 0
  | [], _, _, _, pairs, _, h => by
    simp only [readCodeLengthCodeLengths] at h
    split at h
    · rename_i hone
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact Or.inl hone
    · simp at h
  | sym :: order, acc, sum, bs, pairs, r, h => by
    simp only [readCodeLengthCodeLengths] at h
    cases h1 : readCodeLengthCodeLength bs with
    | none => rw [h1] at h; simp at h
    | some q =>
      obtain ⟨len, bs1⟩ := q
      rw [h1] at h
      dsimp only [bind, Option.bind] at h
      split at h
      · exact readCodeLengthCodeLengths_end order _ _ bs1 pairs r h
      · rename_i h0
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact Or.inr ⟨(sym, len), by simp, h0⟩
        · split at h
          · simp at h
          · exact readCodeLengthCodeLengths_end order _ _ bs1 pairs r h

/-- With at least two non-zero code lengths, the last one read is non-zero (§3.5). -/
theorem readCodeLengthCodeLengths_last {order : List Nat} {bs r : List Bool}
    {pairs : List (Nat × Nat)} (h : readCodeLengthCodeLengths order [] 0 bs = some (pairs, r))
    (h2 : 2 ≤ (pairs.filter (·.2 != 0)).length) : ∃ p, pairs.getLast? = some p ∧ p.2 ≠ 0 := by
  rcases readCodeLengthCodeLengths_end _ _ _ _ _ _ h with hone | hlast
  · omega
  · exact hlast

/-- The code length code: one symbol if there is one non-zero length, otherwise canonical (§3.5). -/
def codeLengthCode (pairs : List (Nat × Nat)) : PrefixCode :=
  match pairs.filter (·.2 != 0) with
  | [(sym, _)] => .single sym
  | _ => .canonical (lengthsOf 18 pairs)

/-- The state while reading code lengths: the lengths so far, the previous non-zero length, and the
last repeat code with its count. -/
structure LengthState where
  lens : List Nat
  prev : Nat
  rep : Option (Nat × Nat)

/-- One code length symbol and its extra bits' value (§3.5, with erratum 5948). -/
def applyCodeLength (st : LengthState) (sym extra : Nat) : LengthState :=
  if sym < 16 then
    { lens := st.lens ++ [sym], prev := if sym = 0 then st.prev else sym, rep := none }
  else
    let len := if sym = 16 then st.prev else 0
    let mult := if sym = 16 then 4 else 8
    let old := match st.rep with
      | some (s, count) => if s = sym then count else 0
      | none => 0
    let new := if old = 0 then 3 + extra else mult * (old - 2) + (3 + extra)
    { lens := st.lens ++ List.replicate (new - old) len, prev := st.prev, rep := some (sym, new) }

/-- The sum of `32768 >> code length` over the non-zero code lengths (§3.5). -/
def lengthSum (lens : List Nat) : Nat :=
  (lens.map fun l => if l = 0 then 0 else 32768 >>> l).sum

/-- The loop of `readSymbolLengths`, with `out` the out-of-fuel result. -/
def readSymbolLengthsWith (size : Nat) (clc : PrefixCode) (out : Option (List Nat × List Bool)) :
    Nat → LengthState → List Bool → Option (List Nat × List Bool)
  | 0, _, _ => out
  | fuel + 1, st, bs =>
    if lengthSum st.lens = 32768 then
      some (st.lens ++ List.replicate (size - st.lens.length) 0, bs)
    else if st.lens.length = size then none
    else do
      let (sym, bs) ← decodeSymbol clc bs
      let (extra, bs) ← readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs
      let st := applyCodeLength st sym extra
      if size < st.lens.length then none
      else if 32768 < lengthSum st.lens then none
      else readSymbolLengthsWith size clc out fuel st bs

/-- The code lengths of an alphabet of `size` symbols, read with the code length code `clc` (§3.5). Fuel:
`size + 1` minus the lengths read (`readSymbolLengths_out`). -/
def readSymbolLengths (size : Nat) (clc : PrefixCode) :
    Nat → LengthState → List Bool → Option (List Nat × List Bool) :=
  readSymbolLengthsWith size clc none

/-- Each code length symbol adds at least one code length. -/
theorem applyCodeLength_length (st : LengthState) (sym extra : Nat) :
    st.lens.length + 1 ≤ (applyCodeLength st sym extra).lens.length := by
  have grow : ∀ (mult old e : Nat), (mult = 4 ∨ mult = 8) →
      old + 1 ≤ (if old = 0 then 3 + e else mult * (old - 2) + (3 + e)) := by
    intro mult old e hm
    rcases hm with rfl | rfl <;> split <;> omega
  unfold applyCodeLength
  by_cases h1 : sym < 16
  · simp [h1]
  · simp only [h1, ↓reduceIte, List.length_append, List.length_replicate]
    have := grow (if sym = 16 then 4 else 8)
      (match st.rep with | some (s, count) => if s = sym then count else 0 | none => 0) extra
      (by split <;> simp)
    omega

/-- While the fuel exceeds the lengths still to read, the out-of-fuel result is never reached. -/
theorem readSymbolLengthsWith_out (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
    (st : LengthState) (bs : List Bool), st.lens.length ≤ size → size < st.lens.length + fuel →
    ∀ out out', readSymbolLengthsWith size clc out fuel st bs =
      readSymbolLengthsWith size clc out' fuel st bs
  | 0, _, _, hle, hlt, _, _ => by omega
  | f + 1, st, bs, _, hlt, out, out' => by
    simp only [readSymbolLengthsWith]
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
        exact readSymbolLengthsWith_out size clc f _ bs2 (by omega) (by omega) out out'

/-- At the fuel `size + 1`, `readSymbolLengths` never reaches its out-of-fuel result. -/
theorem readSymbolLengths_out (size : Nat) (clc : PrefixCode) (bs : List Bool)
    (out : Option (List Nat × List Bool)) :
    readSymbolLengths size clc (size + 1) ⟨[], 8, none⟩ bs =
      readSymbolLengthsWith size clc out (size + 1) ⟨[], 8, none⟩ bs :=
  readSymbolLengthsWith_out size clc (size + 1) _ bs (by simp) (by simp) none out

/-- The sum of two lists of code lengths, one after the other, is the sum of their sums. -/
theorem lengthSum_append (a b : List Nat) : lengthSum (a ++ b) = lengthSum a + lengthSum b := by
  simp [lengthSum]

/-- Code lengths of zero add nothing to the sum. -/
theorem lengthSum_replicate_zero (k : Nat) : lengthSum (List.replicate k 0) = 0 := by
  simp [lengthSum]

/-- The symbols 0 and 17 and above add nothing to the sum. -/
private theorem applyCodeLength_sum_same {st : LengthState} {sym extra : Nat}
    (hs : sym = 0 ∨ 17 ≤ sym) :
    lengthSum (applyCodeLength st sym extra).lens = lengthSum st.lens := by
  unfold applyCodeLength
  rcases hs with rfl | hs
  · simp [lengthSum]
  · have h1 : ¬ sym < 16 := by omega
    have h2 : sym ≠ 16 := by omega
    simp only [h1, ↓reduceIte, h2, lengthSum_append, lengthSum_replicate_zero, Nat.add_zero]

/-- The code length symbol that brings the sum to 32768 is between 1 and 16 (§3.5). -/
theorem applyCodeLength_reaches {st : LengthState} {sym extra : Nat}
    (h0 : lengthSum st.lens ≠ 32768) (h : lengthSum (applyCodeLength st sym extra).lens = 32768) :
    1 ≤ sym ∧ sym ≤ 16 := by
  refine Nat.lt_or_ge sym 1 |>.elim (fun h1 => ?_) (fun h1 => ?_)
  · rw [applyCodeLength_sum_same (Or.inl (by omega))] at h
    exact absurd h h0
  · refine ⟨h1, Nat.le_of_not_lt fun h2 => ?_⟩
    rw [applyCodeLength_sum_same (Or.inr (by omega))] at h
    exact absurd h h0

/-- Once the sum is 32768, no more code length symbols are read, so the symbol that reached it is the
last (§3.5). -/
theorem readSymbolLengths_stop {size : Nat} {clc : PrefixCode} {st : LengthState} (fuel : Nat)
    (bs : List Bool) (h : lengthSum st.lens = 32768) :
    readSymbolLengths size clc (fuel + 1) st bs =
      some (st.lens ++ List.replicate (size - st.lens.length) 0, bs) := by
  simp [readSymbolLengths, readSymbolLengthsWith, h]

/-- The code length symbols read from one state and its bits to another, each read while the sum isn't yet
32768 (§3.5). -/
inductive LengthRun (clc : PrefixCode) : LengthState → List Bool → LengthState → List Bool → Prop
  | refl (st : LengthState) (bs : List Bool) : LengthRun clc st bs st bs
  | step {st st' : LengthState} {bs b1 b2 r : List Bool} {sym e : Nat} :
    lengthSum st.lens ≠ 32768 → decodeSymbol clc bs = some (sym, b1) →
    readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b1 = some (e, b2) →
    LengthRun clc (applyCodeLength st sym e) b2 st' r → LengthRun clc st bs st' r

/-- A successful run of code length symbols ends on the symbol that brings the sum to 32768, a symbol between
1 and 16, with nothing read after it and the remaining lengths zero (§3.5). -/
theorem readSymbolLengths_last {size : Nat} {clc : PrefixCode} : ∀ (fuel : Nat) (st : LengthState)
    (bs : List Bool) (lens : List Nat) (r : List Bool), lengthSum st.lens ≠ 32768 →
    readSymbolLengths size clc fuel st bs = some (lens, r) →
    ∃ (st1 : LengthState) (b1 : List Bool) (sym : Nat) (b2 : List Bool) (e : Nat),
      LengthRun clc st bs st1 b1 ∧
      decodeSymbol clc b1 = some (sym, b2) ∧
      readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) b2 = some (e, r) ∧
      lengthSum st1.lens ≠ 32768 ∧ lengthSum (applyCodeLength st1 sym e).lens = 32768 ∧
      1 ≤ sym ∧ sym ≤ 16 ∧
      lens = (applyCodeLength st1 sym e).lens ++
        List.replicate (size - (applyCodeLength st1 sym e).lens.length) 0
  | 0, _, _, _, _, _, h => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, bs, lens, r, hs, h => by
    simp only [readSymbolLengths, readSymbolLengthsWith, hs, ↓reduceIte] at h
    split at h
    · simp at h
    cases hd : decodeSymbol clc bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
      | none => rw [hx] at h; simp at h
      | some q =>
        obtain ⟨e, bs2⟩ := q
        rw [hx] at h
        dsimp only at h
        split at h
        · simp at h
        split at h
        · simp at h
        by_cases hreach : lengthSum (applyCodeLength st sym e).lens = 32768
        · cases f with
          | zero => simp [readSymbolLengthsWith] at h
          | succ g =>
            simp only [readSymbolLengthsWith, hreach, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hr := applyCodeLength_reaches hs hreach
            exact ⟨st, bs, sym, bs1, e, .refl st bs, hd, hx, hs, hreach, hr.1, hr.2, rfl⟩
        · obtain ⟨st1, b1, s1, b2, e1, hrun, rest⟩ := readSymbolLengths_last f _ bs2 lens r hreach h
          exact ⟨st1, b1, s1, b2, e1, .step hs hd hx hrun, rest⟩

/-- Each non-zero code length adds at most `32768 >> 1 = 16384` to the sum. -/
theorem lengthSum_le (lens : List Nat) : lengthSum lens ≤ 16384 * (lens.filter (· != 0)).length := by
  induction lens with
  | nil => simp [lengthSum]
  | cons l ls ih =>
    simp only [lengthSum, List.map_cons, List.sum_cons] at ih ⊢
    by_cases h : l = 0
    · simp [h]
      omega
    · have hpow : 2 ≤ 2 ^ l := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 1 ≤ l by omega)
        simpa using this
      have hterm : 32768 >>> l ≤ 16384 := by
        rw [Nat.shiftRight_eq_div_pow]
        calc 32768 / 2 ^ l ≤ 32768 / 2 := Nat.div_le_div_left hpow (by decide)
          _ = 16384 := by decide
      simp [h]
      omega

/-- The sum of `2 ^ (15 - k)` over the codes of lengths `1, …, l`. -/
private def lengthSumUpTo (lens : List Nat) : Nat → Nat
  | 0 => 0
  | l + 1 => lengthSumUpTo lens l + blCount lens (l + 1) * 2 ^ (15 - (l + 1))

private theorem blCount_cons (x : Nat) (xs : List Nat) (k : Nat) :
    blCount (x :: xs) k = blCount xs k + (if k ≠ 0 ∧ x = k then 1 else 0) := by
  unfold blCount
  by_cases hk : k = 0
  · simp [hk]
  · by_cases hx : x = k <;> simp [hk, hx]

private theorem lengthSumUpTo_cons (x : Nat) (xs : List Nat) : ∀ l,
    lengthSumUpTo (x :: xs) l =
      lengthSumUpTo xs l + (if 1 ≤ x ∧ x ≤ l then 2 ^ (15 - x) else 0)
  | 0 => by simp [lengthSumUpTo]; omega
  | l + 1 => by
    rw [lengthSumUpTo, lengthSumUpTo, lengthSumUpTo_cons x xs l, blCount_cons, Nat.add_mul]
    by_cases hx1 : x = l + 1
    · subst hx1
      rw [ite_eq_right (show ¬(1 ≤ l + 1 ∧ l + 1 ≤ l) by omega),
        ite_eq_left (show l + 1 ≠ 0 ∧ l + 1 = l + 1 by omega),
        ite_eq_left (show 1 ≤ l + 1 ∧ l + 1 ≤ l + 1 by omega)]
      omega
    · rw [ite_eq_right (show ¬(l + 1 ≠ 0 ∧ x = l + 1) by omega)]
      by_cases hx2 : 1 ≤ x ∧ x ≤ l
      · rw [ite_eq_left hx2, ite_eq_left (show 1 ≤ x ∧ x ≤ l + 1 by omega)]
        omega
      · rw [ite_eq_right hx2, ite_eq_right (show ¬(1 ≤ x ∧ x ≤ l + 1) by omega)]
        omega

private theorem lengthSumUpTo_le (l : Nat) (hl : l ≤ 15) :
    ∀ lens : List Nat, lengthSumUpTo lens l ≤ lengthSum lens
  | [] => by
    have : ∀ m, lengthSumUpTo [] m = 0 := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => simp [lengthSumUpTo, ih, blCount]
    simp [this]
  | x :: xs => by
    rw [lengthSumUpTo_cons]
    have := lengthSumUpTo_le l hl xs
    simp only [lengthSum, List.map_cons, List.sum_cons] at this ⊢
    split
    · rename_i hx
      have hshift : 32768 >>> x = 2 ^ (15 - x) := by
        rw [Nat.shiftRight_eq_div_pow, show 32768 = 2 ^ 15 by rfl,
          Nat.pow_div (by omega) (by omega)]
      rw [ite_eq_right (show ¬x = 0 by omega), hshift]
      omega
    · omega

private theorem nextCode_sum (lens : List Nat) : ∀ l, 1 ≤ l → l ≤ 15 →
    (nextCode lens l + blCount lens l) * 2 ^ (15 - l) = lengthSumUpTo lens l
  | 0, h, _ => by omega
  | 1, _, _ => by simp [nextCode, lengthSumUpTo, blCount]
  | l + 2, _, h => by
    have ih := nextCode_sum lens (l + 1) (by omega) (by omega)
    rw [show lengthSumUpTo lens (l + 2) =
      lengthSumUpTo lens (l + 1) + blCount lens (l + 2) * 2 ^ (15 - (l + 2)) from rfl, ← ih,
      show nextCode lens (l + 2) = (nextCode lens (l + 1) + blCount lens (l + 1)) <<< 1 from rfl,
      Nat.shiftLeft_eq, show 15 - (l + 1) = (15 - (l + 2)) + 1 by omega, Nat.pow_succ]
    grind

/-- Under Kraft's inequality, a used symbol's code is less than `2 ^ len`. -/
theorem code_lt_two_pow {lens : List Nat} (hkraft : lengthSum lens ≤ 32768)
    {s len c : Nat} (hs : lens[s]? = some len) (h0 : len ≠ 0) (hmax : len ≤ 15)
    (hc : code lens s = some c) : c < 2 ^ len := by
  have ⟨_, hc2⟩ := code_bounds hs h0 hc
  have hsum := nextCode_sum lens len (by omega) hmax
  have hle := lengthSumUpTo_le len hmax lens
  have hpow : 2 ^ len * 2 ^ (15 - len) = 32768 := by
    rw [← Nat.pow_add, show len + (15 - len) = 15 by omega]
  have : (nextCode lens len + blCount lens len) * 2 ^ (15 - len) ≤ 2 ^ len * 2 ^ (15 - len) := by
    omega
  have := Nat.le_of_mul_le_mul_right this (Nat.two_pow_pos _)
  omega

/-- The code lengths `readSymbolLengths` returns sum to 32768. -/
theorem readSymbolLengths_sum (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat) (st : LengthState)
    (bs : List Bool) (lens : List Nat) (r : List Bool),
    readSymbolLengths size clc fuel st bs = some (lens, r) → lengthSum lens = 32768
  | 0, _, _, _, _, h => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, bs, lens, r, h => by
    simp only [readSymbolLengths, readSymbolLengthsWith] at h
    split at h
    · rename_i hsum
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, lengthSum_append, lengthSum_replicate_zero, hsum]
    split at h
    · simp at h
    cases hd : decodeSymbol clc bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
      | none => rw [hx] at h; simp at h
      | some q =>
        obtain ⟨e, bs2⟩ := q
        rw [hx] at h
        dsimp only at h
        split at h
        · simp at h
        split at h
        · simp at h
        exact readSymbolLengths_sum size clc f _ bs2 lens r h

/-- A complex prefix code, after its first two bits, `HSKIP` (§3.5). -/
def readComplex (size hskip : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) := do
  let (pairs, bs) ← readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs
  let (lens, bs) ← readSymbolLengths size (codeLengthCode pairs) (size + 1) ⟨[], 8, none⟩ bs
  some (.canonical lens, bs)

/-- A complex prefix code has at least two non-zero code lengths (§3.5). -/
theorem readComplex_two {size hskip : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readComplex size hskip bs = some (c, r)) :
    ∃ lens, c = .canonical lens ∧ 2 ≤ (lens.filter (· != 0)).length := by
  unfold readComplex at h
  cases hp : readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs with
  | none => rw [hp] at h; simp at h
  | some p =>
    obtain ⟨pairs, bs1⟩ := p
    rw [hp] at h
    dsimp only [bind, Option.bind] at h
    cases hl : readSymbolLengths size (codeLengthCode pairs) (size + 1) ⟨[], 8, none⟩ bs1 with
    | none => rw [hl] at h; simp at h
    | some q =>
      obtain ⟨lens, bs2⟩ := q
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      refine ⟨lens, h.1.symm, ?_⟩
      have := readSymbolLengths_sum size _ _ _ _ lens bs2 hl
      have := lengthSum_le lens
      omega

/-- A prefix code over `size` symbols: first two bits 1 for simple, otherwise complex (§3.4). -/
def readPrefixCode (size : Nat) (bs : List Bool) : Option (PrefixCode × List Bool) := do
  let (hskip, bs) ← readInt 2 bs
  if hskip = 1 then readSimple size bs else readComplex size hskip bs

/-! ### The codes `readPrefixCode` returns fit the theorems -/

/-- A single-symbol code, or a canonical code with lengths at most 15 meeting Kraft's inequality. -/
def PrefixCode.Fits : PrefixCode → Prop
  | .single _ => True
  | .canonical lens => (∀ l ∈ lens, l ≤ 15) ∧ lengthSum lens ≤ 32768

private theorem sum_update_le (t : Nat → Nat) (s v : Nat) (g : Nat → Nat) : ∀ xs : List Nat,
    xs.Nodup → (xs.map fun n => t (if n = s then v else g n)).sum ≤ t v + (xs.map fun n => t (g n)).sum
  | [], _ => by simp
  | x :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    by_cases hx : x = s
    · subst hx
      have : (xs.map fun n => t (if n = x then v else g n)) = xs.map fun n => t (g n) :=
        List.map_congr_left fun n hn => by
          rw [ite_eq_right (show ¬n = x from fun h => hnd.1 (h ▸ hn))]
      rw [ite_eq_left rfl, this]
      omega
    · rw [ite_eq_right hx]
      have := sum_update_le t s v g xs hnd.2
      omega

private theorem lengthsOf_cons (size s v : Nat) (rest : List (Nat × Nat)) :
    lengthsOf size ((s, v) :: rest) =
      (List.range size).map fun n => if n = s then v else ((rest.find? (·.1 == n)).map (·.2)).getD 0 := by
  unfold lengthsOf
  apply List.map_congr_left
  intro n _
  by_cases h : s = n
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem lengthSum_lengthsOf (size : Nat) : ∀ assigned : List (Nat × Nat),
    lengthSum (lengthsOf size assigned) ≤ lengthSum (assigned.map (·.2))
  | [] => by simp [lengthSum, lengthsOf, List.map_const', List.sum_replicate_nat]
  | (s, v) :: rest => by
    have ih := lengthSum_lengthsOf size rest
    rw [lengthsOf_cons]
    unfold lengthSum at ih ⊢
    rw [List.map_map]
    unfold lengthsOf at ih
    rw [List.map_map] at ih
    have := sum_update_le (fun l => if l = 0 then 0 else 32768 >>> l) s v
      (fun n => ((rest.find? (·.1 == n)).map (·.2)).getD 0) (List.range size) (List.nodup_range)
    simp only [Function.comp_def] at this ih ⊢
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem lengthsOf_le (size m : Nat) (assigned : List (Nat × Nat))
    (h : ∀ p ∈ assigned, p.2 ≤ m) : ∀ x ∈ lengthsOf size assigned, x ≤ m := by
  intro x hx
  unfold lengthsOf at hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨n, _, rfl⟩ := hx
  cases hf : assigned.find? (·.1 == n) with
  | none => simp
  | some p => simpa using h p (List.mem_of_find?_eq_some hf)

private theorem fits_lengthsOf (size : Nat) (assigned : List (Nat × Nat))
    (hmax : ∀ p ∈ assigned, p.2 ≤ 15) (hsum : lengthSum (assigned.map (·.2)) ≤ 32768) :
    (PrefixCode.canonical (lengthsOf size assigned)).Fits :=
  ⟨lengthsOf_le size 15 assigned hmax, Nat.le_trans (lengthSum_lengthsOf size assigned) hsum⟩

/-- Every simple prefix code fits. -/
theorem readSimple_fits {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readSimple size bs = some (c, r)) : c.Fits := by
  unfold readSimple at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨nsym, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readSimpleSymbols size (alphabetBits size) (nsym + 1) [] bs1 with
    | none => rw [h2] at h; simp at h
    | some q =>
      obtain ⟨syms, bs2⟩ := q
      rw [h2] at h
      dsimp only at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        trivial
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact fits_lengthsOf _ _ (by simp) (by simp [lengthSum])
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact fits_lengthsOf _ _ (by simp) (by simp [lengthSum])
      · cases h3 : readInt 1 bs2 with
        | none => rw [h3] at h; simp at h
        | some t =>
          obtain ⟨ts, bs3⟩ := t
          rw [h3] at h
          dsimp only at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            exact fits_lengthsOf _ _ (by simp) (by simp [lengthSum])
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            exact fits_lengthsOf _ _ (by simp) (by simp [lengthSum])
      · simp at h

private theorem readCodeLengthCodeLength_le {bs r : List Bool} {v : Nat}
    (h : readCodeLengthCodeLength bs = some (v, r)) : v ≤ 5 := by
  unfold readCodeLengthCodeLength at h
  obtain ⟨⟨sym, n, printed⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  have hsym : sym ≤ 5 :=
    (show ∀ e ∈ codeLengthCodeLengthCode, e.1 ≤ 5 by decide) _ hmem
  simp only at hf
  split at hf
  · split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      omega
    · simp at hf
  · simp at hf

private theorem scale_32 : ∀ l < 6, l ≠ 0 → 32768 >>> l = 1024 * (32 >>> l) := by
  decide

private theorem readCodeLengthCodeLengths_fits : ∀ (order : List Nat) (acc : List (Nat × Nat))
    (sum : Nat) (bs : List Bool) (pairs : List (Nat × Nat)) (r : List Bool),
    readCodeLengthCodeLengths order acc sum bs = some (pairs, r) →
    (∀ p ∈ acc, p.2 ≤ 5) → lengthSum (acc.map (·.2)) = 1024 * sum →
    (∀ p ∈ pairs, p.2 ≤ 5) ∧
      ((pairs.filter (·.2 != 0)).length = 1 ∨ lengthSum (pairs.map (·.2)) = 32768)
  | [], acc, sum, bs, pairs, r, h, hacc, _ => by
    simp only [readCodeLengthCodeLengths] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨hacc, Or.inl (by assumption)⟩
    · simp at h
  | sym :: order, acc, sum, bs, pairs, r, h, hacc, hsum => by
    simp only [readCodeLengthCodeLengths] at h
    cases hl : readCodeLengthCodeLength bs with
    | none => rw [hl] at h; simp at h
    | some p =>
      obtain ⟨len, bs1⟩ := p
      rw [hl] at h
      dsimp only [bind, Option.bind] at h
      have hle := readCodeLengthCodeLength_le hl
      have hacc' : ∀ p ∈ acc ++ [(sym, len)], p.2 ≤ 5 := by
        intro p hp
        rcases List.mem_append.mp hp with hp | hp
        · exact hacc p hp
        · simp at hp; rw [hp]; exact hle
      have hsum' : lengthSum ((acc ++ [(sym, len)]).map (·.2)) =
          lengthSum (acc.map (·.2)) + (if len = 0 then 0 else 32768 >>> len) := by
        simp [lengthSum]
      split at h
      · rename_i h0
        refine readCodeLengthCodeLengths_fits order _ sum bs1 pairs r h hacc' ?_
        rw [hsum', hsum, ite_eq_left h0]
        omega
      · rename_i h0
        have hscale := scale_32 len (by omega) h0
        split at h
        · rename_i h32
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          refine ⟨hacc', Or.inr ?_⟩
          rw [hsum', hsum, ite_eq_right h0, hscale]
          omega
        · split at h
          · simp at h
          · refine readCodeLengthCodeLengths_fits order _ _ bs1 pairs r h hacc' ?_
            rw [hsum', hsum, ite_eq_right h0, hscale]
            omega

/-- Every code length code fits. -/
theorem codeLengthCode_fits {order : List Nat} {bs r : List Bool} {pairs : List (Nat × Nat)}
    (h : readCodeLengthCodeLengths order [] 0 bs = some (pairs, r)) :
    (codeLengthCode pairs).Fits := by
  obtain ⟨hmax, hone⟩ := readCodeLengthCodeLengths_fits order [] 0 bs pairs r h (by simp)
    (by simp [lengthSum])
  unfold codeLengthCode
  split
  · trivial
  · rename_i hnot
    rcases hone with hone | hsum
    · obtain ⟨⟨a, b⟩, hp⟩ : ∃ p, pairs.filter (·.2 != 0) = [p] := List.length_eq_one_iff.mp hone
      exact absurd hp (hnot a b)
    · exact fits_lengthsOf 18 pairs (fun p hp => Nat.le_trans (hmax p hp) (by decide))
        (by omega)

private theorem applyCodeLength_max (st : LengthState) (sym extra : Nat) (hp : st.prev ≤ 15)
    (hl : ∀ l ∈ st.lens, l ≤ 15) :
    (applyCodeLength st sym extra).prev ≤ 15 ∧ ∀ l ∈ (applyCodeLength st sym extra).lens, l ≤ 15 := by
  unfold applyCodeLength
  by_cases h1 : sym < 16
  · simp only [h1, ↓reduceIte, List.mem_append, List.mem_singleton]
    refine ⟨by split <;> omega, fun l hl' => ?_⟩
    rcases hl' with hl' | rfl
    · exact hl l hl'
    · omega
  · simp only [h1, ↓reduceIte, List.mem_append, List.mem_replicate]
    refine ⟨hp, fun l hl' => ?_⟩
    rcases hl' with hl' | ⟨_, rfl⟩
    · exact hl l hl'
    · split <;> omega

private theorem readSymbolLengths_max (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
    (st : LengthState) (bs : List Bool) (lens : List Nat) (r : List Bool),
    readSymbolLengths size clc fuel st bs = some (lens, r) →
    st.prev ≤ 15 → (∀ l ∈ st.lens, l ≤ 15) → ∀ l ∈ lens, l ≤ 15
  | 0, _, _, _, _, h, _, _ => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, bs, lens, r, h, hp, hl => by
    simp only [readSymbolLengths, readSymbolLengthsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      intro l hl'
      rcases List.mem_append.mp hl' with hl' | hl'
      · exact hl l hl'
      · rw [(List.mem_replicate.mp hl').2]; omega
    split at h
    · simp at h
    cases hd : decodeSymbol clc bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
      | none => rw [hx] at h; simp at h
      | some q =>
        obtain ⟨e, bs2⟩ := q
        rw [hx] at h
        dsimp only at h
        split at h
        · simp at h
        split at h
        · simp at h
        obtain ⟨hp', hl'⟩ := applyCodeLength_max st sym e hp hl
        exact readSymbolLengths_max size clc f _ bs2 lens r h hp' hl'

/-- Every complex prefix code fits. -/
theorem readComplex_fits {size hskip : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readComplex size hskip bs = some (c, r)) : c.Fits := by
  unfold readComplex at h
  cases hp : readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs with
  | none => rw [hp] at h; simp at h
  | some p =>
    obtain ⟨pairs, bs1⟩ := p
    rw [hp] at h
    dsimp only [bind, Option.bind] at h
    cases hl : readSymbolLengths size (codeLengthCode pairs) (size + 1) ⟨[], 8, none⟩ bs1 with
    | none => rw [hl] at h; simp at h
    | some q =>
      obtain ⟨lens, bs2⟩ := q
      rw [hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨readSymbolLengths_max size _ _ _ _ lens bs2 hl (by decide) (by simp),
        Nat.le_of_eq (readSymbolLengths_sum size _ _ _ _ lens bs2 hl)⟩

/-- Every prefix code `readPrefixCode` returns fits (§3.1). -/
theorem readPrefixCode_fits {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) : c.Fits := by
  unfold readPrefixCode at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨hskip, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · exact readSimple_fits h
    · exact readComplex_fits h

/-! ### The symbols of the codes `readPrefixCode` returns -/

/-- A code's symbols are those of an alphabet of `size` symbols. -/
def PrefixCode.Symbols (size : Nat) : PrefixCode → Prop
  | .single sym => sym < size
  | .canonical lens => lens.length = size

/-- A symbol decoded with a code over an alphabet of `size` symbols is below `size`. -/
theorem decodeSymbol_lt {size : Nat} {c : PrefixCode} {bs r : List Bool} {s : Nat}
    (hc : c.Symbols size) (h : decodeSymbol c bs = some (s, r)) : s < size := by
  cases c with
  | single sym =>
    simp only [decodeSymbol, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hc
  | canonical lens =>
    obtain ⟨len, _, _, hs, _⟩ := decodeLengths_sound lens 15 1 bs s r (by decide) h
    rw [← show lens.length = size from hc]
    exact (List.getElem?_eq_some_iff.mp hs).1

private theorem readSimpleSymbols_lt (size bits : Nat) : ∀ (n : Nat) (syms : List Nat)
    (bs : List Bool) (out : List Nat) (r : List Bool),
    readSimpleSymbols size bits n syms bs = some (out, r) → (∀ s ∈ syms, s < size) →
    ∀ s ∈ out, s < size
  | 0, _, _, _, _, h, hs => by
    simp only [readSimpleSymbols, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  | n + 1, syms, bs, out, r, h, hs => by
    simp only [readSimpleSymbols] at h
    cases hv : readInt bits bs with
    | none => rw [hv] at h; simp at h
    | some p =>
      obtain ⟨v, bs1⟩ := p
      rw [hv] at h
      dsimp only [bind, Option.bind] at h
      split at h
      · simp at h
      · rename_i hbad
        refine readSimpleSymbols_lt size bits n _ bs1 out r h fun s hmem => ?_
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hs s hmem
        · rw [List.mem_singleton.mp hmem]
          omega

private theorem lengthsOf_length (size : Nat) (assigned : List (Nat × Nat)) :
    (lengthsOf size assigned).length = size := by
  simp [lengthsOf]

private theorem readSimple_symbols {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readSimple size bs = some (c, r)) : c.Symbols size := by
  unfold readSimple at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨nsym, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    cases h2 : readSimpleSymbols size (alphabetBits size) (nsym + 1) [] bs1 with
    | none => rw [h2] at h; simp at h
    | some q =>
      obtain ⟨syms, bs2⟩ := q
      rw [h2] at h
      dsimp only at h
      have hlt := readSimpleSymbols_lt size _ _ [] bs1 syms bs2 h2 (by simp)
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact hlt _ (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact lengthsOf_length _ _
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact lengthsOf_length _ _
      · cases h3 : readInt 1 bs2 with
        | none => rw [h3] at h; simp at h
        | some t =>
          obtain ⟨ts, bs3⟩ := t
          rw [h3] at h
          dsimp only at h
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            exact lengthsOf_length _ _
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1]
            exact lengthsOf_length _ _
      · simp at h

private theorem readSymbolLengths_length (size : Nat) (clc : PrefixCode) : ∀ (fuel : Nat)
    (st : LengthState) (bs : List Bool) (lens : List Nat) (r : List Bool),
    readSymbolLengths size clc fuel st bs = some (lens, r) → st.lens.length ≤ size →
    lens.length = size
  | 0, _, _, _, _, h, _ => by simp [readSymbolLengths, readSymbolLengthsWith] at h
  | f + 1, st, bs, lens, r, h, hle => by
    simp only [readSymbolLengths, readSymbolLengthsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simp only [List.length_append, List.length_replicate]
      omega
    split at h
    · simp at h
    cases hd : decodeSymbol clc bs with
    | none => rw [hd] at h; simp at h
    | some p =>
      obtain ⟨sym, bs1⟩ := p
      rw [hd] at h
      dsimp only [bind, Option.bind] at h
      cases hx : readInt (if sym = 16 then 2 else if sym = 17 then 3 else 0) bs1 with
      | none => rw [hx] at h; simp at h
      | some q =>
        obtain ⟨e, bs2⟩ := q
        rw [hx] at h
        dsimp only at h
        split at h
        · simp at h
        split at h
        · simp at h
        rename_i hsize _
        exact readSymbolLengths_length size clc f _ bs2 lens r h (by omega)

/-- The symbols of a code `readPrefixCode` returns are those of its alphabet (§3.1). -/
theorem readPrefixCode_symbols {size : Nat} {bs r : List Bool} {c : PrefixCode}
    (h : readPrefixCode size bs = some (c, r)) : c.Symbols size := by
  unfold readPrefixCode at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨hskip, bs1⟩ := p
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · exact readSimple_symbols h
    · unfold readComplex at h
      cases hp : readCodeLengthCodeLengths (codeLengthOrder.drop hskip) [] 0 bs1 with
      | none => rw [hp] at h; simp at h
      | some q =>
        obtain ⟨pairs, bs2⟩ := q
        rw [hp] at h
        dsimp only [bind, Option.bind] at h
        cases hl : readSymbolLengths size (codeLengthCode pairs) (size + 1) ⟨[], 8, none⟩ bs2 with
        | none => rw [hl] at h; simp at h
        | some t =>
          obtain ⟨lens, bs3⟩ := t
          rw [hl] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact readSymbolLengths_length size _ _ _ _ lens bs3 hl (by simp)

end Brotli.Spec
