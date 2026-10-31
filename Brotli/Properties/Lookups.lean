import Brotli.Spec.Stream

/-!
# Lookups, defaults and bytes

Theorems about the spec's own modelling choices, which the RFC implies without asserting. The spec reads
tables with `[i]?`, which gives `none` out of range, and with `getD`, which gives a default out of range, and
it holds bytes as `Nat`. These theorems show none of that has any effect on a stream: in a stream whose earlier
fields read successfully, each lookup succeeds, no default is used, and every output value is a byte. So
`decode` rejects only by the rules it states.
-/

namespace Brotli.Properties

open Brotli.Spec

private theorem bind_some {α β : Type} {x : Option α} {f : α → Option β} {y : β}
    (h : (x >>= f) = some y) : ∃ a, x = some a ∧ f a = some y := by
  cases x with
  | none => simp [bind] at h
  | some a => exact ⟨a, rfl, h⟩

private theorem lookup_some {α : Type} {l : List α} {i : Nat} (h : i < l.length) :
    ∃ x, l[i]? = some x ∧ x ∈ l :=
  ⟨l[i], List.getElem?_eq_getElem h, List.getElem_mem h⟩

/-- Inside a list, `getD` doesn't depend on its default. -/
theorem getD_default {l : List Nat} {i : Nat} (h : i < l.length) (d d' : Nat) :
    l.getD i d = l.getD i d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-! ### What a meta-block header gives -/

private theorem readPrefixCodes_spec (size : Nat) : ∀ (n : Nat) (bs : List Bool)
    (codes : List PrefixCode) (r : List Bool), readPrefixCodes size n bs = some (codes, r) →
    codes.length = n ∧ ∀ c ∈ codes, c.Symbols size
  | 0, _, codes, _, h => by
    simp only [readPrefixCodes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp
  | n + 1, bs, codes, r, h => by
    simp only [readPrefixCodes] at h
    obtain ⟨⟨c, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨cs, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hl, hs⟩ := readPrefixCodes_spec size n bs1 cs bs2 h2
    refine ⟨by simp [hl], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact readPrefixCode_symbols h1
    · exact hs x hx

private theorem readContextModes_length : ∀ (n : Nat) (bs : List Bool) (modes : List Nat) (r : List Bool),
    readContextModes n bs = some (modes, r) → modes.length = n
  | 0, _, modes, _, h => by
    simp only [readContextModes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    rfl
  | n + 1, bs, modes, r, h => by
    simp only [readContextModes] at h
    obtain ⟨⟨m, bs1⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨ms, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [readContextModes_length n bs1 ms bs2 h2]

private theorem readTreesAndMap_spec {size : Nat} {bs r : List Bool} {n : Nat} {cmap : List Nat}
    (h : readTreesAndMap size bs = some ((n, cmap), r)) :
    cmap.length = size ∧ ∀ v ∈ cmap, v < n := by
  unfold readTreesAndMap at h
  obtain ⟨⟨k, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have hr := readVarLen_range h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    refine ⟨by simp, ?_⟩
    intro v hv
    rw [(List.mem_replicate.mp hv).2]
    omega
  · obtain ⟨⟨m, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, -⟩ := h
    exact ⟨readContextMap_length h2, readContextMap_lt (by omega) h2⟩

private theorem readBlockCategory_spec {bs r : List Bool} {c : BlockCategory}
    (h : readBlockCategory bs = some (c, r)) :
    c.Wf ∧ (2 ≤ c.n → c.countCode.Symbols blockCountAlphabetSize) := by
  unfold readBlockCategory at h
  obtain ⟨⟨n, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  have hr := readVarLen_range h1
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨⟨hr.1, hr.2, by simp only; omega⟩, by simp only; omega⟩
  obtain ⟨⟨tc, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cc, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨fc, bs4⟩, _, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨⟨hr.1, hr.2, fun _ => readPrefixCode_symbols h2⟩, fun _ => readPrefixCode_symbols h3⟩

/-- What a meta-block header read from a stream gives the lookups that follow it. -/
structure HeaderOk (m : MetaBlockHeader) : Prop where
  literal : m.literal.Wf
  insertCopy : m.insertCopy.Wf
  distance : m.distance.Wf
  literalCount : 2 ≤ m.literal.n → m.literal.countCode.Symbols blockCountAlphabetSize
  insertCopyCount : 2 ≤ m.insertCopy.n → m.insertCopy.countCode.Symbols blockCountAlphabetSize
  distanceCount : 2 ≤ m.distance.n → m.distance.countCode.Symbols blockCountAlphabetSize
  modes_length : m.contextModes.length = m.literal.n
  literalMap_length : m.literalMap.length = literalContextMapSize m.literal.n
  literalMap_lt : ∀ v ∈ m.literalMap, v < m.literalCodes.length
  literalCodes : ∀ c ∈ m.literalCodes, c.Symbols literalAlphabetSize
  insertCopyCodes_length : m.insertCopyCodes.length = m.insertCopy.n
  insertCopyCodes : ∀ c ∈ m.insertCopyCodes, c.Symbols insertCopyAlphabetSize
  distanceMap_length : m.distanceMap.length = distanceContextMapSize m.distance.n
  distanceMap_lt : ∀ v ∈ m.distanceMap, v < m.distanceCodes.length
  distanceCodes : ∀ c ∈ m.distanceCodes, c.Symbols (distanceAlphabetSize m.npostfix m.ndirect)

/-- Every header read from a stream meets `HeaderOk`. -/
theorem readMetaBlockHeader_ok {bs r : List Bool} {m : MetaBlockHeader}
    (h : readMetaBlockHeader bs = some (m, r)) : HeaderOk m := by
  unfold readMetaBlockHeader at h
  obtain ⟨⟨c1, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c2, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨c3, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨np, bs4⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨nd, bs5⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ms, bs6⟩, h6, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨tl, ml⟩, bs7⟩, h7, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨⟨td, md⟩, bs8⟩, h8, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cl, bs9⟩, h9, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨ci, bs10⟩, h10, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨cd, bs11⟩, h11, h⟩ := bind_some h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  obtain ⟨w1, k1⟩ := readBlockCategory_spec h1
  obtain ⟨w2, k2⟩ := readBlockCategory_spec h2
  obtain ⟨w3, k3⟩ := readBlockCategory_spec h3
  obtain ⟨l7, v7⟩ := readTreesAndMap_spec h7
  obtain ⟨l8, v8⟩ := readTreesAndMap_spec h8
  obtain ⟨l9, s9⟩ := readPrefixCodes_spec _ _ _ _ _ h9
  obtain ⟨l10, s10⟩ := readPrefixCodes_spec _ _ _ _ _ h10
  obtain ⟨l11, s11⟩ := readPrefixCodes_spec _ _ _ _ _ h11
  exact {
    literal := w1, insertCopy := w2, distance := w3
    literalCount := k1, insertCopyCount := k2, distanceCount := k3
    modes_length := readContextModes_length _ _ _ _ h6
    literalMap_length := l7
    literalMap_lt := by simpa only [l9] using v7
    literalCodes := s9
    insertCopyCodes_length := l10
    insertCopyCodes := s10
    distanceMap_length := l8
    distanceMap_lt := by simpa only [l11] using v8
    distanceCodes := s11 }

/-! ### Lookups never fail -/

/-- The context bytes of an output of bytes are bytes. -/
theorem contextBytes_lt {output : List Nat} (h : ∀ b ∈ output, b < 256) :
    (contextBytes output).1 < 256 ∧ (contextBytes output).2 < 256 := by
  match output, h with
  | [], _ => simp [contextBytes]
  | [p1], h => simpa [contextBytes] using h p1 (by simp)
  | p1 :: p2 :: _, h =>
    exact ⟨h p1 (by simp), h p2 (by simp)⟩

/-- A literal's context mode, map position and prefix code all exist, and the code is over the literal
alphabet. -/
theorem literal_lookups {m : MetaBlockHeader} {st : BlockState} {p1 : Nat} (p2 : Nat) (hm : HeaderOk m)
    (hs : st.Wf m.literal) (hp : p1 < 256) :
    ∃ mode index code, m.contextModes[st.types.cur]? = some mode ∧
      literalPrefixCodeIndex m.literalMap st.types.cur (contextId mode p1 p2) = some index ∧
      m.literalCodes[index]? = some code ∧ code.Symbols literalAlphabetSize := by
  obtain ⟨mode, h1, _⟩ := lookup_some (l := m.contextModes) (i := st.types.cur)
    (by rw [hm.modes_length]; exact hs.2.1)
  have hpos := literalIndex_lt hs.2.1 (contextId_lt mode p2 hp)
  rw [← hm.literalMap_length] at hpos
  obtain ⟨index, h2, h2m⟩ := lookup_some hpos
  obtain ⟨code, h3, h3m⟩ := lookup_some (hm.literalMap_lt index h2m)
  exact ⟨mode, index, code, h1, h2, h3, hm.literalCodes code h3m⟩

/-- A distance's map position and prefix code exist, and the code is over the distance alphabet. -/
theorem distance_lookups {m : MetaBlockHeader} {st : BlockState} (clen : Nat) (hm : HeaderOk m)
    (hs : st.Wf m.distance) :
    ∃ index code, distancePrefixCodeIndex m.distanceMap st.types.cur (distanceContextId clen) = some index ∧
      m.distanceCodes[index]? = some code ∧
      code.Symbols (distanceAlphabetSize m.npostfix m.ndirect) := by
  have hpos := distanceIndex_lt hs.2.1 (distanceContextId_lt clen)
  rw [← hm.distanceMap_length] at hpos
  obtain ⟨index, h2, h2m⟩ := lookup_some hpos
  obtain ⟨code, h3, h3m⟩ := lookup_some (hm.distanceMap_lt index h2m)
  exact ⟨index, code, h2, h3, hm.distanceCodes code h3m⟩

/-- An insert-and-copy element's prefix code exists, and it is over the alphabet. -/
theorem insertCopy_lookup {m : MetaBlockHeader} {st : BlockState} (hm : HeaderOk m)
    (hs : st.Wf m.insertCopy) :
    ∃ code, m.insertCopyCodes[st.types.cur]? = some code ∧ code.Symbols insertCopyAlphabetSize := by
  obtain ⟨code, h, hm'⟩ := lookup_some (l := m.insertCopyCodes) (i := st.types.cur)
    (by rw [hm.insertCopyCodes_length]; exact hs.2.1)
  exact ⟨code, h, hm.insertCopyCodes code hm'⟩

private theorem insertCopyCodes_total : ∀ c, c < 704 →
    ((insertCopyCodes c).any fun p => decide (p.1 < 24) && decide (p.2 < 24)) = true := by
  decide +kernel

/-- Every symbol of the insert-and-copy alphabet has a cell and rows in both length tables. -/
theorem insertCopy_tables {c : Nat} (h : c < insertCopyAlphabetSize) :
    ∃ ic cc ir cr, insertCopyCodes c = some (ic, cc) ∧ insertLengthCodes[ic]? = some ir ∧
      copyLengthCodes[cc]? = some cr := by
  have key := insertCopyCodes_total c h
  cases hc : insertCopyCodes c with
  | none => simp [hc] at key
  | some p =>
    obtain ⟨ic, cc⟩ := p
    simp only [hc, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at key
    obtain ⟨ir, h1, _⟩ := lookup_some (l := insertLengthCodes) (i := ic) (by
      have : insertLengthCodes.length = 24 := by decide
      omega)
    obtain ⟨cr, h2, _⟩ := lookup_some (l := copyLengthCodes) (i := cc) (by
      have : copyLengthCodes.length = 24 := by decide
      omega)
    exact ⟨ic, cc, ir, cr, rfl, h1, h2⟩

/-- Every symbol of the block count alphabet has a row in the table. -/
theorem blockCount_table {c : Nat} (h : c < blockCountAlphabetSize) :
    ∃ row, blockCountCodes[c]? = some row := by
  obtain ⟨row, h1, _⟩ := lookup_some (l := blockCountCodes) (i := c)
    (by rw [blockCountCodes_length]; exact h)
  exact ⟨row, h1⟩

/-- `ALPHABET_BITS` is always found, so the default of `alphabetBits` isn't used. -/
theorem alphabetBits_found (size : Nat) :
    ((List.range (size + 1)).find? fun b => size ≤ 2 ^ b).isSome = true := by
  rw [List.find?_isSome]
  exact ⟨size, List.mem_range.mpr (by omega), by simpa using Nat.le_of_lt Nat.lt_two_pow_self⟩

/-! ### The steps of a command, with the lookups gone -/

/-- A literal step: after the block switch, the only thing that can fail is decoding the literal. -/
theorem readLiterals_step {m : MetaBlockHeader} {n : Nat} {st st1 : BlockState} {output : List Nat}
    {bs bs1 : List Bool} (hm : HeaderOk m) (hs : st1.Wf m.literal) (hb : ∀ b ∈ output, b < 256)
    (h1 : nextElement m.literal st bs = some (st1, bs1)) :
    ∃ code, code.Symbols literalAlphabetSize ∧
      readLiterals m (n + 1) st output bs =
        (decodeSymbol code bs1 >>= fun (byte, bs2) => readLiterals m n st1 (byte :: output) bs2) := by
  obtain ⟨mode, index, code, h2, h3, h4, hc⟩ :=
    literal_lookups (contextBytes output).2 hm hs (contextBytes_lt hb).1
  refine ⟨code, hc, ?_⟩
  simp only [readLiterals]
  rw [h1]
  dsimp only [bind, Option.bind]
  rw [h2]
  dsimp only
  rw [h3]
  dsimp only
  rw [h4]

/-- A distance step: after the block switch, the only things that can fail are reading the distance and a
special symbol that resolves to zero or less. -/
theorem readCommandDistance_step {m : MetaBlockHeader} {st st1 : BlockState} {r : Distances}
    {c clen : Nat} {bs bs1 : List Bool} (hm : HeaderOk m) (hs : st1.Wf m.distance)
    (hi : implicitZeroDistance c = false) (h1 : nextElement m.distance st bs = some (st1, bs1)) :
    ∃ code, code.Symbols (distanceAlphabetSize m.npostfix m.ndirect) ∧
      readCommandDistance m st r c clen bs =
        (readDistance m.npostfix m.ndirect code r bs1 >>= fun ((dcode, d), bs2) =>
          some ((st1, dcode, d), bs2)) := by
  obtain ⟨index, code, h2, h3, hc⟩ := distance_lookups clen hm hs
  refine ⟨code, hc, ?_⟩
  unfold readCommandDistance
  simp only [hi, Bool.false_eq_true, ↓reduceIte]
  rw [h1]
  dsimp only [bind, Option.bind]
  rw [h2]
  dsimp only
  rw [h3]

/-! ### Distances -/

/-- Every distance is at least 1. -/
theorem distanceOf_pos {np nd dcode dextra d : Nat} {r : Distances}
    (h : distanceOf np nd r dcode dextra = some d) : 1 ≤ d := by
  unfold distanceOf at h
  split at h
  · dsimp only at h
    split at h
    · simp at h
    · rename_i hv
      simp only [Option.some.injEq] at h
      omega
  · split at h
    · rename_i h0 h1
      simp only [Option.some.injEq] at h
      omega
    · simp only [Option.some.injEq] at h
      rw [← h]
      exact Nat.le_add_left 1 _

/-- A command's distance is at least 1, the special symbols' rejection included. -/
theorem readCommandDistance_pos {m : MetaBlockHeader} {st : BlockState} {r : Distances}
    {c clen : Nat} {bs b : List Bool} {v : BlockState × Nat × Nat}
    (h : readCommandDistance m st r c clen bs = some (v, b)) : 1 ≤ v.2.2 := by
  unfold readCommandDistance at h
  split at h
  · obtain ⟨d, h1, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact distanceOf_pos h1
  · obtain ⟨⟨st1, bs1⟩, _, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨⟨⟨dcode, d⟩, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    unfold readDistance at h2
    obtain ⟨⟨sym, bs3⟩, _, h2⟩ := bind_some h2
    dsimp only at h2
    obtain ⟨⟨e, bs4⟩, _, h2⟩ := bind_some h2
    dsimp only at h2
    obtain ⟨d', h5, h2⟩ := bind_some h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨⟨-, rfl⟩, -⟩ := h2
    exact distanceOf_pos h5

/-- `copyBytes`, with its default as a parameter. -/
def copyBytesWith (dflt distance : Nat) : Nat → List Nat → List Nat
  | 0, output => output
  | n + 1, output => copyBytesWith dflt distance n (output.getD (distance - 1) dflt :: output)

/-- A copy from within the output never uses `copyBytes`' default: any other gives the same result. -/
theorem copyBytes_default {d : Nat} (dflt : Nat) (h1 : 1 ≤ d) : ∀ (n : Nat) (o : List Nat), d ≤ o.length →
    copyBytesWith dflt d n o = copyBytes d n o
  | 0, _, _ => rfl
  | n + 1, o, h => by
    simp only [copyBytesWith, copyBytes]
    rw [getD_default (l := o) (i := d - 1) (by omega) dflt 0]
    exact copyBytes_default dflt h1 n _ (by simp only [List.length_cons]; omega)

/-! ### Outputs are bytes -/

private theorem getD_byte {o : List Nat} (h : ∀ b ∈ o, b < 256) (i : Nat) : o.getD i 0 < 256 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : o[i]? with
  | none => simp
  | some v => simpa using h v (List.mem_of_getElem? hi)

private theorem copyBytes_bytes (d : Nat) : ∀ (n : Nat) (o : List Nat), (∀ b ∈ o, b < 256) →
    ∀ b ∈ copyBytes d n o, b < 256
  | 0, _, h => h
  | n + 1, o, h => by
    refine copyBytes_bytes d n _ ?_
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact getD_byte h _
    · exact h b hb

private theorem xor_byte {a b : Nat} (ha : a < 256) (hb : b < 256) : a ^^^ b < 256 :=
  Nat.xor_lt_two_pow (n := 8) ha hb

private theorem ferment_bytes (word : List Nat) (h : ∀ b ∈ word, b < 256) :
    (∀ b ∈ (ferment word).1, b < 256) ∧ ∀ b ∈ (ferment word).2, b < 256 := by
  match word, h with
  | [], _ => simp [ferment]
  | b :: rest, h =>
    have hb := h b (by simp)
    have hr : ∀ x ∈ rest, x < 256 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [ferment]
    split
    · refine ⟨?_, hr⟩
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      split
      · exact xor_byte hb (by decide)
      · exact hb
    · split
      · match rest, hr with
        | [], _ => simpa using hb
        | c :: rest', hr =>
          have hc := hr c (by simp)
          refine ⟨?_, fun x hx => hr x (List.mem_cons_of_mem _ hx)⟩
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hb
          · exact xor_byte hc (by decide)
      · match rest, hr with
        | [], _ => simpa using hb
        | [c], hr =>
          have hc := hr c (by simp)
          refine ⟨?_, by simp⟩
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl
          · exact hb
          · exact hc
        | c :: e :: rest', hr =>
          have hc := hr c (by simp)
          have he := hr e (by simp)
          refine ⟨?_, fun x hx => hr x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))⟩
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl
          · exact hb
          · exact hc
          · exact xor_byte he (by decide)

private theorem fermentAllWith_bytes : ∀ (fuel : Nat) (word : List Nat), (∀ b ∈ word, b < 256) →
    ∀ b ∈ fermentAllWith [] fuel word, b < 256
  | _, [], _ => by simp [fermentAllWith]
  | 0, _ :: _, _ => by simp [fermentAllWith]
  | fuel + 1, b :: word, h => by
    obtain ⟨h1, h2⟩ := ferment_bytes (b :: word) h
    simp only [fermentAllWith]
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · exact fermentAllWith_bytes fuel _ h2 x hx

private theorem applyElementary_bytes (e : ElementaryTransform) (word : List Nat)
    (h : ∀ b ∈ word, b < 256) : ∀ b ∈ applyElementary e word, b < 256 := by
  intro x hx
  cases e with
  | identity => exact h x hx
  | fermentFirst =>
    obtain ⟨h1, h2⟩ := ferment_bytes word h
    rcases List.mem_append.mp hx with hx | hx
    · exact h1 x hx
    · exact h2 x hx
  | fermentAll => exact fermentAllWith_bytes _ _ h x hx
  | omitFirst k => exact h x (List.mem_of_mem_drop hx)
  | omitLast k => exact h x (List.mem_of_mem_take hx)

private theorem transforms_bytes :
    ∀ t ∈ transforms, (∀ b ∈ bytes t.prefixString, b < 256) ∧ ∀ b ∈ bytes t.suffixString, b < 256 := by
  decide +kernel

private theorem DICT_byte (i : Nat) : DICT i < 256 := by
  unfold DICT
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

private theorem dictionaryWord_bytes {length distance maxDistance : Nat} {word : List Nat}
    (h : dictionaryWord length distance maxDistance = some word) : ∀ b ∈ word, b < 256 := by
  unfold dictionaryWord at h
  split at h
  · simp at h
  · obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hp, hs⟩ := transforms_bytes t (List.mem_of_getElem? ht)
    intro x hx
    simp only [applyTransform] at hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hp x hx
      · refine applyElementary_bytes _ _ ?_ x hx
        intro y hy
        obtain ⟨k, _, rfl⟩ := List.mem_map.mp hy
        exact DICT_byte _
    · exact hs x hx

/-! ### The invariant through a stream -/

/-- A block switch keeps a category's block types within its number of block types. -/
theorem nextElement_wf {c : BlockCategory} {st st' : BlockState} {bs r : List Bool}
    (hc : c.Wf) (hs : st.Wf c) (h : nextElement c st bs = some (st', r)) : st'.Wf c := by
  unfold nextElement at h
  split at h
  · split at h
    · simp at h
    · rename_i hn
      have h2 : 2 ≤ c.n := by omega
      obtain ⟨⟨t, bs1⟩, h1, h⟩ := bind_some h
      dsimp only at h
      obtain ⟨⟨cnt, bs2⟩, _, h⟩ := bind_some h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      unfold readBlockType at h1
      obtain ⟨⟨sym, bs3⟩, h3, h1⟩ := bind_some h1
      dsimp only at h1
      split at h1
      · simp at h1
      · simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, -⟩ := h1
        have hsym := decodeSymbol_lt (hc.2.2 h2) h3
        have hcur := nextBlockType_lt (hs.1 h2) hs.2.1 hsym
        refine ⟨fun _ => hs.2.1, hcur, ?_⟩
        intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hcur
        · exact hs.2.2 u hu
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact hs

/-- A meta-block's first block state meets `BlockState.Wf`. -/
theorem initial_wf {c : BlockCategory} (hc : c.Wf) : (BlockState.initial c).Wf c := by
  refine ⟨fun h2 => ?_, ?_, ?_⟩
  · simp only [BlockState.initial, initialBlockTypes]
    omega
  · simp only [BlockState.initial, initialBlockTypes]
    exact hc.1
  · intro t ht
    simp only [BlockState.initial, List.mem_singleton] at ht
    have := hc.1
    omega

/-- A state of a meta-block's data, as the stream reaches it. -/
structure CommandOk (m : MetaBlockHeader) (s : CommandState) : Prop where
  bytes : ∀ b ∈ s.output, b < 256
  produced : s.produced = s.output.length
  literal : s.literal.Wf m.literal
  insertCopy : s.insertCopy.Wf m.insertCopy
  distance : s.distance.Wf m.distance

/-- The state between meta-blocks, as the stream reaches it. -/
structure StreamOk (st : StreamState) : Prop where
  bytes : ∀ b ∈ st.output, b < 256
  produced : st.produced = st.output.length

/-- Reading literals keeps the block state `Wf` and the output bytes, adding `n` values. -/
theorem readLiterals_ok {m : MetaBlockHeader} (hm : HeaderOk m) : ∀ (n : Nat) (st : BlockState)
    (output : List Nat) (bs : List Bool) (st' : BlockState) (o : List Nat) (r : List Bool),
    st.Wf m.literal → (∀ b ∈ output, b < 256) → readLiterals m n st output bs = some (st', o, r) →
    st'.Wf m.literal ∧ (∀ b ∈ o, b < 256) ∧ o.length = output.length + n
  | 0, _, _, _, _, _, _, hs, hb, h => by
    simp only [readLiterals, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨hs, hb, rfl⟩
  | n + 1, st, output, bs, st', o, r, hs, hb, h => by
    simp only [readLiterals] at h
    obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨mode, _, h⟩ := bind_some h
    obtain ⟨index, _, h⟩ := bind_some h
    obtain ⟨code, hc, h⟩ := bind_some h
    obtain ⟨⟨byte, bs2⟩, h2, h⟩ := bind_some h
    dsimp only at h
    have hbyte : byte < 256 :=
      decodeSymbol_lt (hm.literalCodes code (List.mem_of_getElem? hc)) h2
    have hb' : ∀ b ∈ byte :: output, b < 256 := by
      intro b hm'
      rcases List.mem_cons.mp hm' with rfl | hm'
      · exact hbyte
      · exact hb b hm'
    obtain ⟨w, bb, hl⟩ := readLiterals_ok hm n _ _ bs2 st' o r (nextElement_wf hm.literal hs h1) hb' h
    refine ⟨w, bb, ?_⟩
    simp only [List.length_cons] at hl
    omega

private theorem readCommandDistance_wf {m : MetaBlockHeader} {st : BlockState} {r : Distances}
    {c clen : Nat} {bs b : List Bool} {v : BlockState × Nat × Nat} (hm : HeaderOk m)
    (hs : st.Wf m.distance) (h : readCommandDistance m st r c clen bs = some (v, b)) :
    v.1.Wf m.distance := by
  unfold readCommandDistance at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  · obtain ⟨⟨st1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨_, _, h⟩ := bind_some h
    obtain ⟨⟨⟨dcode, d⟩, bs2⟩, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact nextElement_wf hm.distance hs h1

/-- A backward copy reads from within the output: its distance is from 1 to the output's length. -/
theorem copy_in_range {w d : Nat} {s : CommandState} (hp : s.produced = s.output.length) (h1 : 1 ≤ d)
    (h : isDictionaryReference d (maxBackwardDistance w s.produced) = false) :
    1 ≤ d ∧ d ≤ s.output.length := by
  have := (backwardDistance_iff.mp h).2
  omega

private theorem copyCommand_ok {w clen dcode d : Nat} {m : MetaBlockHeader} {s s' : CommandState}
    (hs : CommandOk m s) (h : copyCommand w s clen dcode d = some s') : CommandOk m s' := by
  unfold copyCommand at h
  dsimp only at h
  split at h
  · obtain ⟨word, h1, h⟩ := bind_some h
    split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      refine ⟨?_, ?_, hs.literal, hs.insertCopy, hs.distance⟩
      · intro b hb
        rcases List.mem_append.mp hb with hb | hb
        · exact dictionaryWord_bytes h1 b (List.mem_reverse.mp hb)
        · exact hs.bytes b hb
      · simp only [List.length_append, List.length_reverse, hs.produced]
        omega
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      obtain ⟨hlen⟩ : ∃ _ : (copyBytes d clen s.output).length = s.output.length + clen, True := by
        have key : ∀ (n : Nat) (o : List Nat), (copyBytes d n o).length = o.length + n := by
          intro n
          induction n with
          | zero => intro o; rfl
          | succ n ih =>
            intro o
            simp only [copyBytes, ih, List.length_cons]
            omega
        exact ⟨key _ _, trivial⟩
      refine ⟨copyBytes_bytes d clen _ hs.bytes, ?_, hs.literal, hs.insertCopy, hs.distance⟩
      simp only [hlen, hs.produced]

/-- A command keeps a meta-block's state `CommandOk`. -/
theorem readCommand_ok {w : Nat} {m : MetaBlockHeader} {s s' : CommandState} {bs r : List Bool}
    (hm : HeaderOk m) (hs : CommandOk m s) (h : readCommand w m s bs = some (s', r)) : CommandOk m s' := by
  unfold readCommand at h
  obtain ⟨⟨ic, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨code, _, h⟩ := bind_some h
  obtain ⟨⟨⟨c, ilen, clen⟩, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp at h
  obtain ⟨⟨lit, out, bs3⟩, h3, h⟩ := bind_some h
  dsimp only at h
  have wI := nextElement_wf hm.insertCopy hs.insertCopy h1
  obtain ⟨wL, bb, hl⟩ := readLiterals_ok hm _ _ _ _ _ _ _ hs.literal hs.bytes h3
  have hmid : CommandOk m
      { s with
        insertCopy := ic, literal := lit, output := out,
        produced := s.produced + ilen, remaining := s.remaining - ilen } :=
    ⟨bb, by simp only [hs.produced, hl], wL, wI, hs.distance⟩
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hmid
  · obtain ⟨⟨⟨dst, dcode, d⟩, bs4⟩, h4, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨s2, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have wD := readCommandDistance_wf hm hs.distance h4
    refine copyCommand_ok ?_ h5
    exact ⟨hmid.bytes, hmid.produced, hmid.literal, hmid.insertCopy, wD⟩

/-- Every state a meta-block's commands reach is a `CommandOk`, so the lookups and copies of the next command
are in range. -/
theorem readCommands_ok (w : Nat) {m : MetaBlockHeader} (hm : HeaderOk m) : ∀ (fuel : Nat)
    (s s' : CommandState) (bs r : List Bool), CommandOk m s →
    readCommands w m fuel s bs = some (s', r) → CommandOk m s'
  | 0, _, _, _, _, _, h => by simp [readCommands, readCommandsWith] at h
  | f + 1, s, s', bs, r, hs, h => by
    simp only [readCommands, readCommandsWith] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hs
    obtain ⟨⟨s1, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    exact readCommands_ok w hm f s1 s' bs1 r (readCommand_ok hm hs h1) h

private theorem readCompressed_ok {w mlen : Nat} {st st' : StreamState} {bs r : List Bool}
    (hs : StreamOk st) (h : readCompressed w st mlen bs = some (st', r)) : StreamOk st' := by
  unfold readCompressed at h
  obtain ⟨⟨m, bs1⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨s, bs2⟩, h2, h⟩ := bind_some h
  dsimp only at h
  have hm := readMetaBlockHeader_ok h1
  have ho := readCommands_ok w hm _ _ s _ bs2
    ⟨hs.bytes, hs.produced, initial_wf hm.literal, initial_wf hm.insertCopy, initial_wf hm.distance⟩ h2
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨ho.bytes, ho.produced⟩
  · simp at h

private theorem readBytes_ok : ∀ (n : Nat) (bs : List Bool) (bytes : List Nat) (r : List Bool),
    readBytes n bs = some (bytes, r) → bytes.length = n ∧ ∀ b ∈ bytes, b < 256
  | 0, _, bytes, _, h => by
    simp only [readBytes, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    simp
  | n + 1, bs, bytes, r, h => by
    simp only [readBytes] at h
    obtain ⟨⟨b, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    obtain ⟨⟨rest, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hl, hb⟩ := readBytes_ok n bs1 rest bs2 h2
    refine ⟨by simp [hl], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · simpa using readInt_lt 8 _ _ _ h1
    · exact hb x hx

private theorem readMetaBlockBody_ok {w : Nat} {st st' : StreamState} {islast : Bool} {bs r : List Bool}
    (hs : StreamOk st) (h : readMetaBlockBody w st islast bs = some (st', r)) : StreamOk st' := by
  unfold readMetaBlockBody at h
  obtain ⟨⟨mn, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨bs2, _, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact hs
  obtain ⟨⟨mlen, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨iu, bs3⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨bs4, _, h⟩ := bind_some h
    obtain ⟨⟨bytes, bs5⟩, h5, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨hl, hb⟩ := readBytes_ok _ _ _ _ h5
    refine ⟨?_, ?_⟩
    · intro b hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hb b (List.mem_reverse.mp hm)
      · exact hs.bytes b hm
    · simp only [List.length_append, List.length_reverse, hl, hs.produced]
      omega
  · exact readCompressed_ok hs h

private theorem readMetaBlock_ok {w : Nat} {st st' : StreamState} {last : Bool} {bs r : List Bool}
    (hs : StreamOk st) (h : readMetaBlock w st bs = some ((st', last), r)) : StreamOk st' := by
  unfold readMetaBlock at h
  obtain ⟨⟨islast, bs1⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · obtain ⟨⟨st1, bs2⟩, h2, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact readMetaBlockBody_ok hs h2
  obtain ⟨⟨ie, bs2⟩, _, h⟩ := bind_some h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact hs
  · obtain ⟨⟨st1, bs3⟩, h3, h⟩ := bind_some h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact readMetaBlockBody_ok hs h3

/-- Every state between meta-blocks holds bytes, with `produced` its length. -/
theorem readMetaBlocks_ok (w : Nat) : ∀ (fuel : Nat) (st st' : StreamState) (bs r : List Bool),
    StreamOk st → readMetaBlocks w fuel st bs = some (st', r) → StreamOk st'
  | 0, _, _, _, _, _, h => by simp [readMetaBlocks, readMetaBlocksWith] at h
  | f + 1, st, st', bs, r, hs, h => by
    simp only [readMetaBlocks, readMetaBlocksWith] at h
    obtain ⟨⟨⟨st1, last⟩, bs1⟩, h1, h⟩ := bind_some h
    dsimp only at h
    have hs1 := readMetaBlock_ok hs h1
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact hs1
    · exact readMetaBlocks_ok w f st1 st' bs1 r hs1 h

private theorem toUInt8_toNat : ∀ x, x < 256 → (Nat.toUInt8 x).toNat = x := by
  decide +kernel

private theorem map_toUInt8 : ∀ l : List Nat, (∀ b ∈ l, b < 256) →
    (l.map Nat.toUInt8).map UInt8.toNat = l
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons]
    rw [toUInt8_toNat x (h x (by simp)), map_toUInt8 l fun b hb => h b (List.mem_cons_of_mem _ hb)]

/-- The meta-blocks of a valid stream end with every output value a byte and `produced` the output's length,
and `Nat.toUInt8` truncates nothing: the bytes `decode` returns are exactly those values. -/
theorem decode_bytes {input y : List UInt8} (h : decode input = some y) :
    ∃ wbits bs st r, readWBITS (bits input) = some (wbits, bs) ∧
      readMetaBlocks (windowSize wbits) (bs.length + 1) ⟨[], 0, initialDistances⟩ bs = some (st, r) ∧
      (∀ b ∈ st.output, b < 256) ∧ st.produced = st.output.length ∧
      y.map UInt8.toNat = st.output.reverse := by
  unfold decode at h
  obtain ⟨⟨wbits, bs⟩, h1, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨st, bs1⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_some h
  simp only [Option.some.injEq] at h
  have hs := readMetaBlocks_ok _ _ _ _ _ _ ⟨by simp, rfl⟩ h2
  refine ⟨wbits, bs, st, bs1, h1, h2, hs.bytes, hs.produced, ?_⟩
  rw [← h]
  exact map_toUInt8 _ fun b hb => hs.bytes b (List.mem_reverse.mp hb)

/-! ### The other defaults -/

/-- With bytes for `p1` and `p2`, the lookup tables' default isn't used. -/
theorem Lut_default {p : Nat} (h : p < 256) (d : Nat) :
    Lut0.getD p d = Lut0.getD p 0 ∧ Lut1.getD p d = Lut1.getD p 0 ∧ Lut2.getD p d = Lut2.getD p 0 := by
  obtain ⟨h0, h1, h2⟩ := Lut_lengths
  exact ⟨getD_default (by omega) d 0, getD_default (by omega) d 0, getD_default (by omega) d 0⟩

/-- `inverseMoveToFrontFrom`, with its default as a parameter. -/
def inverseMoveToFrontFromWith (dflt : Nat) : List Nat → List Nat → List Nat
  | _, [] => []
  | mtf, index :: v =>
    let value := mtf.getD index dflt
    value :: inverseMoveToFrontFromWith dflt (value :: mtf.eraseIdx index) v

/-- With every index inside `mtf`, the transform never uses its default: any other gives the same result. -/
theorem inverseMoveToFront_default (dflt : Nat) : ∀ (v mtf : List Nat), (∀ x ∈ v, x < mtf.length) →
    inverseMoveToFrontFromWith dflt mtf v = inverseMoveToFrontFrom mtf v
  | [], _, _ => rfl
  | index :: v, mtf, h => by
    have hi : index < mtf.length := h index (by simp)
    simp only [inverseMoveToFrontFromWith, inverseMoveToFrontFrom]
    rw [getD_default hi dflt 0]
    congr 1
    refine inverseMoveToFront_default dflt v _ ?_
    intro x hx
    have := h x (List.mem_cons_of_mem _ hx)
    simp only [List.length_cons, List.length_eraseIdx_of_lt hi]
    omega

/-- A context map read with NTREES of at most 256 hands the transform the values it read, all below 256, the
length of `mtf`, so `inverseMoveToFront_default` applies. -/
theorem readContextMap_indexes {size ntrees : Nat} {bs r : List Bool} {cmap : List Nat}
    (h0 : 0 < ntrees) (h1 : ntrees ≤ 256) (h : readContextMap size ntrees bs = some (cmap, r)) :
    ∃ rlemax b1 code b2 vals b3 imtf,
      readRLEMAX bs = some (rlemax, b1) ∧
      readPrefixCode (contextMapAlphabetSize ntrees rlemax) b1 = some (code, b2) ∧
      readContextMapValues rlemax code (size + 1) size b2 = some (vals, b3) ∧
      readInt 1 b3 = some (imtf, r) ∧
      (∀ x ∈ vals, x < (List.range 256).length) ∧
      cmap = if imtf = 0 then vals else inverseMoveToFront vals := by
  unfold readContextMap at h
  obtain ⟨⟨rlemax, bs1⟩, h2, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨code, bs2⟩, h3, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨vals, bs3⟩, h4, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨⟨imtf, bs4⟩, h5, h⟩ := bind_some h
  dsimp only at h
  have hlt := readContextMapValues_lt h0 (readPrefixCode_symbols h3) _ _ _ _ _ h4
  have hin : ∀ x ∈ vals, x < (List.range 256).length := by
    intro x hx
    have := hlt x hx
    simp only [List.length_range]
    omega
  generalize hf : (if imtf = 0 then vals else inverseMoveToFront vals) = final at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rlemax, bs1, code, bs2, vals, bs3, imtf, h2, h3, h4, h5, hin, hf.symm⟩
  · simp at h

private theorem NWORDS_pos : ∀ length, length < 25 → 4 ≤ length → 0 < NWORDS length := by
  decide +kernel

private theorem NDBITS_in_range {length : Nat} (h : length ≤ 24) : length < NDBITS.length := by
  rw [NDBITS_length]
  omega

/-- In a dictionary reference, `NDBITS`' default isn't used, the index is below `NWORDS`, and every byte of
the base word lies inside the dictionary, so `DICT`'s default isn't used. -/
theorem dictionary_in_range {length wordId k : Nat} (h1 : 4 ≤ length) (h2 : length ≤ 24) (hk : k < length) :
    (∀ d d', NDBITS.getD length d = NDBITS.getD length d') ∧
      wordId % NWORDS length < NWORDS length ∧
      (wordOffset length (wordId % NWORDS length) + k) / 32 < dictLines.length := by
  have hw := NWORDS_pos length (by omega) h1
  have hlt := Nat.mod_lt wordId hw
  refine ⟨fun d d' => getD_default (NDBITS_in_range h2) d d', hlt, ?_⟩
  have hle := wordOffset_le length (by omega) h1
  obtain ⟨hsize, hlines⟩ := DICTSIZE_eq
  rw [hsize] at hle
  unfold wordOffset at hle ⊢
  have hmul : (wordId % NWORDS length + 1) * length ≤ NWORDS length * length :=
    Nat.mul_le_mul_right length hlt
  rw [Nat.add_mul, Nat.one_mul] at hmul
  have hsum : DOFFSET length + wordId % NWORDS length * length + k < 122784 := by omega
  apply Nat.div_lt_of_lt_mul
  omega

end Brotli.Properties
