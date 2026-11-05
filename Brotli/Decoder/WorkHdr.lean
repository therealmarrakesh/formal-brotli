import Brotli.Decoder.Progress
import Brotli.Decoder.CostHeader

/-!
# The work of a header

A header step's work, counted by `stepHW`, is paid for by the bits the header reads. Most steps do little and read at least
one bit. The few that do much (building a table, zero-filling a context map, the inverse move-to-front transform) or read
nothing are paid for in advance: a potential on the places of the header read in order holds what is still to do once the
bits that settle its size are read, and rises only when bits are read.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Tables -/

/-- A table's work, with its lengths complete: at most seven for each symbol and 1265 more, and for a context map's code
the map's zeros as read and as transformed, and its three lists of 256 bytes. -/
theorem tableDoneW_le {st : Hd} {single : Bool} {sym : UInt64} (ha : TableArgs st.size st.head st.next single sym)
    (har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32) :
    tableDoneW st single ≤ 7 * st.size.toNat + 1265 +
      (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) := by
  unfold tableDoneW
  have hb : ∀ t : ByteArray, t.size % 2 = 0 ∧ t.size + 2672 < 2 ^ 32 →
      (if single then buildSingleW else buildFastW t st.head st.next) ≤ 7 * st.size.toNat + 1264 := by
    intro t ht
    cases hs : single with
    | true =>
      show buildSingleW ≤ _
      have := buildSingleW_le
      omega
    | false =>
      show buildFastW t st.head st.next ≤ _
      obtain ⟨c, hf⟩ := ha
      obtain ⟨L, hc, hlen, hl⟩ := hf.canon hs
      have hC := hf.complete
      rw [hc] at hC
      have h704 := hf.small
      have h1 := buildFastW_le (⟨hC, by omega, hl, hf.hsz, hf.nsz, ht.1, ht.2⟩ : BuildArgs t st.head st.next L)
      have h2 := longCount_le L
      omega
  cases hr : st.role with
  | map =>
    simp only [↓reduceIte]
    have := zbW_le 256
    have := hb (ByteArray.emptyWithCapacity soloCap) ⟨rfl, by decide⟩
    omega
  | type =>
    simp only [reduceCtorEq, ↓reduceIte]
    have := hb st.d.arena har
    omega
  | count =>
    simp only [reduceCtorEq, ↓reduceIte]
    have := hb st.d.arena har
    omega
  | codes =>
    simp only [reduceCtorEq, ↓reduceIte]
    have := hb st.d.arena har
    omega

/-- A finished code length code's table's work: its eighteen lengths are at most five, so it has no long code words. -/
theorem clTableW_le {st : Hd} (h : ∃ acc, ClDone st acc) : clTableW st ≤ 927 := by
  have h18 : (USize.ofNat 18).toNat = 18 := usize_ofNat' (by decide)
  obtain ⟨acc, hd⟩ := h
  unfold clTableW
  by_cases h1 : st.clNz = 1
  · rw [ite_eq_left h1]
    have := buildSingleW_le
    omega
  · rw [ite_eq_right h1]
    by_cases hn : (USize.ofNat 18).toNat ≤ st.clLens.size
    · rw [dite_eq_left hn]
      have b1 := buildLensW_short (hn := hn) (⟨hd.complete h1, by rw [h18]; decide, rfl, by decide⟩ :
        LensArgs ByteArray.empty st.clLens (USize.ofNat 18))
        (fun l hl => Nat.le_trans (hd.short h1 l hl) (show 5 ≤ 8 by decide))
      rw [h18] at b1
      omega
    · rw [dite_eq_right hn]
      omega

/-! ### The potential

On the header's places read in order. A number of block types or trees not yet read counts as 0, so the potential rises
by what that number brings when it is read. -/

/-- The rate at which a header's bits pay for its work: the most a bit pays for is the literal context map's zeros that a
literal category's number of block types brings, 128 for each type, when that number takes 11 bits. -/
def hdrRate : Nat := 2980

/-- A bound on the work of zero-filling `k` bytes (`zbW_le`). -/
def zb (k : Nat) : Nat := k + k / 65536 + 1

/-- What a context map of `S` values holds before its number of trees: its zeros, and what the trees' number, the run
length's bits and the code's bits do not pay of the values a code gives without reading. -/
def mapPre (S : Nat) : Nat := 2 * S + 5268

/-- What follows the second context map: the groups' steps, their arrays' zeros and the header's last step. -/
def afterD (nI tL tD : Nat) : Nat := 3 * tL + zb (4 * nI) + 4 + 3 * nI + zb (4 * tD) + 4 + 3 * tD + 4

/-- What follows the first context map. -/
def afterL (nI nD tL : Nat) : Nat := mapPre (4 * nD) + zb (4 * tL) + smallMax + 1 + afterD nI tL 0

/-- What is still to do from the context modes on, with the numbers of block types known so far. -/
def beforeMaps (nL nI nD : Nat) : Nat := 3 + mapPre (64 * nL) + 1 + afterL nI nD 0

/-- The potential once category `i` is known to have `n` block types. -/
def catPot (g : Gh) : Cat → Nat → Nat
  | .L, n => beforeMaps n 0 0
  | .I, n => beforeMaps g.m.literal.n n 0
  | .D, n => beforeMaps g.m.literal.n g.m.insertCopy.n n

/-- What a context map's last step does to the next group's array, and to the arena's reservation. -/
def mapFin (g : Gh) (isL : Bool) : Nat := if isL then 1 else zb (4 * g.treesL) + smallMax + 1

/-- What follows a context map of `t` trees. -/
def mapAfter (g : Gh) (isL : Bool) (t : Nat) : Nat :=
  if isL then afterL g.m.insertCopy.n g.m.distance.n t else afterD g.m.insertCopy.n g.treesL t

/-- From a context map's last bit on: the check that every tree occurs, and what follows. -/
def imtfTail (g : Gh) (isL : Bool) (t : Nat) : Nat := t + 4 + mapFin g isL + mapAfter g isL t

/-- From a context map's code on: what follows its values, and what the code's five bits or more do not pay of the values a
code that reads no bits gives, every value written as read and transformed, and flagged, with the code's table. -/
def mapOwner (g : Gh) (isL : Bool) (t : Nat) : Nat := imtfTail g isL t + max 3 (2 * mapSize g isL + 9 * t + 1436 - 5 * hdrRate)

/-- From a context map's run length on: what its code holds, less what the run length's bit pays. -/
def mapOwnerR (g : Gh) (isL : Bool) (t : Nat) : Nat := imtfTail g isL t + max 3 (2 * mapSize g isL + 9 * t + 1439 - 6 * hdrRate)

/-- From a group's next code on. -/
def codesPot (g : Gh) : CK → Nat → Nat
  | .L, left => afterD g.m.insertCopy.n left g.treesD
  | .I, left => 3 * left + zb (4 * g.treesD) + 8 + 3 * g.treesD
  | .D, left => 3 * left + 4

/-- At most what a code's table's step does for its owner: for a context map, the map's zeros as read and as transformed,
and its three lists of 256 bytes. -/
def ownerX (g : Gh) : Owner → Nat
  | .map isL _ _ => 770 +zb (mapSize g isL) + zb (mapSize g isL)
  | _ => 0

/-- From where a code's owner goes on to. -/
def ownerPot (g : Gh) : Owner → Nat
  | .type i n => catPot g i n
  | .count i n _ => catPot g i n
  | .map isL t _ => mapOwner g isL t
  | .codes k _ left => codesPot g k left

/-- A code's table's step, with a refill and a round of the stream's loop, besides what it does for its owner. -/
def symsTable (n : Nat) : Nat := 7 * n + 1268

/-- The code length code's last step: its table, and the lists' links emptied. -/
def clDone : Nat := 963

/-- At least the bits still to read before a code length code ends with two symbols or more: each length adds at most
four to the 32 it fills for each bit it takes. -/
def clMulti (sum : Nat) : Nat := (32 - sum + 3) / 4

/-- At least the bits still to read before a code length code ends with one symbol: each length left takes two bits. -/
def clSingle (order : List Nat) : Nat := 2 * order.length

/-- What the lengths still to read pay for, at the rate less what each read costs: a code length code ending with two
symbols or more leads to lengths that each take a bit, and one ending with one symbol may lead to lengths that take no
bits, each prepaid. -/
def clensPot (n : Nat) (order : List Nat) (sum : Nat) : Nat :=
  max (clDone + symsTable n - (hdrRate - 3) * clMulti sum) (clDone + symsTable n + 4 * n - (hdrRate - 3) * clSingle order)

/-- What a code's lengths still to read prepay: with a code length code of one symbol, the lengths read without bits. -/
def symsPre (clc : PrefixCode) (n len : Nat) : Nat :=
  match clc with
  | .single _ => 4 * (n - len)
  | .canonical _ => 0

/-- The potential of a header's place. A code's lengths carry its table's work, paid by the bits of its code length
code. -/
def hpot (g : Gh) : HPhase → Nat
  | .cat i => catPot g i 0
  | .code o _ => ownerX g o + ownerPot g o
  | .clens o n order _ sum => clensPot n order sum + ownerX g o + ownerPot g o
  | .syms o n clc ls => symsPre clc n ls.lens.length + symsTable n + ownerX g o + ownerPot g o
  | .first i n _ _ => catPot g i n
  | .np => beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n
  | .modes _ _ => beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n
  | .trees isL => mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0
  | .rlemax isL t => 770 + zb (mapSize g isL) + zb (mapSize g isL) + mapOwnerR g isL t
  | .vals isL t r code _ left =>
    if left = 0 then 3 + imtfTail g isL t
    else match runOf r code with
      | some _ => 2 * left + 2 * t + 23 + imtfTail g isL t
      | none => 3 + imtfTail g isL t
  | .imtf isL t _ => imtfTail g isL t
  | .codes k _ left => codesPot g k left

/-- A bound on a header step's work, with a round for its refill and its round of the stream's loop, by where it goes;
the bytes its refill takes pay for themselves. -/
def hcost (g : Gh) : HPhase → HPhase → Nat
  | .cat _, _ => 3
  | .code _ _, .clens .. => 22
  | .code o n, _ => 7 * n + 1301 + ownerX g o
  | .clens .., .syms .. => clDone
  | .clens .., _ => 3
  | .syms _ _ _ ls, .syms _ _ _ ls' => ls'.lens.length - ls.lens.length + 3
  | .syms o n _ _, _ => symsTable n + ownerX g o
  | .first .., _ => 3
  | .np, _ => 260
  | .modes .., _ => 3
  | .trees _, .rlemax .. => 3
  | .trees isL, _ => 3 + zb (mapSize g isL) + mapFin g isL
  | .rlemax .., _ => 3
  | .vals _ t r code _ left, .vals _ _ _ _ _ left' =>
    match runOf r code with | some _ => 2 * left + 2 * t + 12 | none => left - left' + 268
  | .vals .., _ => 3
  | .imtf isL t _, _ => t + 4 + mapFin g isL
  | .codes _ _ (_ + 1), _ => 3
  | .codes .L _ 0, _ => zb (4 * g.m.insertCopy.n) + 4
  | .codes .I _ 0, _ => zb (4 * g.treesD) + 4
  | .codes .D _ 0, _ => 4

/-- A context map's values left, at the places reading them. -/
def vleft : HPhase → Nat
  | .vals _ _ _ _ _ left => left
  | _ => 0

/-- A prefix code's alphabet, at the places reading one. -/
def psize : HPhase → Nat
  | .code _ n => n
  | .clens _ n .. => n
  | .syms _ n .. => n
  | _ => 0

/-! ### What reads pay -/

theorem hdrRate_eq : hdrRate = 2980 := rfl

private theorem pow_pay : ∀ n, n < 8 → 1 ≤ n → 256 * 2 ^ n + 3 ≤ 2980 * (4 + n) := by decide

/-- A number of block types or trees pays for 128 for each, and 3. -/
theorem varLen_pay {bs b : List Bool} {v : Nat} (h : readVarLen bs = some (v, b)) :
    128 * v + 3 + hdrRate * b.length ≤ hdrRate * bs.length := by
  rw [hdrRate_eq]
  unfold readVarLen at h
  cases h1 : readInt 1 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨first, bs1⟩ := p
    have l1 := readInt_length _ _ _ _ h1
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      omega
    · cases h2 : readInt 3 bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨n, bs2⟩ := q
        have l2 := readInt_length _ _ _ _ h2
        have n8 : n < 8 := readInt_lt _ _ _ _ h2
        rw [h2] at h
        dsimp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          omega
        · rename_i hn0
          cases h3 : readInt n bs2 with
          | none => rw [h3] at h; simp at h
          | some r =>
            obtain ⟨x, bs3⟩ := r
            have l3 := readInt_length _ _ _ _ h3
            have x8 := readInt_lt _ _ _ _ h3
            rw [h3] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [Nat.shiftLeft_eq, Nat.one_mul]
            have key := pow_pay n n8 (by omega)
            have hm : 2980 * bs.length = 2980 * bs3.length + 2980 * (4 + n) := by
              rw [← Nat.mul_add]
              congr 1
              omega
            rw [hm]
            generalize 2 ^ n = P at x8 key
            omega

private theorem trees_key : ∀ k, k < 8 → 18 * 2 ^ (k + 1) + 11838 ≤ 2980 * (4 + k) := by decide

/-- A number of two trees or more, in `4 + k` bits, pays for the map's code's share of the values it may give without
reading. -/
private theorem max_sub (a b : Nat) : max 3 (a - b) ≤ 3 ∨ max 3 (a - b) + b ≤ a := by omega

private theorem trees_pay {S Z v Fn A0 Av P K C B M : Nat} (hS : S ≤ 16384) (hZ : Z = S + 1)
    (hA : Av ≤ A0 + 8 * v) (hvk : v ≤ P) (hkey : 18 * P + 11838 ≤ K) (hm : B = C + K)
    (hM : M ≤ 3 ∨ M + 6 * 2980 ≤ 2 * S + 9 * v + 1439) :
    3 + (770 + Z + Z + ((v + 4 + Fn + Av) + M)) + C ≤ 2 * S + 5268 + Fn + A0 + B := by
  omega

/-- A code length code's length fills at most four of its 32 for each bit it takes, and takes two bits or more. -/
theorem clcl_fill {bs r : List Bool} {v : Nat} (h : readCodeLengthCodeLength bs = some (v, r)) :
    r.length + 2 ≤ bs.length ∧ (if v = 0 then 0 else 32 >>> v) ≤ 4 * (bs.length - r.length) := by
  unfold readCodeLengthCodeLength at h
  obtain ⟨⟨sym, n, printed⟩, hmem, hf⟩ := List.exists_of_findSome?_eq_some h
  simp only at hf
  split at hf
  · rename_i hr
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      have := readInt_length _ _ _ _ hr
      simp only [codeLengthCodeLengthCode, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
        simp only [↓reduceIte, reduceCtorEq] <;> omega
    · simp at hf
  · simp at hf

/-- A simple prefix code takes its symbol count's two bits, and its first symbol's bits. -/
theorem simpleChain_takes {size bits : Nat} {bs r : List Bool} {c : PrefixCode} (h : simpleChain size bits bs = some (c, r)) :
    r.length + 2 + bits ≤ bs.length := by
  unfold simpleChain at h
  cases h1 : readInt 2 bs with
  | none => rw [h1] at h; cases h
  | some p =>
    obtain ⟨nsym, bs1⟩ := p
    rw [h1] at h
    have l1 := readInt_length _ _ _ _ h1
    have h' : simpleC1 size bits nsym bs1 = some (c, r) := h
    unfold simpleC1 at h'
    cases h2 : readInt bits bs1 with
    | none => rw [h2] at h'; cases h'
    | some q =>
      obtain ⟨s1, bs2⟩ := q
      rw [h2] at h'
      have l2 := readInt_length _ _ _ _ h2
      have h'' : (if size ≤ s1 then none else simpleN1 size bits nsym s1 bs2) = some (c, r) := h'
      split at h''
      · cases h''
      · have := faith_le (faith_simpleN1 size bits nsym s1) h''
        omega

/-- A number of two block types or trees or more takes four bits or more: four and `n`, for a number up to `2 ^ (n + 1)`. -/
theorem varLen_long {bs b : List Bool} {v : Nat} (h : readVarLen bs = some (v, b)) (hv : 2 ≤ v) :
    ∃ n, n < 8 ∧ bs.length = b.length + 4 + n ∧ v ≤ 2 ^ (n + 1) := by
  unfold readVarLen at h
  cases h1 : readInt 1 bs with
  | none => rw [h1] at h; simp at h
  | some p =>
    obtain ⟨first, bs1⟩ := p
    have l1 := readInt_length _ _ _ _ h1
    rw [h1] at h
    dsimp only [bind, Option.bind] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
    · cases h2 : readInt 3 bs1 with
      | none => rw [h2] at h; simp at h
      | some q =>
        obtain ⟨n, bs2⟩ := q
        have l2 := readInt_length _ _ _ _ h2
        have n8 : n < 8 := readInt_lt _ _ _ _ h2
        rw [h2] at h
        dsimp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨0, by decide, by omega, by decide⟩
        · rename_i hn0
          cases h3 : readInt n bs2 with
          | none => rw [h3] at h; simp at h
          | some r =>
            obtain ⟨x, bs3⟩ := r
            have l3 := readInt_length _ _ _ _ h3
            have x8 := readInt_lt _ _ _ _ h3
            rw [h3] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨n, n8, by omega, ?_⟩
            rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.pow_succ]
            omega

/-- A context map's run is shorter than twice two to the bits that give it. -/
theorem mapSym_runLen {rlemax : Nat} {code : PrefixCode} {bs r : List Bool} {v n : Nat}
    (h : mapSym rlemax code bs = some ((v, n), r)) : n < 2 ^ (bs.length - r.length + 1) := by
  unfold mapSym at h
  cases hd : decodeSymbol code bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨sym, bs1⟩ := p
    rw [hd] at h
    have hb1 := decodeSymbol_le hd
    dsimp only [bind, Option.bind] at h
    cases hv : contextMapValue rlemax sym with
    | some w =>
      rw [hv] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨_, rfl⟩, _⟩ := h
      exact Nat.one_lt_two_pow (by omega)
    | none =>
      rw [hv] at h
      cases hx : readInt sym bs1 with
      | none => rw [hx] at h; cases h
      | some q =>
        rw [hx] at h
        have l := readInt_length _ _ _ _ hx
        have hq := readInt_lt _ _ _ _ hx
        have h' : some ((0, (1 <<< sym) + q.1), q.2) = some ((v, n), r) := h
        simp only [Option.some.injEq, Prod.mk.injEq] at h'
        obtain ⟨⟨_, rfl⟩, rfl⟩ := h'
        rw [Nat.shiftLeft_eq, Nat.one_mul]
        have hp : 2 ^ (sym + 1) ≤ 2 ^ (bs.length - q.2.length + 1) := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.pow_succ] at hp
        omega

/-- A run of up to 16384 values shorter than twice two to its `B` bits, with a bit or more, is paid for at the rate. -/
theorem run_pay {f B : Nat} (hf : f ≤ 16384) (hr : f < 2 ^ (B + 1)) (hB : 1 ≤ B) : f + 268 ≤ 2980 * B := by
  by_cases h5 : B ≤ 5
  · have : 2 ^ (B + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
    have : (2 : Nat) ^ 6 = 64 := rfl
    omega
  · omega

/-- A code's first two bits pay for the start of its code length code. -/
theorem clensPot_start {n k : Nat} (hn : n ≤ 704) (hk : k < 4) : 22 + clensPot n (codeLengthOrder.drop k) 0 ≤ 2980 * 2 := by
  have hl : (codeLengthOrder.drop k).length = 18 - k := by rw [List.length_drop]; rfl
  unfold clensPot clMulti clSingle symsTable clDone hdrRate
  rw [hl]
  omega

/-- A length read of a code length code, of `B` bits, that fills `f` of its 32. -/
theorem clensPot_step {n x sum f B : Nat} {rest : List Nat} (hB : 2 ≤ B) (hf : f ≤ 4 * B) :
    3 + clensPot n rest (sum + f) ≤ clensPot n (x :: rest) sum + 2980 * B := by
  unfold clensPot clMulti clSingle hdrRate
  simp only [List.length_cons]
  omega

/-- The length that fills a code length code with two symbols or more, of `B` bits. -/
theorem clensPot_fin {n x sum B : Nat} {rest : List Nat} (hf : 32 - sum ≤ 4 * B) :
    clDone + symsTable n ≤ clensPot n (x :: rest) sum + 2980 * B := by
  unfold clensPot clMulti clSingle hdrRate
  omega

/-- A code length code that ends with one symbol. -/
theorem clensPot_nil {n sum : Nat} : clDone + symsTable n + 4 * n ≤ clensPot n [] sum := by
  unfold clensPot clSingle
  simp only [List.length_nil, Nat.mul_zero, Nat.sub_zero]
  omega

theorem symsPre_le (clc : PrefixCode) (n len : Nat) : symsPre clc n len ≤ 4 * (n - len) := by
  cases clc <;> simp only [symsPre] <;> omega

/-- A code length code filled by a length that is not its first is not a single symbol's. -/
theorem codeLengthCode_canon {acc : List (Nat × Nat)} {sum x v : Nat} (hs : lengthSum (acc.map (·.2)) = 1024 * sum)
    (hv : v ≠ 0) (hf : sum + (32 >>> v) = 32) : ∃ L, codeLengthCode (acc ++ [(x, v)]) = .canonical L := by
  unfold codeLengthCode
  have hfil : (acc ++ [(x, v)]).filter (·.2 != 0) = acc.filter (·.2 != 0) ++ [(x, v)] := by
    rw [List.filter_append]
    simp [hv]
  rw [hfil]
  cases ha : acc.filter (·.2 != 0) with
  | nil =>
    exfalso
    have hle := lengthSum_le (acc.map (·.2))
    have hlen : ((acc.map (·.2)).filter (· != 0)).length = (acc.filter (·.2 != 0)).length := by
      rw [List.filter_map, List.length_map]
      rfl
    rw [hlen, ha] at hle
    have : sum = 0 := by simp at hle; omega
    subst this
    have : 32 >>> v < 32 := by
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_self (by decide) (Nat.one_lt_two_pow hv)
    omega
  | cons q qs =>
    cases qs with
    | nil => exact ⟨_, rfl⟩
    | cons q' qs' => exact ⟨_, rfl⟩

/-- A code length symbol of a canonical code takes a bit or more. -/
theorem lenSym_takes {L : List Nat} {bs r : List Bool} {v : Nat × Nat} (h : lenSym (.canonical L) bs = some (v, r)) :
    r.length < bs.length := by
  unfold lenSym at h
  cases hd : decodeSymbol (.canonical L) bs with
  | none => rw [hd] at h; cases h
  | some p =>
    obtain ⟨s, b1⟩ := p
    rw [hd] at h
    have l1 := decodeLengths_reads L bs 15 1 (Nat.le_refl _) s b1 hd
    change (readInt (if s = 16 then 2 else if s = 17 then 3 else 0) b1 >>= _) = _ at h
    cases hx : readInt (if s = 16 then 2 else if s = 17 then 3 else 0) b1 with
    | none => rw [hx] at h; cases h
    | some q =>
      rw [hx] at h
      have l2 := readInt_length _ _ _ _ hx
      have h' : some ((s, q.1), q.2) = some (v, r) := h
      simp only [Option.some.injEq, Prod.mk.injEq] at h'
      rw [← h'.2]
      omega

theorem catPot_le (g : Gh) (i : Cat) (v : Nat) : catPot g i v ≤ catPot g i 0 + 128 * v := by
  cases i <;> simp only [catPot, beforeMaps, afterL, afterD, mapPre, zb] <;> omega

theorem mapAfter_le (g : Gh) (isL : Bool) (v : Nat) : mapAfter g isL v ≤ mapAfter g isL 0 + 8 * v := by
  cases isL <;> simp only [mapAfter, afterL, afterD, zb, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem hpot_catNext (g : Gh) (i : Cat) (c : BlockCategory) : hpot (g.setCat i c) (catNextPhase i) = catPot g i c.n := by
  cases i <;> rfl

theorem hpot_mapNext (g : Gh) (isL : Bool) (t : Nat) (m : List Nat) :
    hpot (g.setMap isL t m) (mapNextPhase (g.setMap isL t m) isL) = mapAfter g isL t := by
  cases isL with
  | true =>
    simp only [Gh.setMap, mapNextPhase, hpot, mapSize, mapFin, mapAfter, afterL, distanceContextMapSize, Bool.false_eq_true,
      ↓reduceIte]
    omega
  | false => rfl

/-- A code's owner, when it is no context map, holds what the code's table leads to. -/
theorem hpot_owner_le (g : Gh) (o : Owner) (c : PrefixCode) (ho : ∀ isL t r, o ≠ .map isL t r) :
    hpot g (ownerPlace g o c) ≤ ownerPot g o := by
  cases o with
  | type i n => exact Nat.le_of_eq (by simp only [ownerPlace, hpot, ownerX, ownerPot, Nat.zero_add])
  | count i n tc => exact Nat.le_refl _
  | codes k done left => exact Nat.le_refl _
  | map isL t r => exact absurd rfl (ho isL t r)

/-- A context map's code holds what its table leads to, less what five of its bits pay: a code that reads no bits gives
the map's values without reading. -/
theorem hpot_owner_map (g : Gh) (isL : Bool) (t r : Nat) (c : PrefixCode) :
    hpot g (ownerPlace g (.map isL t r) c) + 7 * (t + 16) + 1301 ≤ mapOwner g isL t + 5 * hdrRate := by
  simp only [ownerPlace, hpot, mapOwner]
  split
  · omega
  · cases runOf r c with
    | some v => dsimp only; omega
    | none => dsimp only; omega

/-- A code's owner holds what a code with two symbols or more leads to. -/
theorem hpot_owner_canon (g : Gh) (o : Owner) (L : List Nat) : hpot g (ownerPlace g o (.canonical L)) ≤ ownerPot g o := by
  cases o with
  | type i n => exact Nat.le_of_eq (by simp only [ownerPlace, hpot, ownerX, ownerPot, Nat.zero_add])
  | count i n tc => exact Nat.le_refl _
  | codes k done left => exact Nat.le_refl _
  | map isL t r =>
    simp only [ownerPlace, hpot, ownerPot, mapOwner, runOf]
    split <;> omega

/-- An alphabet of two symbols or more takes a bit or more. -/
theorem alphabetBits_pos {n : Nat} (h : 2 ≤ n) : 1 ≤ alphabetBits n := by
  have := (alphabetBits_spec n).1
  refine Nat.le_of_not_lt fun h0 => ?_
  rw [Nat.lt_one_iff.mp h0] at this
  simp at this
  omega

theorem hcost_code_owner (g : Gh) (o : Owner) (n : Nat) (c : PrefixCode) :
    hcost g (.code o n) (ownerPlace g o c) = 7 * n + 1301 + ownerX g o := by
  cases o <;> rfl

theorem hcost_syms_owner (g : Gh) (o : Owner) (n : Nat) (clc : PrefixCode) (ls : LengthState) (c : PrefixCode) :
    hcost g (.syms o n clc ls) (ownerPlace g o c) = symsTable n + ownerX g o := by
  cases o <;> rfl

private theorem grow_aux (old e mult : Nat) (hm : mult = 4 ∨ mult = 8) :
    1 ≤ (if old = 0 then 3 + e else mult * (old - 2) + (3 + e)) - old := by
  rcases hm with rfl | rfl <;> split <;> omega

/-- A code length symbol adds at least one length. -/
theorem applyCodeLength_grow (ls : LengthState) (s e : Nat) :
    ∃ l, (applyCodeLength ls s e).lens = ls.lens ++ l ∧ 1 ≤ l.length := by
  unfold applyCodeLength
  split
  · exact ⟨[s], rfl, by simp⟩
  · dsimp only
    refine ⟨_, rfl, ?_⟩
    rw [List.length_replicate]
    exact grow_aux _ _ _ (by split <;> simp)

theorem hstage_pos (g : Gh) (p : HPhase) : 1 ≤ hstage g p := by
  cases p with
  | modes done n => cases n <;> simp only [hstage] <;> omega
  | codes k done n =>
    simp only [hstage]
    cases n with
    | succ => simp only [ckStage]; omega
    | zero => cases k <;> simp only [ckStage] <;> (repeat' split) <;> omega
  | clens o size order acc sum => cases order <;> simp only [hstage] <;> omega
  | _ => simp only [hstage] <;> omega

/-- A header step's work, as `hcost` bounds it, is paid for by the potential and the bits the step reads. -/
theorem hpay {g : Gh} {p : HPhase} {bs c : List Bool} {g' : Gh} {p' : HPhase} (hsz : psize p ≤ 704) (hvl : vleft p ≤ 16384)
    (hts : ∀ isL, p = .trees isL → mapSize g isL ≤ 16384)
    (hcl : ∀ o n order acc sum, p = .clens o n order acc sum → lengthSum (acc.map (·.2)) = 1024 * sum)
    (hmn : ∀ isL t r n, p = .code (.map isL t r) n → 2 ≤ n ∧ n ≤ t + 16)
    (h : hStepP (g, p) bs = .next (g', p') c) :
    hcost g p p' + hpot g' p' + hdrRate * c.length ≤ hpot g p + hdrRate * bs.length := by
  rw [hdrRate_eq]
  cases p with
  | cat i =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.cat i) bs = _ from h)
    have hpay := varLen_pay e1
    rw [hdrRate_eq] at hpay
    have hle := catPot_le g i v
    split at e2 <;> cases e2
    · rw [hpot_catNext]
      show 3 + catPot g i v + _ ≤ catPot g i 0 + _
      omega
    · show 3 + (0 + catPot g i v) + _ ≤ catPot g i 0 + _
      omega
  | code o n =>
    obtain ⟨hv, b, e1, e2⟩ := readIn_next' (show hStep g (.code o n) bs = _ from h)
    have l1 := readInt_length _ _ _ _ e1
    have hn : n ≤ 704 := hsz
    have e0 : hpot g (.code o n) = ownerX g o + ownerPot g o := rfl
    rw [e0]
    have hv4 : hv < 4 := by simpa using readInt_lt 2 bs hv b e1
    split at e2
    · obtain ⟨cd, b', e3, e4⟩ := readIn_next' e2
      have l2 := simpleChain_takes e3
      cases e4
      rw [hcost_code_owner]
      cases o with
      | map isL t r =>
        obtain ⟨h2, hnt⟩ := hmn isL t r n rfl
        have hab := alphabetBits_pos h2
        have hle := hpot_owner_map g isL t r cd
        rw [hdrRate_eq] at hle
        show 7 * n + 1301 + ownerX g (.map isL t r) + hpot g (ownerPlace g (.map isL t r) cd) + _ ≤
          ownerX g (.map isL t r) + mapOwner g isL t + _
        omega
      | type i k =>
        have hle := hpot_owner_le g (.type i k) cd (fun _ _ _ e => Owner.noConfusion e)
        omega
      | count i k tc =>
        have hle := hpot_owner_le g (.count i k tc) cd (fun _ _ _ e => Owner.noConfusion e)
        omega
      | codes k done left =>
        have hle := hpot_owner_le g (.codes k done left) cd (fun _ _ _ e => Owner.noConfusion e)
        omega
    · cases e2
      have hs := clensPot_start hn hv4
      show 22 + (clensPot n (codeLengthOrder.drop hv) 0 + ownerX g o + ownerPot g o) + _ ≤ _
      omega
  | clens o n order acc sum =>
    have e0 : hpot g (.clens o n order acc sum) = clensPot n order sum + ownerX g o + ownerPot g o := rfl
    have es : ∀ clc, hpot g (.syms o n clc ⟨[], 8, none⟩) = symsPre clc n 0 + symsTable n + ownerX g o + ownerPot g o :=
      fun _ => rfl
    have hsum := hcl o n order acc sum rfl
    rw [e0]
    cases order with
    | nil =>
      have h' : (if (acc.filter (·.2 != 0)).length = 1 then ORes.next (g, HPhase.syms o n (codeLengthCode acc) ⟨[], 8, none⟩) bs
          else .bad) = .next (g', p') c := h
      split at h' <;> cases h'
      rw [es]
      have := symsPre_le (codeLengthCode acc) n 0
      have := clensPot_nil (n := n) (sum := sum)
      show clDone + _ + _ ≤ _
      omega
    | cons x rest =>
      obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.clens o n (x :: rest) acc sum) bs = _ from h)
      obtain ⟨hl, hf⟩ := clcl_fill e1
      have hB : 2 ≤ bs.length - b.length := by omega
      have hm : 2980 * bs.length = 2980 * b.length + 2980 * (bs.length - b.length) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      generalize bs.length - b.length = B at hB hm hf
      split at e2
      · cases e2
        have := clensPot_step (n := n) (x := x) (rest := rest) (sum := sum) (f := 0) hB (Nat.zero_le _)
        show 3 + (clensPot n rest sum + ownerX g o + ownerPot g o) + _ ≤ _
        rw [Nat.add_zero] at this
        omega
      · rename_i hv0
        rw [ite_eq_right hv0] at hf
        split at e2
        · cases e2
          rename_i hfull
          rw [es]
          obtain ⟨L, hL⟩ := codeLengthCode_canon hsum hv0 hfull
          have hpre : symsPre (codeLengthCode (acc ++ [(x, v)])) n 0 = 0 := by rw [hL]; rfl
          have := clensPot_fin (n := n) (x := x) (rest := rest) (sum := sum) (show 32 - sum ≤ 4 * B by omega)
          show clDone + _ + _ ≤ _
          rw [hpre]
          omega
        · split at e2
          · cases e2
          · cases e2
            have := clensPot_step (n := n) (x := x) (rest := rest) (sum := sum) (f := 32 >>> v) hB hf
            show 3 + (clensPot n rest (sum + (32 >>> v)) + ownerX g o + ownerPot g o) + _ ≤ _
            omega
  | syms o n clc ls =>
    have e0 : hpot g (.syms o n clc ls) = symsPre clc n ls.lens.length + symsTable n + ownerX g o + ownerPot g o := rfl
    have hn : n ≤ 704 := hsz
    rw [e0]
    have h' : (if n < ls.lens.length then ORes.bad
        else if lengthSum ls.lens = 32768 then
          .next (g, ownerPlace g o (.canonical (ls.lens ++ List.replicate (n - ls.lens.length) 0))) bs
        else if ls.lens.length = n then .bad
        else readIn 18 (lenSym clc) bs fun v b =>
          if n < (applyCodeLength ls v.1 v.2).lens.length then .bad
          else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then .bad
          else .next (g, .syms o n clc (applyCodeLength ls v.1 v.2)) b) = .next (g', p') c := h
    split at h'
    · cases h'
    · split at h'
      · cases h'
        have hle := hpot_owner_canon g o (ls.lens ++ List.replicate (n - ls.lens.length) 0)
        rw [hcost_syms_owner]
        omega
      · split at h'
        · cases h'
        · obtain ⟨v, b, e1, e2⟩ := readIn_next' h'
          have l1 := faith_le (faith_lenSym clc) e1
          split at e2
          · cases e2
          · split at e2
            · cases e2
            · cases e2
              rename_i hle _
              obtain ⟨l, hl, hl1⟩ := applyCodeLength_grow ls v.1 v.2
              show (applyCodeLength ls v.1 v.2).lens.length - ls.lens.length + 3 +
                (symsPre clc n (applyCodeLength ls v.1 v.2).lens.length + symsTable n + ownerX g o + ownerPot g o) + _ ≤ _
              rw [hl] at hle ⊢
              rw [List.length_append] at hle ⊢
              cases clc with
              | single s =>
                simp only [symsPre]
                omega
              | canonical L =>
                have l2 := lenSym_takes e1
                simp only [symsPre]
                omega
  | first i n tc cc =>
    have hm := hStep_moves g (.first i n tc cc) bs _ _ h
    have hs := hstage_pos g' p'
    have h1 : hstage g (.first i n tc cc) = 1 := rfl
    rw [h1] at hm
    have hl : c.length + 1 ≤ bs.length := by
      rcases hm with hm | hm
      · exact hm
      · exact absurd hm (Nat.not_lt.mpr hs)
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.first i n tc cc) bs = _ from h)
    cases e2
    rw [hpot_catNext]
    show 3 + catPot g i n + _ ≤ catPot g i n + _
    omega
  | np =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g .np bs = _ from h)
    have l1 : b.length + 6 = bs.length := by
      unfold readNp at e1
      cases h1 : readInt 2 bs with
      | none => rw [h1] at e1; cases e1
      | some p =>
        rw [h1] at e1
        dsimp only [bind, Option.bind] at e1
        cases h2 : readInt 4 p.2 with
        | none => rw [h2] at e1; cases e1
        | some q =>
          rw [h2] at e1
          simp only [Option.some.injEq, Prod.mk.injEq] at e1
          obtain ⟨-, rfl⟩ := e1
          have := readInt_length _ _ _ _ h1
          have := readInt_length _ _ _ _ h2
          omega
    cases e2
    show 260 + beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n + _ ≤ beforeMaps g.m.literal.n g.m.insertCopy.n g.m.distance.n + _
    omega
  | modes done left =>
    cases left with
    | zero =>
      cases h
      show 3 + (mapPre (64 * g.m.literal.n) + 1 + mapAfter _ true 0) + _ ≤ beforeMaps _ _ _ + _
      unfold beforeMaps mapAfter
      simp only [↓reduceIte]
      omega
    | succ n =>
      obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.modes done (n + 1)) bs = _ from h)
      have hl := takes_one (faith_readInt 2) rfl e1
      cases e2
      show 3 + beforeMaps _ _ _ + _ ≤ beforeMaps _ _ _ + _
      omega
  | trees isL =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.trees isL) bs = _ from h)
    have hpay := varLen_pay e1
    rw [hdrRate_eq] at hpay
    have hle := mapAfter_le g isL v
    have hS := hts isL rfl
    have hS0 : mapSize g isL / 65536 = 0 := Nat.div_eq_of_lt (by omega)
    have e0 : hpot g (.trees isL) = mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0 := rfl
    rw [e0]
    unfold mapPre
    split at e2 <;> cases e2
    · have e := hpot_mapNext g isL v (List.replicate (mapSize g isL) 0)
      have hc : hcost g (.trees isL) (mapNextPhase (g.setMap isL v (List.replicate (mapSize g isL) 0)) isL) =
          3 + zb (mapSize g isL) + mapFin g isL := by cases isL <;> rfl
      rw [hc, e]
      unfold zb
      omega
    · rename_i hv2
      obtain ⟨k, hk8, hbl, hvk⟩ := varLen_long e1 (by omega)
      have hkey := trees_key k hk8
      generalize 2 ^ (k + 1) = P at hvk hkey
      have hm : 2980 * bs.length = 2980 * c.length + 2980 * (4 + k) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      show 3 + (770 + zb (mapSize g isL) + zb (mapSize g isL) +
        ((v + 4 + mapFin g isL + mapAfter g isL v) + max 3 (2 * mapSize g isL + 9 * v + 1439 - 6 * hdrRate))) + _ ≤ _
      have hZ : zb (mapSize g isL) = mapSize g isL + 1 := by
        unfold zb
        omega
      have hM := max_sub (2 * mapSize g isL + 9 * v + 1439) (6 * hdrRate)
      rw [hdrRate_eq] at hM ⊢
      exact trees_pay hS hZ hle hvk hkey hm hM
  | rlemax isL t =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.rlemax isL t) bs = _ from h)
    have hl := takes_one faith_readRLEMAX rfl e1
    cases e2
    show 3 + (770 + zb (mapSize g isL) + zb (mapSize g isL) + mapOwner g isL t) + _ ≤
      770 + zb (mapSize g isL) + zb (mapSize g isL) + mapOwnerR g isL t + _
    unfold mapOwner mapOwnerR hdrRate
    omega
  | vals isL t r code done left =>
    have hvl' : left ≤ 16384 := hvl
    rcases hStep_vals_next h with ⟨h0, e, rfl⟩ | ⟨h0, v, hr, e, rfl⟩ | ⟨h0, hr, h'⟩
    · cases e
      simp only [hcost, hpot, h0, ↓reduceIte]
      omega
    · cases e
      simp only [hcost, hpot, h0, hr, ↓reduceIte]
      omega
    · obtain ⟨v, b, e1, e2⟩ := readIn_next' h'
      have l1 := faith_le (faith_mapSym r code) e1
      have l2 : b.length ≠ bs.length := fun e => by
        have := (mapSym_noRead e1 e).1
        rw [hr] at this
        cases this
      have hrun : v.2 < 2 ^ (bs.length - b.length + 1) := mapSym_runLen e1
      have hpay : left - (left - v.2) + 268 ≤ 2980 * (bs.length - b.length) :=
        run_pay (by omega) (Nat.lt_of_le_of_lt (show left - (left - v.2) ≤ v.2 by omega) hrun) (by omega)
      have hm : 2980 * bs.length = 2980 * b.length + 2980 * (bs.length - b.length) := by
        rw [← Nat.mul_add]
        congr 1
        omega
      split at e2
      · cases e2
      · rename_i hle
        cases e2
        simp only [hcost, hpot, h0, hr, ↓reduceIte]
        split <;> omega
  | imtf isL t vals =>
    obtain ⟨v, b, e1, e2⟩ := readIn_next' (show hStep g (.imtf isL t vals) bs = _ from h)
    have l1 := faith_le (faith_readInt 1) e1
    generalize (if v = 0 then vals else inverseMoveToFront vals) = fin at e2
    split at e2
    · cases e2
      rw [hpot_mapNext]
      show t + 4 + mapFin g isL + mapAfter g isL t + _ ≤ t + 4 + mapFin g isL + mapAfter g isL t + _
      omega
    · cases e2
  | codes k done left =>
    cases left with
    | succ n =>
      cases h
      dsimp only
      cases k
      · show 3 + (0 + afterD _ n _) + _ ≤ afterD _ (n + 1) _ + _
        unfold afterD
        omega
      · show 3 + (0 + (3 * n + zb (4 * g.treesD) + 8 + 3 * g.treesD)) + _ ≤
          3 * (n + 1) + zb (4 * g.treesD) + 8 + 3 * g.treesD + _
        omega
      · show 3 + (0 + (3 * n + 4)) + _ ≤ 3 * (n + 1) + 4 + _
        omega
    | zero =>
      cases k with
      | L =>
        cases h
        dsimp only
        show zb (4 * g.m.insertCopy.n) + 4 + (3 * g.m.insertCopy.n + zb (4 * g.treesD) + 8 + 3 * g.treesD) + _ ≤
          afterD g.m.insertCopy.n 0 g.treesD + _
        unfold afterD
        omega
      | I =>
        cases h
        dsimp only
        show zb (4 * g.treesD) + 4 + (3 * g.treesD + 4) + _ ≤ 3 * 0 + zb (4 * g.treesD) + 8 + 3 * g.treesD + _
        omega
      | D => cases h

/-! ### The header machine's work, by where a step goes -/

/-- The tag of a state at a place. -/
def ptag : HPhase → HTag
  | .cat _ => .cat
  | .code .. => .code
  | .clens .. => .clens
  | .syms .. => .syms
  | .first .. => .first
  | .np => .np
  | .modes .. => .modes
  | .trees _ => .trees
  | .rlemax .. => .rlemax
  | .vals .. => .vals
  | .imtf .. => .imtf
  | .codes .. => .codes

theorem HRel.tag_eq {st : Hd} {g : Gh} {p : HPhase} (h : HRel st g p) : st.tag = ptag p := by
  cases p
  case np => exact h.2.2
  all_goals exact h.2.2.1

theorem hcost_ge (g : Gh) (p p' : HPhase) : 3 ≤ hcost g p p' := by
  cases p with
  | code o n => cases p' <;> simp only [hcost] <;> omega
  | clens o n ord acc sum => cases p' <;> simp only [hcost, clDone] <;> omega
  | syms o n clc ls => cases p' <;> simp only [hcost, symsTable] <;> omega
  | trees isL => cases p' <;> simp only [hcost] <;> omega
  | vals isL t r code done left =>
    cases p' with
    | vals => simp only [hcost]; split <;> omega
    | _ => simp only [hcost]; omega
  | imtf => simp only [hcost]; omega
  | codes k done left =>
    cases left with
    | succ => simp only [hcost]; omega
    | zero => cases k <;> simp only [hcost] <;> omega
  | _ => simp only [hcost]; omega

theorem hcost_code (g : Gh) (o : Owner) (n : Nat) (p' : HPhase) :
    hcost g (.code o n) p' = if ptag p' = .clens then 22 else 7 * n + 1301 + ownerX g o := by
  cases p' <;> rfl

theorem hcost_clens (g : Gh) (o : Owner) (n : Nat) (order : List Nat) (acc : List (Nat × Nat)) (sum : Nat) (p' : HPhase) :
    hcost g (.clens o n order acc sum) p' = if ptag p' = .syms then clDone else 3 := by
  cases p' <;> rfl

theorem hcost_trees (g : Gh) (isL : Bool) (p' : HPhase) :
    hcost g (.trees isL) p' = if ptag p' = .rlemax then 3 else 3 + zb (mapSize g isL) + mapFin g isL := by
  cases p' <;> rfl

theorem hcost_syms_other (g : Gh) (o : Owner) (n : Nat) (clc : PrefixCode) (ls : LengthState) {p' : HPhase}
    (h : ptag p' ≠ .syms) : hcost g (.syms o n clc ls) p' = symsTable n + ownerX g o := by
  cases p' <;> first | rfl | exact absurd rfl h

/-- Where a finished table's step goes. -/
theorem growSingle_role (st : Hd) (sym : UInt64) (h : st.d.arena.size + 2672 < 2 ^ 32 ∧ st.d.arena.size % 2 = 0) :
    (growSingle st sym h).role = st.role := by
  unfold growSingle clearDone
  rfl

theorem growLens_role (st : Hd) (h : ∃ L, BuildArgs st.d.arena st.head st.next L) : (growLens st h).role = st.role := by
  unfold growLens clearDone
  rfl

theorem tableDone_tag {st : Hd} {s : Bool} {y : UInt64} {ha : TableArgs st.size st.head st.next s y} {hi : InstallOk st.role st.idx st.fill}
    {har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32} :
    (tableDone st s y ha hi har).tag ≠ .clens ∧ (tableDone st s y ha hi har).tag ≠ .syms := by
  have key : ∀ (x : Hd) (b : UInt64) (hx : InstallOk x.role x.idx x.fill), x.role ≠ .map →
      (installTable x b hx).tag ≠ .clens ∧ (installTable x b hx).tag ≠ .syms := by
    intro x b hx hm
    unfold installTable
    split
    · exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
    · exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
    · exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
    · rename_i e
      exact absurd e hm
  unfold tableDone
  dsimp only
  cases hr : st.role with
  | map =>
    unfold mapTableDone
    exact ⟨fun e => HTag.noConfusion e, fun e => HTag.noConfusion e⟩
  | type | count | codes =>
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      exact key _ _ _ (by rw [growSingle_role, hr]; decide)
    · rw [dite_eq_right hs]
      exact key _ _ _ (by rw [growLens_role, hr]; decide)

theorem mapFin_ge {st : Hd} {g : Gh} {isL : Bool} (hi : st.isL = isL) (hu : Upto st.d g (mapIdx isL)) :
    mapFinishW st ≤ mapFin g isL := by
  unfold mapFinishW mapFin
  rw [hi]
  cases isL with
  | true => exact Nat.le_refl _
  | false =>
    obtain ⟨hT, _⟩ := hu.lmap (by decide)
    have hle := hu.le
    have hsm := hu.small (by decide)
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hT]
    have := zbW_le (4 * g.treesL)
    unfold zb
    omega

theorem wTrees {st : Hd} {g : Gh} {isL : Bool} {pos : USize} {g' : Gh} {p' : HPhase} (hrel : HRel st g (.trees isL))
    (hr : HRel (stepHTrees st pos) g' p') : stepHTreesW st + 2 ≤ hcost g (.trees isL) p' := by
  obtain ⟨hw, hu, ht, hi⟩ := hrel
  have htag := hr.tag_eq
  obtain ⟨hmf, -⟩ := mapSizeFast_eq (g := g) hi hu
  have hfin := mapFin_ge hi hu
  have hge := hcost_ge g (.trees isL) p'
  unfold stepHTreesW
  unfold stepHTrees at htag
  dsimp only at htag ⊢
  generalize varLenFast ⟨st.word, st.count⟩ = r at htag ⊢
  cases hs : r.status with
  | short => dsimp only; omega
  | bad => dsimp only; omega
  | ok =>
    rw [hs] at htag
    dsimp only at htag ⊢
    by_cases ha : r.a < 2
    · rw [ite_eq_left ha] at htag ⊢
      have hne : ptag p' ≠ .rlemax := by
        rw [← htag]
        rcases mapFinish_tag { st with word := r.word, count := r.count, pos := pos, status := .next } r.a
          (zeroBytes (mapSizeFast st)) with e | e | e
        · rw [e]
          exact fun e => HTag.noConfusion e
        · rw [e]
          exact fun e => HTag.noConfusion e
        · rw [e]
          show st.tag ≠ _
          rw [ht]
          exact fun e => HTag.noConfusion e
      rw [hcost_trees, ite_eq_right hne, hmf]
      have := zbW_le (mapSize g isL)
      unfold zb
      omega
    · rw [ite_eq_right ha]
      omega

theorem wImtf {st : Hd} {g : Gh} {isL : Bool} {t : Nat} {vals : List Nat} {p' : HPhase} (hrel : HRel st g (.imtf isL t vals)) :
    stepHImtfW st + 2 ≤ hcost g (.imtf isL t vals) p' := by
  obtain ⟨hw, hu, ht, hi, hn, h2, h256, hm⟩ := hrel
  have hfin := mapFin_ge hi hu
  unfold stepHImtfW
  show _ ≤ t + 4 + mapFin g isL
  split
  · rw [hn]
    omega
  · omega

theorem wCodes {st : Hd} {g : Gh} {k : CK} {done : List PrefixCode} {left : Nat} {p' : HPhase} (hrel : HRel st g (.codes k done left)) :
    stepHCodesW st + 2 ≤ hcost g (.codes k done left) p' := by
  obtain ⟨hw, hu, ht, hck, hidx, hleft, hsum, h256, hpart⟩ := hrel
  have hge := hcost_ge g (.codes k done left) p'
  unfold stepHCodesW
  cases left with
  | succ n =>
    have hne : st.left ≠ 0 := fun e => by rw [e] at hleft; exact Nat.succ_ne_zero _ hleft.symm
    rw [ite_eq_right hne]
    omega
  | zero =>
    have he : st.left = 0 := UInt64.toNat_inj.mp (by rw [hleft]; rfl)
    rw [ite_eq_left he]
    unfold ckFinishW
    rw [hck]
    cases k with
    | L =>
      have hI : st.d.nI.toNat = g.m.insertCopy.n := (hu.cat .I (by show 1 < 7; decide)).n
      show zbW (4 * st.d.nI.toNat) + 1 + 1 + 2 ≤ zb (4 * g.m.insertCopy.n) + 4
      rw [hI]
      have := zbW_le (4 * g.m.insertCopy.n)
      unfold zb
      omega
    | I =>
      obtain ⟨hT, _⟩ := hu.dmap (by show 6 < 8; decide)
      show zbW (4 * st.d.treesD.toNat) + 1 + 1 + 2 ≤ zb (4 * g.treesD) + 4
      rw [hT]
      have := zbW_le (4 * g.treesD)
      unfold zb
      omega
    | D => show 1 + 1 + 2 ≤ 4; omega

theorem wNp {st : Hd} {g : Gh} {p' : HPhase} (hrel : HRel st g .np) : stepHNpW st + 2 ≤ hcost g .np p' := by
  obtain ⟨hw, hu, ht⟩ := hrel
  have hL := hu.cat .L (by show 0 < 3; decide)
  have h1 : st.d.nL.toNat ≤ 256 := by
    show (st.d.nOf .L).toNat ≤ 256
    rw [hL.n]
    exact hL.wf.2.1
  have := zbW_le st.d.nL.toNat
  unfold stepHNpW
  show _ ≤ 260
  split <;> omega

/-- A context map's values: a step that does not go on is one round. -/
theorem valsW_stop (st : Hd) (pos : USize) {hH : ∃ g p, HRel st g p} {hT : st.tag = .vals}
    (h : (stepHVals st pos hH hT).status ≠ .next) : stepHValsW st ≤ 1 := by
  unfold stepHValsW
  unfold stepHVals at h
  dsimp only at h ⊢
  by_cases hl : st.left = 0
  · rw [dite_eq_left hl] at h
    exact absurd rfl h
  rw [dite_eq_right hl] at h
  rw [ite_eq_right hl]
  generalize hT' : mapSymFastT st hH hT = rr at h
  obtain ⟨r, hr⟩ := rr
  have e : r = mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ := by
    rw [← mapSymFastT_val (h := hH) (ht := hT), hT']
  clear hT'
  rw [← e]
  dsimp only at h
  obtain ⟨rs, rw', rc, ra, rb, rcc, rd, re⟩ := r
  cases rs with
  | short => dsimp only; omega
  | bad => dsimp only; omega
  | ok =>
    dsimp only at h ⊢
    by_cases h1 : st.left < rb
    · rw [ite_eq_left h1]
      omega
    · rw [dite_eq_right h1] at h
      exfalso
      apply h
      repeat' (first | rfl | split)

/-- A context map's values: a step's work is its run, its value and a few rounds, with a code that reads no bits twice its
values left and the trees. -/
theorem wVals {st : Hd} {g : Gh} {isL : Bool} {t r : Nat} {code : PrefixCode} {done : List Nat} {left : Nat} {pos : USize}
    {g' : Gh} {p' : HPhase} {a : ByteArray} {stop : USize} {F : List Bool} {hH : ∃ g p, HRel st g p} {hT : st.tag = .vals}
    (hrel : HRel st g (.vals isL t r code done left))
    (hj : hStepP (g, .vals isL t r code done left) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepHVals st pos hH hT).word (stepHVals st pos hH hT).count a (stepHVals st pos hH hT).pos stop F)) :
    stepHValsW st + 2 ≤ hcost g (.vals isL t r code done left) p' := by
  obtain ⟨hw, hu, ht, hi, hn, hr, h2, h256, h16, hok, hC, hsy, hidx, hleft, hlen, hsz, hlt, hat, hzero, hx⟩ := hrel
  have hge := hcost_ge g (.vals isL t r code done left) p'
  unfold stepHValsW
  dsimp only
  by_cases hl : st.left = 0
  · rw [ite_eq_left hl]
    omega
  rw [ite_eq_right hl]
  have hl0 : left ≠ 0 := by
    rw [← hleft]
    exact fun e => hl (UInt64.toNat_inj.mp e)
  have R := mapSymFast_ok (t := st.mapT.t) (base := USize.ofNat 0) (hfit := st.mapT.fits) (h32 := st.mapT.h32) (rlemax := st.rlemax)
    hw hok hC (by omega)
  rw [hr] at R
  have hval := R.ok
  generalize mapSymFast st.mapT.t (USize.ofNat 0) st.mapT.fits st.mapT.h32 st.rlemax ⟨st.word, st.count⟩ = rr at hval
  cases hsr : rr.status with
  | short => dsimp only; omega
  | bad => dsimp only; omega
  | ok =>
    dsimp only
    obtain ⟨hv, hr1, hv1, hrlt⟩ := mapSym_bounds (by omega) h16 hsy ((hval hsr).2 [])
    by_cases hbig : st.left < rr.b
    · rw [ite_eq_left hbig]
      omega
    rw [ite_eq_right hbig]
    have hbig' : rr.b.toNat ≤ left := by
      rw [← hleft]
      exact Nat.le_of_not_lt fun e => hbig (UInt64.lt_iff_toNat_lt.mpr e)
    -- What the spec's step does: where it goes, by whether the code reads.
    have hk := imtfRunW_le (s := rr.a) (k := st.left) (by omega)
    have hk2 := imtfRunW_le (s := rr.a) (k := rr.b) (by omega)
    by_cases hc : rr.count = st.count
    · rw [ite_eq_left hc, min_run (by omega)]
      have hro : runOf r code = some rr.a.toNat := by
        have e := (hval hsr).2 []
        rw [List.append_nil, List.append_nil] at e
        refine (mapSym_noRead e ?_).1
        show rr.buf.held.length = _
        rw [held_len, held_len]
        exact congrArg UInt64.toNat hc
      rcases hStep_vals_next hj with ⟨h0', _, _⟩ | ⟨_, v, hv', e, _⟩ | ⟨_, hno, _⟩
      · exact absurd h0' hl0
      · cases e
        simp only [hcost, hro]
        split <;> omega
      · rw [hro] at hno
        cases hno
    · rw [ite_eq_right hc]
      rcases hStep_vals_next hj with ⟨h0', _, _⟩ | ⟨_, v, hv', _, _⟩ | ⟨_, hno, h'⟩
      · exact absurd h0' hl0
      · -- A code that reads nothing reads nothing here.
        have e := (hval hsr).2 []
        rw [List.append_nil, List.append_nil, mapSym_of_run hv'] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        have hlen' := congrArg List.length e.2
        rw [held_len, held_len] at hlen'
        exact absurd (UInt64.toNat_inj.mp hlen'.symm) hc
      · obtain ⟨vv, b, e4, e5⟩ := readIn_next' h'
        rw [avail_mk, (hval hsr).2] at e4
        simp only [Option.some.injEq, Prod.mk.injEq] at e4
        obtain ⟨rfl, -⟩ := e4
        split at e5
        · cases e5
        · cases e5
          simp only [hcost, hno]
          split <;> omega

/-- What a table's step does for its owner, against `ownerX`. -/
theorem ownerX_ge {st : Hd} {g : Gh} {n : Nat} {o : Owner} (ho : OwnerRel st g n o) (hu : Upto st.d g (ownerStage o)) :
    (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) ≤ ownerX g o := by
  cases o with
  | type i k => rw [ho.1]; simp
  | count i k tc => rw [ho.1]; simp
  | codes k done left => rw [ho.1]; simp
  | map isL t r =>
    obtain ⟨hr, hi, _⟩ := ho
    obtain ⟨hmf, _⟩ := mapSizeFast_eq (g := g) hi hu
    rw [hr, hmf]
    have := zbW_le (mapSize g isL)
    simp only [↓reduceIte, ownerX, zb]
    omega

theorem wCode {st : Hd} {g : Gh} {o : Owner} {n : Nat} {pos : USize} {g' : Gh} {p' : HPhase} {hH : ∃ g p, HRel st g p}
    {hT : st.tag = .code} (hrel : HRel st g (.code o n))
    (hn : (stepHCode st pos hH hT).status = .next) (hr : HRel (stepHCode st pos hH hT) g' p') :
    stepHCodeW st pos + 2 ≤ hcost g (.code o n) p' := by
  obtain ⟨hw, hu, ht, hs, ho⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have htag := hr.tag_eq
  have hge := hcost_ge g (.code o n) p'
  have hX := ownerX_ge ho hu
  unfold stepHCodeW
  unfold stepHCode at htag hn
  dsimp only at htag hn ⊢
  by_cases h2 : 2 ≤ st.count
  · rw [dite_eq_left h2] at htag hn
    rw [ite_eq_left h2]
    by_cases h1 : (BitBuffer.mk st.word st.count).peek 2 = 1
    · rw [ite_eq_left h1] at htag hn ⊢
      generalize hT' : simpleFastT st hH hT h2 = rr at htag hn
      obtain ⟨r, hra⟩ := rr
      have e : r = simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) := by
        rw [← simpleFastT_val (h := hH) (ht := hT) (h2 := h2), hT']
      clear hT'
      rw [← e]
      dsimp only at htag hn
      revert htag hn
      split
      · intro _ hn
        simp [markH] at hn
      · intro _ hn
        simp [markH] at hn
      · rename_i hsr
        intro htag hn
        try rw [hsr]
        dsimp only
        rw [hcost_code]
        by_cases he : r.e = 0
        · rw [dite_eq_left he] at htag
          rw [ite_eq_left he]
          have hnc : ptag p' ≠ .clens := by rw [← htag]; exact tableDone_tag.1
          rw [ite_eq_right hnc]
          have hT' : tableDoneW { st with word := r.word, count := r.count, pos := pos, status := .next } true ≤
              7 * st.size.toNat + 1265 + (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) :=
            tableDoneW_le (st := { st with word := r.word, count := r.count, pos := pos, status := .next })
              ⟨_, (hra hsr).single he st.headSz st.nextSz⟩ hu.arenaOk
          omega
        · rw [dite_eq_right he] at htag
          have hf : r.a.toNat < 704 ∧ r.b.toNat < 704 ∧ r.c.toNat < 704 ∧ r.d.toNat < 704 := (hra hsr).fits
          rw [ite_eq_right he, dite_eq_left hf]
          have hnc : ptag p' ≠ .clens := by
            rw [← htag]
            exact tableDone_tag.1
          rw [ite_eq_right hnc]
          have hT' : tableDoneW (simpleLists st r pos hf) false ≤
              7 * st.size.toNat + 1265 + (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) :=
            tableDoneW_le (st := simpleLists st r pos hf) (simpleLists_args (hra hsr) he) hu.arenaOk
          have hz := zbW_le 32
          omega
    · rw [ite_eq_right h1] at htag ⊢
      have hc : ptag p' = .clens := htag.symm
      rw [hcost_code, ite_eq_left hc]
      have := zbW_le 18
      omega
  · rw [ite_eq_right h2]
    omega

theorem clFinish_tag {st : Hd} {h : ∃ acc, ClDone st acc} : (clFinish st h).tag = .syms := rfl

theorem clFinishW_le {st : Hd} (h : ∃ acc, ClDone st acc) : clFinishW st ≤ 960 := by
  unfold clFinishW
  have := clTableW_le h
  have := zbW_le 32
  omega

theorem wClens {st : Hd} {g : Gh} {o : Owner} {n : Nat} {order : List Nat} {acc : List (Nat × Nat)} {sum : Nat} {pos : USize}
    {g' : Gh} {p' : HPhase} {hH : ∃ g p, HRel st g p} {hT : st.tag = .clens} (hrel : HRel st g (.clens o n order acc sum))
    (hn : (stepHClens st pos hH hT).status = .next)
    (hr : HRel (stepHClens st pos hH hT) g' p') : stepHClensW st pos + 2 ≤ hcost g (.clens o n order acc sum) p' := by
  obtain ⟨hw, hu, ht, hs, ho, hc⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have htag := hr.tag_eq
  have hge := hcost_ge g (.clens o n order acc sum) p'
  unfold stepHClensW
  unfold stepHClens at htag hn
  dsimp only at htag hn ⊢
  by_cases h18 : st.clIdx = 18
  · rw [dite_eq_left h18] at htag hn
    rw [ite_eq_left h18]
    by_cases hnz : st.clNz = 1
    · rw [dite_eq_left hnz] at htag hn
      rw [ite_eq_left hnz]
      have hsy : ptag p' = .syms := by rw [← htag]; exact clFinish_tag
      rw [hcost_clens, ite_eq_left hsy]
      have := clFinishW_le (st := { st with pos := pos, status := .next }) (clens_done0 hH hT h18 hnz)
      have hcd : clDone = 963 := rfl
      omega
    · rw [ite_eq_right hnz]
      omega
  · rw [dite_eq_right h18] at htag hn
    rw [ite_eq_right h18]
    generalize hrr : cclFastS ⟨st.word, st.count⟩ = rr at htag hn
    obtain ⟨r, hr5⟩ := rr
    have er : r = cclFast ⟨st.word, st.count⟩ := by rw [← cclFastS_val, hrr]
    rw [← er]
    dsimp only at htag hn
    cases hsr : r.status with
    | short => dsimp only; omega
    | bad => dsimp only; omega
    | ok =>
      rw [hsr] at htag hn
      dsimp only at htag hn ⊢
      by_cases h0 : r.a = 0
      · rw [ite_eq_left h0]
        omega
      · rw [dite_eq_right h0] at htag hn
        rw [ite_eq_right h0]
        by_cases h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32
        · rw [dite_eq_left h32] at htag hn
          rw [ite_eq_left h32]
          have hsy : ptag p' = .syms := by rw [← htag]; exact clFinish_tag
          rw [hcost_clens, ite_eq_left hsy]
          have := clFinishW_le (st := { st with
              word := r.word, count := r.count, pos := pos, status := .next
              clLens := setLen st.clLens (getU clOrderLut st.clIdx.toUSize).toUInt64 r.a, clSum := st.clSum + ((32 : UInt64) >>> r.a)
              clNz := st.clNz + 1, clSym := (getU clOrderLut st.clIdx.toUSize).toUInt64, clIdx := st.clIdx + 1 })
            (clens_done1 hH hT h18 hr5 h0 h32)
          have hcd : clDone = 963 := rfl
          omega
        · rw [ite_eq_right h32]
          omega

/-- A code's lengths only grow while it stays at its lengths. -/
theorem syms_grow {g : Gh} {o : Owner} {n : Nat} {clc : PrefixCode} {ls : LengthState} {bs c : List Bool} {g' : Gh} {o' : Owner}
    {n' : Nat} {clc' : PrefixCode} {ls' : LengthState} (h : hStepP (g, .syms o n clc ls) bs = .next (g', .syms o' n' clc' ls') c) :
    ls.lens.length < ls'.lens.length := by
  have h' : (if n < ls.lens.length then ORes.bad
      else if lengthSum ls.lens = 32768 then
        .next (g, ownerPlace g o (.canonical (ls.lens ++ List.replicate (n - ls.lens.length) 0))) bs
      else if ls.lens.length = n then .bad
      else readIn 18 (lenSym clc) bs fun v b =>
        if n < (applyCodeLength ls v.1 v.2).lens.length then .bad
        else if 32768 < lengthSum (applyCodeLength ls v.1 v.2).lens then .bad
        else .next (g, .syms o n clc (applyCodeLength ls v.1 v.2)) b) = .next (g', .syms o' n' clc' ls') c := h
  split at h'
  · cases h'
  · split at h'
    · cases o <;> cases h'
    · split at h'
      · cases h'
      · obtain ⟨v, b, _, e2⟩ := readIn_next' h'
        split at e2
        · cases e2
        · split at e2
          · cases e2
          · cases e2
            obtain ⟨l, hl, hl1⟩ := applyCodeLength_grow ls v.1 v.2
            rw [hl, List.length_append]
            omega

/-- An index that grew by an addition grew by what was added. -/
private theorem add_grew {a d : UInt64} {m : Nat} (h : (a + d).toNat = m) (hm : a.toNat < m) : d.toNat = m - a.toNat := by
  rw [UInt64.toNat_add] at h
  have h1 := a.toNat_lt
  have h2 := d.toNat_lt
  generalize (2 : Nat) ^ 64 = M at h h1 h2
  by_cases hov : a.toNat + d.toNat < M
  · rw [Nat.mod_eq_of_lt hov] at h
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem wSyms {st : Hd} {g : Gh} {o : Owner} {n : Nat} {clc : PrefixCode} {ls : LengthState} {pos : USize} {g' : Gh} {p' : HPhase}
    {bs c : List Bool} {hH : ∃ g p, HRel st g p} {hT : st.tag = .syms} (hrel : HRel st g (.syms o n clc ls))
    (hn : (stepHSyms st pos hH hT).status = .next) (hr : HRel (stepHSyms st pos hH hT) g' p')
    (hj : hStepP (g, .syms o n clc ls) bs = .next (g', p') c) :
    stepHSymsW st pos + 2 ≤ hcost g (.syms o n clc ls) p' := by
  obtain ⟨hw, hu, ht, hs, ho, hy⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hge := hcost_ge g (.syms o n clc ls) p'
  have hX := ownerX_ge ho hu
  unfold stepHSymsW
  unfold stepHSyms at hr hn
  by_cases hsum : st.symSum = 32768
  · rw [dite_eq_left hsum] at hr
    rw [ite_eq_left hsum]
    have hns : ptag p' ≠ .syms := by rw [← hr.tag_eq]; exact tableDone_tag.2
    rw [hcost_syms_other g o n clc ls hns]
    have hT' : tableDoneW { st with pos := pos, status := .next } false ≤
        7 * st.size.toNat + 1265 + (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) :=
      tableDoneW_le (st := { st with pos := pos, status := .next }) (syms_args (st := st) hH hT hsum) hu.arenaOk
    have hst : symsTable n = 7 * n + 1268 := rfl
    omega
  · rw [dite_eq_right hsum] at hr hn
    rw [ite_eq_right hsum]
    by_cases hln : st.ln = st.size
    · rw [ite_eq_left hln]
      omega
    · rw [dite_eq_right hln] at hr hn
      rw [ite_eq_right hln]
      dsimp only at hr hn ⊢
      generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at hr hn ⊢
      cases hsr : r.status with
      | short => dsimp only; omega
      | bad => dsimp only; omega
      | ok =>
        rw [hsr] at hr hn
        dsimp only at hr hn ⊢
        unfold symsOk at hr hn
        by_cases h16 : r.a < 16
        · rw [ite_eq_left h16]
          omega
        · rw [dite_eq_right h16] at hr hn
          rw [ite_eq_right h16]
          dsimp only at hr hn ⊢
          generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hr hn ⊢
          generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hr hn ⊢
          generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at hr hn ⊢
          unfold symsRep at hr hn
          by_cases hover : st.size < st.ln + (new - old)
          · rw [ite_eq_left hover]
            omega
          · rw [dite_eq_right hover] at hr hn
            rw [ite_eq_right hover]
            dsimp only at hr hn ⊢
            generalize (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
              else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))) = sum at hr hn ⊢
            by_cases hbig : 32768 < sum
            · rw [ite_eq_left hbig] at hn
              exact absurd hn (fun e => HStatus.noConfusion e)
            · rw [ite_eq_right hbig] at hr ⊢
              by_cases hz : (if r.a = 16 then st.prevLen else 0) = 0
              · rw [ite_eq_left hz]
                omega
              · rw [ite_eq_right hz] at hr ⊢
                have htg : ptag p' = .syms := by rw [← hr.tag_eq]; exact ht
                cases p' with
                | syms o' n' clc' ls' =>
                  have hy' : SymRel (pushRun st r pos hH hT (st.ln + (new - old)) new sum (syms_lnLt hH hT hln)
                    (syms_eLe hH hT hover)) n' clc' ls' := hr.2.2.2.2.2
                  have hg := syms_grow hj
                  have hl := hy.ln
                  have hln' : (st.ln + (new - old)).toNat = ls'.lens.length := hy'.ln
                  have key := add_grew hln' (by rw [hl]; exact hg)
                  rw [hl] at key
                  show _ + 1 + 2 ≤ ls'.lens.length - ls.lens.length + 3
                  omega
                | _ => cases htg

/-- A header step's work, once the buffer is refilled, by where it goes. -/
theorem stepAtHW_cost {st : Hd} {g : Gh} {p : HPhase} {pos : USize} {g' : Gh} {p' : HPhase} {a : ByteArray} {stop : USize}
    {F : List Bool} {h : ∃ g p, HRel st g p} (hrel : HRel st g p) (hn : (stepAtH st pos h).status = .next)
    (hr : HRel (stepAtH st pos h) g' p')
    (hj : hStepP (g, p) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepAtH st pos h).word (stepAtH st pos h).count a (stepAtH st pos h).pos stop F)) :
    stepAtHW st pos + 2 ≤ hcost g p p' := by
  have htag := hrel.tag_eq
  have hge := hcost_ge g p p'
  cases p with
  | cat i =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | code o n =>
    have e1 : stepAtH st pos h = stepHCode st pos h htag := stepAtH_code htag
    have e2 : stepAtHW st pos = stepHCodeW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wCode hrel hn hr
  | clens o n order acc sum =>
    have e1 : stepAtH st pos h = stepHClens st pos h htag := stepAtH_clens htag
    have e2 : stepAtHW st pos = stepHClensW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wClens hrel hn hr
  | syms o n clc ls =>
    have e1 : stepAtH st pos h = stepHSyms st pos h htag := stepAtH_syms htag
    have e2 : stepAtHW st pos = stepHSymsW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn hr
    rw [e2]
    exact wSyms hrel hn hr hj
  | first i n tc cc =>
    have e : stepAtHW st pos = stepHFirstW := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    show 1 + 2 ≤ 3
    omega
  | np =>
    have e : stepAtHW st pos = stepHNpW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wNp hrel
  | modes done left =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | trees isL =>
    have e1 : stepAtH st pos h = stepHTrees st pos := stepAtH_trees htag
    have e2 : stepAtHW st pos = stepHTreesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hr
    rw [e2]
    exact wTrees hrel hr
  | rlemax isL t =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    omega
  | vals isL t r code done left =>
    have e1 : stepAtH st pos h = stepHVals st pos h htag := stepAtH_vals htag
    have e2 : stepAtHW st pos = stepHValsW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hj
    rw [e2]
    exact wVals hrel hj
  | imtf isL t vals =>
    have e : stepAtHW st pos = stepHImtfW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wImtf hrel
  | codes k done left =>
    have e : stepAtHW st pos = stepHCodesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    exact wCodes hrel

/-- A header step, once refilled, stays at the position it is given. -/
private theorem stepAtH_at (st : Hd) (p : USize) (h : ∃ g p, HRel st g p) : (stepAtH st p h).pos = p := by
  rw [stepAtH_pos]

/-- A header step's work, by where it goes. -/
theorem stepHW_cost {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} {g : Gh} {p : HPhase}
    {g' : Gh} {p' : HPhase} {h : HIn st} (hrel : HRel st g p) (hp : pos.toNat ≤ stop.toNat)
    (hn : (stepH a stop hs st pos h hp).status = .next)
    (hr : HRel (stepH a stop hs st pos h hp) g' p')
    (hj : ∀ F, hStepP (g, p) (availBits st.word st.count a pos stop F) =
      .next (g', p') (availBits (stepH a stop hs st pos h hp).word (stepH a stop hs st pos h hp).count a
        (stepH a stop hs st pos h hp).pos stop F)) :
    stepHW a stop hs st pos + 1 ≤ hcost g p p' + ((stepH a stop hs st pos h hp).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  have eH : stepH a stop hs st pos h hp = stepAtH { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos
      (hrel_bits h.rel (refill_spec hs hp (hrel_wf h.rel)).1) := by
    unfold stepH refillH
    rfl
  have eW : stepHW a stop hs st pos = refillW st.word st.count a pos stop hs + stepAtHW { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepHW
    rw [dite_eq_left hp']
  obtain ⟨h1, h2, h3, h4, h5⟩ := refill_spec hs hp hrel.wf
  have hR := refillW_take (word := st.word) (count := st.count) hs hp
  rw [eH] at hn hr hj
  rw [eW, eH, stepAtH_at]
  have hj1 := hj []
  have ha : availBits st.word st.count a pos stop [] = availBits (refill st.word st.count a pos stop hs hp).word
      (refill st.word st.count a pos stop hs hp).count a (refill st.word st.count a pos stop hs hp).pos stop [] := by
    show (BitBuffer.mk st.word st.count).held ++ (chunkBits a pos.toNat stop.toNat ++ []) =
      (refill st.word st.count a pos stop hs hp).buf.held ++ (chunkBits a (refill st.word st.count a pos stop hs hp).pos.toNat stop.toNat ++ [])
    rw [← List.append_assoc, ← List.append_assoc, h4]
  rw [ha] at hj1
  have := stepAtHW_cost (hrel.withBits h1) hn hr hj1
  omega

/-! ### A step that stops

A step that needs input, rejects, runs out of memory or finishes the header stops the call's run of steps. With room in
the arena's reservation, its work is within what the potential holds. -/

/-- A category's places hold at least a block count's step. -/
theorem catPot_ge (g : Gh) (i : Cat) {n : Nat} : 269 ≤ catPot g i n := by
  cases i <;> simp only [catPot, beforeMaps, mapPre] <;> omega

/-- What a code's owner holds is at least 4: the least is a distance group's last code. -/
theorem ownerPot_ge (g : Gh) (o : Owner) : 4 ≤ ownerPot g o := by
  cases o with
  | type i k => have := catPot_ge g i (n := k); show 4 ≤ catPot g i k; omega
  | count i k tc => have := catPot_ge g i (n := k); show 4 ≤ catPot g i k; omega
  | map isL t r => simp only [ownerPot, mapOwner, imtfTail]; omega
  | codes k done left => cases k <;> simp only [ownerPot, codesPot, afterD] <;> omega

/-- A code's step that stops reads too few bits or rejects them; with the arena's room, its table is never built. -/
theorem codeW_le {st : Hd} {g : Gh} {o : Owner} {n : Nat} {pos : USize} {hH : ∃ g p, HRel st g p} {hT : st.tag = .code}
    (hrel : HRel st g (.code o n)) (hb : st.d.arena.size + budO g o ≤ st.d.arenaCap.toNat)
    (hn : (stepHCode st pos hH hT).status ≠ .next) : stepHCodeW st pos + 2 ≤ hpot g (.code o n) := by
  have hrel' := hrel
  obtain ⟨hw, hu, ht, hs, ho⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hP := ownerPot_ge g o
  have e0 : hpot g (.code o n) = ownerX g o + ownerPot g o := rfl
  rw [e0]
  unfold stepHCodeW
  unfold stepHCode at hn
  dsimp only at hn ⊢
  by_cases h2 : 2 ≤ st.count
  · rw [dite_eq_left h2] at hn
    rw [ite_eq_left h2]
    by_cases h1 : (BitBuffer.mk st.word st.count).peek 2 = 1
    · rw [ite_eq_left h1] at hn ⊢
      have hwit := fun hsr => simple_wit hw (by omega) h2 h1 hsr
      generalize hT' : simpleFastT st hH hT h2 = rr at hn
      obtain ⟨r, hra⟩ := rr
      have e : r = simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) := by
        rw [← simpleFastT_val (h := hH) (ht := hT) (h2 := h2), hT']
      clear hT'
      rw [← e] at hwit ⊢
      dsimp only at hn
      revert hn
      split
      · rename_i hsr
        intro _
        (try rw [hsr]); (try dsimp only); omega
      · rename_i hsr
        intro _
        (try rw [hsr]); (try dsimp only); omega
      · rename_i hsr
        intro hn
        obtain ⟨hw2, _⟩ := hwit hsr
        by_cases he : r.e = 0
        · rw [dite_eq_left he] at hn
          have hd := simple_done1 (K := (⟨fun _ _ => none, fun _ _ => none⟩ : HK Unit)) pos hrel' hw2 (hra hsr) he hb
            (ha := ⟨_, (hra hsr).single he st.headSz st.nextSz⟩) (hi := code_install hH hT) (har := hrel_arena hH)
          exact absurd hd.status hn
        · rw [dite_eq_right he] at hn
          have hd := simple_done2 (K := (⟨fun _ _ => none, fun _ _ => none⟩ : HK Unit)) pos hrel' hw2 (hra hsr) he hb
            (ha := simpleLists_args (hra hsr) he) (hi := code_install hH hT) (har := hrel_arena hH)
          exact absurd hd.status hn
    · rw [ite_eq_right h1] at hn
      exact absurd rfl hn
  · rw [ite_eq_right h2]
    omega

theorem clensW_le {st : Hd} {g : Gh} {o : Owner} {n : Nat} {order : List Nat} {acc : List (Nat × Nat)} {sum : Nat} {pos : USize}
    {hH : ∃ g p, HRel st g p} {hT : st.tag = .clens} (_hrel : HRel st g (.clens o n order acc sum))
    (hn : (stepHClens st pos hH hT).status ≠ .next) : stepHClensW st pos + 2 ≤ hpot g (.clens o n order acc sum) := by
  have hP := ownerPot_ge g o
  have e0 : hpot g (.clens o n order acc sum) = clensPot n order sum + ownerX g o + ownerPot g o := rfl
  rw [e0]
  unfold stepHClensW
  unfold stepHClens at hn
  dsimp only at hn ⊢
  by_cases h18 : st.clIdx = 18
  · rw [dite_eq_left h18] at hn
    rw [ite_eq_left h18]
    by_cases hnz : st.clNz = 1
    · rw [dite_eq_left hnz] at hn
      exact absurd rfl hn
    · rw [ite_eq_right hnz]
      omega
  · rw [dite_eq_right h18] at hn
    rw [ite_eq_right h18]
    generalize hrr : cclFastS ⟨st.word, st.count⟩ = rr at hn
    obtain ⟨r, hr5⟩ := rr
    have er : r = cclFast ⟨st.word, st.count⟩ := by rw [← cclFastS_val, hrr]
    rw [← er]
    dsimp only at hn
    cases hsr : r.status with
    | short => dsimp only; omega
    | bad => dsimp only; omega
    | ok =>
      rw [hsr] at hn
      dsimp only at hn ⊢
      by_cases h0 : r.a = 0
      · rw [ite_eq_left h0]
        omega
      · rw [dite_eq_right h0] at hn
        rw [ite_eq_right h0]
        by_cases h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32
        · rw [dite_eq_left h32] at hn
          exact absurd rfl hn
        · rw [ite_eq_right h32]
          omega

theorem symsW_stop {st : Hd} {g : Gh} {o : Owner} {n : Nat} {clc : PrefixCode} {ls : LengthState} {pos : USize}
    {hH : ∃ g p, HRel st g p} {hT : st.tag = .syms}
    (hrel : HRel st g (.syms o n clc ls)) (hn : (stepHSyms st pos hH hT).status ≠ .next) :
    stepHSymsW st pos + 2 ≤ hpot g (.syms o n clc ls) := by
  obtain ⟨hw, hu, ht, hs, ho, hy⟩ := hrel
  obtain ⟨hs1, hs2, hs3⟩ := hs
  have hX := ownerX_ge ho hu
  have e0 : hpot g (.syms o n clc ls) = symsPre clc n ls.lens.length + symsTable n + ownerX g o + ownerPot g o := rfl
  have hst : symsTable n = 7 * n + 1268 := rfl
  rw [e0]
  unfold stepHSymsW
  unfold stepHSyms at hn
  by_cases hsum : st.symSum = 32768
  · rw [ite_eq_left hsum]
    have hT' : tableDoneW { st with pos := pos, status := .next } false ≤
        7 * st.size.toNat + 1265 + (if st.role = .map then 770 + zbW (mapSizeFast st) + zbW (mapSizeFast st) else 0) :=
      tableDoneW_le (st := { st with pos := pos, status := .next }) (syms_args (st := st) hH hT hsum) hu.arenaOk
    omega
  · rw [dite_eq_right hsum] at hn
    rw [ite_eq_right hsum]
    by_cases hln : st.ln = st.size
    · rw [ite_eq_left hln]
      omega
    · rw [dite_eq_right hln] at hn
      rw [ite_eq_right hln]
      dsimp only at hn ⊢
      generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at hn ⊢
      cases hsr : r.status with
      | short => dsimp only; omega
      | bad => dsimp only; omega
      | ok =>
        rw [hsr] at hn
        dsimp only at hn ⊢
        unfold symsOk at hn
        by_cases h16 : r.a < 16
        · rw [ite_eq_left h16]
          omega
        · rw [dite_eq_right h16] at hn
          rw [ite_eq_right h16]
          dsimp only at hn ⊢
          generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at hn ⊢
          generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at hn ⊢
          generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at hn ⊢
          unfold symsRep at hn
          by_cases hover : st.size < st.ln + (new - old)
          · rw [ite_eq_left hover]
            omega
          · rw [dite_eq_right hover] at hn
            rw [ite_eq_right hover]
            dsimp only at hn ⊢
            generalize (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
              else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))) = sum at hn ⊢
            by_cases hbig : 32768 < sum
            · rw [ite_eq_left hbig]
              omega
            · rw [ite_eq_right hbig] at hn
              by_cases hz : (if r.a = 16 then st.prevLen else 0) = 0
              · rw [ite_eq_left hz] at hn
                exact absurd rfl hn
              · rw [ite_eq_right hz] at hn
                exact absurd rfl hn

/-- A header step that stops, once the buffer is refilled: its work is within its place's potential. -/
theorem stepAtHW_stop {st : Hd} {g : Gh} {p : HPhase} {pos : USize} {h : ∃ g p, HRel st g p} (hrel : HRel st g p)
    (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) (hn : (stepAtH st pos h).status ≠ .next) :
    stepAtHW st pos + 2 ≤ hpot g p := by
  have htag := hrel.tag_eq
  cases p with
  | cat i =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    have := catPot_ge g i (n := 0)
    show _ ≤ catPot g i 0
    omega
  | code o n =>
    have e1 : stepAtH st pos h = stepHCode st pos h htag := stepAtH_code htag
    have e : stepAtHW st pos = stepHCodeW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn
    rw [e]
    exact codeW_le hrel hb hn
  | clens o n order acc sum =>
    have e1 : stepAtH st pos h = stepHClens st pos h htag := stepAtH_clens htag
    have e : stepAtHW st pos = stepHClensW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn
    rw [e]
    have := clensW_le (pos := pos) hrel hn
    omega
  | syms o n clc ls =>
    have e1 : stepAtH st pos h = stepHSyms st pos h htag := stepAtH_syms htag
    have e : stepAtHW st pos = stepHSymsW st pos := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn
    rw [e]
    have := symsW_stop hrel hn
    omega
  | first i n tc cc =>
    have e : stepAtHW st pos = stepHFirstW := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    have := catPot_ge g i (n := n)
    show 1 + 2 ≤ catPot g i n
    omega
  | np =>
    have e : stepAtHW st pos = stepHNpW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    have := wNp (p' := .np) hrel
    have : hcost g .np .np = 260 := rfl
    have : 260 ≤ hpot g .np := by
      show 260 ≤ beforeMaps _ _ _
      unfold beforeMaps mapPre
      omega
    omega
  | modes done left =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    have : 3 ≤ hpot g (.modes done left) := by
      show 3 ≤ beforeMaps _ _ _
      unfold beforeMaps
      omega
    omega
  | trees isL =>
    have e : stepAtHW st pos = stepHTreesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    obtain ⟨hw, hu, ht, hi⟩ := hrel
    obtain ⟨hmf, -⟩ := mapSizeFast_eq (g := g) hi hu
    have hfin := mapFin_ge hi hu
    have := zbW_le (mapSize g isL)
    have e0 : hpot g (.trees isL) = mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0 := rfl
    rw [e0]
    unfold mapPre stepHTreesW
    dsimp only
    split
    · split
      · rw [hmf]
        omega
      · omega
    · omega
  | rlemax isL t =>
    have e : stepAtHW st pos = 1 := by unfold stepAtHW; rw [htag] <;> rfl
    have : 3 ≤ hpot g (.rlemax isL t) := by
      show 3 ≤ 770 +_ + _ + _
      omega
    omega
  | vals isL t r code done left =>
    have e1 : stepAtH st pos h = stepHVals st pos h htag := stepAtH_vals htag
    have e : stepAtHW st pos = stepHValsW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e1] at hn
    rw [e]
    have : 3 ≤ hpot g (.vals isL t r code done left) := by
      simp only [hpot]
      split
      · omega
      · split <;> omega
    have := valsW_stop st pos hn
    omega
  | imtf isL t vals =>
    have e : stepAtHW st pos = stepHImtfW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    have := wImtf (p' := .np) hrel
    show _ ≤ imtfTail g isL t
    unfold imtfTail
    simp only [hcost] at this
    omega
  | codes k done left =>
    have e : stepAtHW st pos = stepHCodesW st := by unfold stepAtHW; rw [htag] <;> rfl
    rw [e]
    have := wCodes (p' := .np) hrel
    have hle : hcost g (.codes k done left) .np ≤ hpot g (.codes k done left) := by
      cases left with
      | succ n => cases k <;> simp only [hcost, hpot, codesPot, afterD] <;> omega
      | zero => cases k <;> simp only [hcost, hpot, codesPot, afterD] <;> omega
    omega

/-- A header step that stops: its work is within its place's potential. -/
theorem stepHW_stop {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize} {g : Gh} {p : HPhase}
    {h : HIn st} (hrel : HRel st g p) (hb : st.d.arena.size + budH g p ≤ st.d.arenaCap.toNat) (hp : pos.toNat ≤ stop.toNat)
    (hn : (stepH a stop hs st pos h hp).status ≠ .next) :
    stepHW a stop hs st pos + 1 ≤ hpot g p + ((stepH a stop hs st pos h hp).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  have eH : stepH a stop hs st pos h hp = stepAtH { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos
      (hrel_bits h.rel (refill_spec hs hp (hrel_wf h.rel)).1) := by
    unfold stepH refillH
    rfl
  have eW : stepHW a stop hs st pos = refillW st.word st.count a pos stop hs + stepAtHW { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepHW
    rw [dite_eq_left hp']
  obtain ⟨h1, -⟩ := refill_spec hs hp hrel.wf
  have hR := refillW_take (word := st.word) (count := st.count) hs hp
  rw [eH] at hn
  rw [eW, eH, stepAtH_at]
  have := stepAtHW_stop (hrel.withBits h1) hb hn
  omega

/-! ### A step that runs out of input

Such a step leaves the state at its place, so its work is not paid for by the potential: it is at most 259. -/

theorem tableDone_ni {st : Hd} {s : Bool} {y : UInt64} {ha : TableArgs st.size st.head st.next s y} {hi : InstallOk st.role st.idx st.fill}
    {har : st.d.arena.size % 2 = 0 ∧ st.d.arena.size + 2672 < 2 ^ 32}
    (h : st.status = .next) : (tableDone st s y ha hi har).status ≠ .needsInput := by
  unfold tableDone
  dsimp only
  cases hr : st.role with
  | map =>
    dsimp only
    unfold mapTableDone
    show st.status ≠ _
    rw [h]
    exact fun e => HStatus.noConfusion e
  | type | count | codes =>
    dsimp only
    by_cases hs : s = true
    · rw [dite_eq_left hs]
      rw [(installTable_spec _ _ _).2.2.2.1]
      show st.status ≠ _
      rw [h]
      exact fun e => HStatus.noConfusion e
    · rw [dite_eq_right hs]
      rw [(installTable_spec _ _ _).2.2.2.1]
      show st.status ≠ _
      rw [h]
      exact fun e => HStatus.noConfusion e

theorem clFinish_ni {st : Hd} {hd : ∃ acc, ClDone st acc} (h : st.status = .next) : (clFinish st hd).status ≠ .needsInput := by
  show st.status ≠ _
  rw [h]
  exact fun e => HStatus.noConfusion e

theorem ckFinish_ni {st : Hd} (h : st.status = .next) : (ckFinish st).status ≠ .needsInput := by
  unfold ckFinish
  dsimp only
  split
  · show st.status ≠ _
    rw [h]
    exact fun e => HStatus.noConfusion e
  · show st.status ≠ _
    rw [h]
    exact fun e => HStatus.noConfusion e
  · exact fun e => HStatus.noConfusion e

/-- A header step that runs out of input, once the buffer is refilled, does one round: nothing that runs out of input
builds, fills or transforms. -/
theorem stepAtHW_short {st : Hd} {pos : USize} {hH : ∃ g p, HRel st g p} (h : (stepAtH st pos hH).status = .needsInput) :
    stepAtHW st pos ≤ 1 := by
  unfold stepAtHW
  cases ht : st.tag <;> dsimp only <;> first
    | rw [stepAtH_cat ht] at h | rw [stepAtH_code ht] at h | rw [stepAtH_clens ht] at h | rw [stepAtH_syms ht] at h
    | rw [stepAtH_first ht] at h | rw [stepAtH_np ht] at h | rw [stepAtH_modes ht] at h | rw [stepAtH_trees ht] at h
    | rw [stepAtH_rlemax ht] at h | rw [stepAtH_vals ht] at h | rw [stepAtH_imtf ht] at h | rw [stepAtH_codes ht] at h
    | rw [stepAtH_ready ht] at h
  case cat | modes | rlemax | ready => omega
  case first => show 1 ≤ 1; omega
  case code =>
    unfold stepHCode at h
    unfold stepHCodeW
    dsimp only at h ⊢
    by_cases h2 : 2 ≤ st.count
    · rw [dite_eq_left h2] at h
      rw [ite_eq_left h2]
      by_cases h1 : (BitBuffer.mk st.word st.count).peek 2 = 1
      · rw [ite_eq_left h1] at h ⊢
        generalize hT' : simpleFastT st hH ht h2 = rr at h
        obtain ⟨r, hra⟩ := rr
        have e : r = simpleFast st.size (alphabetBitsFast st.size) ((BitBuffer.mk st.word st.count).drop 2) := by
          rw [← simpleFastT_val (h := hH) (ht := ht) (h2 := h2), hT']
        clear hT'
        rw [← e]
        dsimp only at h
        revert h
        split
        · rename_i hsr
          intro _
          (try rw [hsr]); (try dsimp only); omega
        · rename_i hsr
          intro _
          (try rw [hsr]); (try dsimp only); omega
        · intro h
          by_cases he : r.e = 0
          · rw [dite_eq_left he] at h
            exact absurd h (tableDone_ni rfl)
          · rw [dite_eq_right he] at h
            exact absurd h (tableDone_ni rfl)
      · rw [ite_eq_right h1] at h
        exact absurd h (fun e => HStatus.noConfusion e)
    · rw [ite_eq_right h2]
      omega
  case clens =>
    unfold stepHClens at h
    unfold stepHClensW
    dsimp only at h ⊢
    by_cases h18 : st.clIdx = 18
    · rw [dite_eq_left h18] at h
      rw [ite_eq_left h18]
      by_cases hnz : st.clNz = 1
      · rw [dite_eq_left hnz] at h
        exact absurd h (clFinish_ni rfl)
      · rw [ite_eq_right hnz]
        omega
    · rw [dite_eq_right h18] at h
      rw [ite_eq_right h18]
      generalize hrr : cclFastS ⟨st.word, st.count⟩ = rr at h
      obtain ⟨r, hr5⟩ := rr
      have er : r = cclFast ⟨st.word, st.count⟩ := by rw [← cclFastS_val, hrr]
      rw [← er]
      dsimp only at h
      cases hsr : r.status with
      | short => dsimp only; omega
      | bad => dsimp only; omega
      | ok =>
        rw [hsr] at h
        dsimp only at h ⊢
        by_cases h0 : r.a = 0
        · rw [ite_eq_left h0]
          omega
        · rw [dite_eq_right h0] at h
          rw [ite_eq_right h0]
          by_cases h32 : st.clSum + ((32 : UInt64) >>> r.a) = 32
          · rw [dite_eq_left h32] at h
            exact absurd h (clFinish_ni rfl)
          · rw [ite_eq_right h32]
            omega
  case syms =>
    unfold stepHSyms at h
    unfold stepHSymsW
    by_cases hsum : st.symSum = 32768
    · rw [dite_eq_left hsum] at h
      exact absurd h (tableDone_ni rfl)
    · rw [dite_eq_right hsum] at h
      rw [ite_eq_right hsum]
      by_cases hln : st.ln = st.size
      · rw [ite_eq_left hln]
        omega
      · rw [dite_eq_right hln] at h
        rw [ite_eq_right hln]
        dsimp only at h ⊢
        generalize lenSymFast st.clt.t (USize.ofNat 0) st.clt.fits st.clt.h32 ⟨st.word, st.count⟩ = r at h ⊢
        cases hsr : r.status with
        | short => dsimp only; omega
        | bad => dsimp only; omega
        | ok =>
          rw [hsr] at h
          dsimp only at h ⊢
          unfold symsOk at h
          by_cases h16 : r.a < 16
          · rw [ite_eq_left h16]
            omega
          · rw [dite_eq_right h16] at h
            rw [ite_eq_right h16]
            dsimp only at h ⊢
            generalize (if st.repCount ≠ 0 ∧ st.repSym = r.a then st.repCount else 0) = old at h ⊢
            generalize (if r.a = 16 then (4 : UInt64) else 8) = mult at h ⊢
            generalize (if old = 0 then 3 + r.b else mult * (old - 2) + (3 + r.b)) = new at h ⊢
            unfold symsRep at h
            by_cases hover : st.size < st.ln + (new - old)
            · rw [ite_eq_left hover]
              omega
            · rw [dite_eq_right hover] at h
              rw [ite_eq_right hover]
              dsimp only at h ⊢
              generalize (if (if r.a = 16 then st.prevLen else 0) = 0 then st.symSum
                else st.symSum + (new - old) * ((32768 : UInt64) >>> (if r.a = 16 then st.prevLen else 0))) = sum at h ⊢
              by_cases hbig : 32768 < sum
              · rw [ite_eq_left hbig]
                omega
              · rw [ite_eq_right hbig] at h
                by_cases hz : (if r.a = 16 then st.prevLen else 0) = 0
                · rw [ite_eq_left hz] at h
                  exact absurd h (fun e => HStatus.noConfusion e)
                · rw [ite_eq_right hz] at h
                  exact absurd h (fun e => HStatus.noConfusion e)
  case np =>
    unfold stepHNp at h
    unfold stepHNpW
    dsimp only at h ⊢
    generalize npFast ⟨st.word, st.count⟩ = r at h ⊢
    cases hsr : r.status with
    | short => dsimp only; omega
    | bad => dsimp only; omega
    | ok =>
      rw [hsr] at h
      dsimp only at h
      exact absurd h (fun e => HStatus.noConfusion e)
  case trees =>
    unfold stepHTrees at h
    unfold stepHTreesW
    dsimp only at h ⊢
    generalize varLenFast ⟨st.word, st.count⟩ = r at h ⊢
    cases hsr : r.status with
    | short => dsimp only; omega
    | bad => dsimp only; omega
    | ok =>
      rw [hsr] at h
      dsimp only at h ⊢
      by_cases ha : r.a < 2
      · rw [ite_eq_left ha] at h
        rcases (mapFinish_spec _ _ _).2.2.2 with e | e <;> rw [e] at h <;> exact absurd h (fun e => HStatus.noConfusion e)
      · rw [ite_eq_right ha]
        omega
  case vals =>
    have := valsW_stop st pos (hH := hH) (hT := ht) (by rw [h]; exact fun e => HStatus.noConfusion e)
    omega
  case imtf =>
    unfold stepHImtf at h
    unfold stepHImtfW
    dsimp only at h ⊢
    by_cases h1 : 1 ≤ st.count
    · rw [ite_eq_left h1] at h
      repeat' split at h
      all_goals first
        | exact absurd h (fun e => HStatus.noConfusion e)
        | (rcases (mapFinish_spec _ _ _).2.2.2 with e | e <;> rw [e] at h <;> exact absurd h (fun e => HStatus.noConfusion e))
    · rw [ite_eq_right h1]
      omega
  case codes =>
    unfold stepHCodes at h
    unfold stepHCodesW
    by_cases h0 : st.left = 0
    · rw [ite_eq_left h0] at h
      exact absurd h (ckFinish_ni rfl)
    · rw [ite_eq_right h0]
      omega

/-- A header step that runs out of input does at most a refill and one round more. -/
theorem stepHW_short {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {st : Hd} {pos : USize}
    {hH : HIn st} {hp : pos.toNat ≤ stop.toNat} (h : (stepH a stop hs st pos hH hp).status = .needsInput) :
    stepHW a stop hs st pos ≤ 2 + ((stepH a stop hs st pos hH hp).pos.toNat - pos.toNat) := by
  have hp' : pos ≤ stop := USize.le_iff_toNat_le.mpr hp
  have eH : stepH a stop hs st pos hH hp = stepAtH { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos
      (hrel_bits hH.rel (refill_spec hs hp (hrel_wf hH.rel)).1) := by
    unfold stepH refillH
    rfl
  have eW : stepHW a stop hs st pos = refillW st.word st.count a pos stop hs + stepAtHW { st with
      word := (refill st.word st.count a pos stop hs hp).word
      count := (refill st.word st.count a pos stop hs hp).count } (refill st.word st.count a pos stop hs hp).pos := by
    unfold stepHW
    rw [dite_eq_left hp']
  have hR := refillW_take (word := st.word) (count := st.count) hs hp
  rw [eH] at h
  rw [eW, eH, stepAtH_at]
  have := stepAtHW_short h
  omega

/-! ### The most a header's place holds

With at most 256 block types in a category, 256 trees in a context map and 16384 values in it, a header's place holds at
most 77764: a literal context map's code's lengths, with the table's work for the map and what the map holds. -/

theorem beforeMaps_le {nL nI nD : Nat} (h1 : nL ≤ 256) (h2 : nI ≤ 256) (h3 : nD ≤ 256) : beforeMaps nL nI nD ≤ 53380 := by
  unfold beforeMaps afterL afterD mapPre zb smallMax catMax treeMax
  omega

theorem catPot_most {g : Gh} {i : Cat} {n : Nat} (h0 : g.m.literal.n ≤ 256) (hI : i = .D → g.m.insertCopy.n ≤ 256) (hn : n ≤ 256) :
    catPot g i n ≤ 53380 := by
  cases i with
  | L => exact beforeMaps_le hn (by omega) (by omega)
  | I => exact beforeMaps_le h0 hn (by omega)
  | D => exact beforeMaps_le h0 (hI rfl) hn

theorem mapTail_le {g : Gh} {isL : Bool} {t : Nat} (ht : t ≤ 256) (hI : g.m.insertCopy.n ≤ 256) (hD : g.m.distance.n ≤ 256)
    (hL : isL = false → g.treesL ≤ 256) : mapFin g isL + mapAfter g isL t ≤ 17133 := by
  unfold mapFin mapAfter afterL afterD mapPre zb smallMax catMax treeMax
  cases isL with
  | false =>
    have := hL rfl
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  | true =>
    simp only [↓reduceIte]
    omega

theorem imtfTail_le {g : Gh} {isL : Bool} {t : Nat} (ht : t ≤ 256) (hI : g.m.insertCopy.n ≤ 256)
    (hD : g.m.distance.n ≤ 256) (hL : isL = false → g.treesL ≤ 256) : imtfTail g isL t ≤ 17393 := by
  have := mapTail_le ht hI hD hL
  unfold imtfTail
  omega

theorem mapOwner_le {g : Gh} {isL : Bool} {t : Nat} (hS : mapSize g isL ≤ 16384) (ht : t ≤ 256) (hI : g.m.insertCopy.n ≤ 256)
    (hD : g.m.distance.n ≤ 256) (hL : isL = false → g.treesL ≤ 256) : mapOwner g isL t ≤ 39001 := by
  have := imtfTail_le ht hI hD hL
  unfold mapOwner hdrRate
  omega

theorem codesPot_le {g : Gh} {k : CK} {left : Nat} (hl : left ≤ 256) (hI : g.m.insertCopy.n ≤ 256) (hD : g.treesD ≤ 256) :
    codesPot g k left ≤ 4366 := by
  cases k <;> simp only [codesPot, afterD, zb] <;> omega

theorem ownerX_le {g : Gh} (hg : GOk g) (o : Owner) : ownerX g o ≤ 33540 := by
  cases o with
  | map isL t r =>
    have := mapSize_le hg isL
    simp only [ownerX, zb]
    omega
  | _ => simp [ownerX]

/-- What a code's owner settled: a category's block types before a category's code, the categories before a context map,
and the maps before the groups of codes. -/
theorem ownerPot_le {st : Hd} {g : Gh} {n : Nat} {o : Owner} (ho : OwnerRel st g n o) (hu : Upto st.d g (ownerStage o)) (hg : GOk g) :
    ownerPot g o ≤ 53380 := by
  have hI : 1 < ownerStage o → g.m.insertCopy.n ≤ 256 := fun h => (hu.cat .I h).wf.2.1
  cases o with
  | type i k =>
    obtain ⟨_, _, _, _, hk, _⟩ := ho
    show catPot g i k ≤ _
    refine Nat.le_trans (catPot_most (i := i) hg.1 (fun e => hI ?_) hk) (by omega)
    subst e
    show 1 < 2
    decide
  | count i k tc =>
    obtain ⟨_, _, _, _, hk, _⟩ := ho
    show catPot g i k ≤ _
    refine Nat.le_trans (catPot_most (i := i) hg.1 (fun e => hI ?_) hk) (by omega)
    subst e
    show 1 < 2
    decide
  | map isL t r =>
    obtain ⟨_, _, _, _, _, ht, _⟩ := ho
    have hst : 5 ≤ ownerStage (.map isL t r) := by
      show 5 ≤ mapIdx isL
      unfold mapIdx
      split <;> omega
    refine Nat.le_trans (mapOwner_le (mapSize_le hg isL) ht (hI (by omega)) hg.2.1 (fun e => ?_)) (by omega)
    subst e
    exact (hu.lmap (show 5 < 6 by decide)).2.2.1
  | codes k done left =>
    obtain ⟨_, _, _, _, _, hl, hc, _⟩ := ho
    have hst : 7 ≤ ownerStage (.codes k done left) := by
      show 7 ≤ ckIdx k + 7
      omega
    show codesPot g k left ≤ _
    exact Nat.le_trans (codesPot_le (k := k) (left := left) (by omega) (hI (by omega)) (hu.dmap (by omega)).2.2.1) (by omega)

/-- What a code's owner holds, with the most the code's lengths carry. -/
theorem codeOwner_le {st : Hd} {g : Gh} {n : Nat} {o : Owner} (ho : OwnerRel st g n o) (hu : Upto st.d g (ownerStage o))
    (hg : GOk g) (hn : n ≤ 704) : ownerX g o + ownerPot g o + clDone + symsTable n + 4 * n ≤ 77764 := by
  have hP := ownerPot_le ho hu hg
  have hI : 1 < ownerStage o → g.m.insertCopy.n ≤ 256 := fun h => (hu.cat .I h).wf.2.1
  unfold clDone symsTable
  cases o with
  | type i k =>
    obtain ⟨_, _, _, _, hk, hs⟩ := ho
    simp only [ownerX]
    rw [hs]
    unfold blockTypeAlphabetSize
    omega
  | count i k tc =>
    obtain ⟨_, _, _, _, _, hs, _⟩ := ho
    simp only [ownerX]
    rw [hs]
    unfold blockCountAlphabetSize
    omega
  | map isL t r =>
    obtain ⟨_, _, _, _, _, ht, hr, hs⟩ := ho
    have hst : 5 ≤ ownerStage (.map isL t r) := by
      show 5 ≤ mapIdx isL
      unfold mapIdx
      split <;> omega
    have hm := mapOwner_le (mapSize_le hg isL) ht (hI (by omega)) hg.2.1 (fun e => by
      subst e
      exact (hu.lmap (show 5 < 6 by decide)).2.2.1)
    have hX := ownerX_le hg (.map isL t r)
    have e : ownerPot g (.map isL t r) = mapOwner g isL t := rfl
    rw [e, hs]
    unfold contextMapAlphabetSize
    omega
  | codes k done left =>
    simp only [ownerX]
    omega

/-- The most a header's place holds. -/
theorem hpot_le {st : Hd} {g : Gh} {p : HPhase} (hrel : HRel st g p) (hg : GOk g) (hp : HOk p) : hpot g p ≤ 77764 := by
  obtain ⟨_, hu, hm⟩ := hrel
  have hS := mapSize_le hg
  have hI : 1 < stageOf p → g.m.insertCopy.n ≤ 256 := fun h => (hu.cat .I h).wf.2.1
  have hL : 5 < stageOf p → g.treesL ≤ 256 := fun h => (hu.lmap h).2.2.1
  have hD : 6 < stageOf p → g.treesD ≤ 256 := fun h => (hu.dmap h).2.2.1
  have hmap : ∀ isL, stageOf p = mapIdx isL → (isL = false → g.treesL ≤ 256) ∧ g.m.insertCopy.n ≤ 256 := by
    intro isL e
    refine ⟨fun e2 => hL ?_, hI ?_⟩
    · rw [e, e2]
      decide
    · rw [e]
      unfold mapIdx
      split <;> omega
  cases p with
  | cat i =>
    refine Nat.le_trans (catPot_most (i := i) (n := 0) hg.1 (fun e => hI ?_) (Nat.zero_le 256)) (by omega)
    subst e
    show 1 < 2
    decide
  | code o n =>
    obtain ⟨_, hs, ho⟩ := hm
    have := codeOwner_le ho hu hg hs.2.2
    show ownerX g o + ownerPot g o ≤ _
    omega
  | clens o n order acc sum =>
    obtain ⟨_, hs, ho, _⟩ := hm
    have := codeOwner_le ho hu hg hs.2.2
    have hc : clensPot n order sum ≤ clDone + symsTable n + 4 * n := by unfold clensPot; omega
    show clensPot n order sum + ownerX g o + ownerPot g o ≤ _
    omega
  | syms o n clc ls =>
    obtain ⟨_, hs, ho, _⟩ := hm
    have := codeOwner_le ho hu hg hs.2.2
    have := symsPre_le clc n ls.lens.length
    have hst : symsTable n ≤ clDone + symsTable n := Nat.le_add_left _ _
    show symsPre clc n ls.lens.length + symsTable n + ownerX g o + ownerPot g o ≤ _
    omega
  | first i n tc cc =>
    refine Nat.le_trans (catPot_most (i := i) (n := n) hg.1 (fun e => hI ?_) hp) (by omega)
    subst e
    show 1 < 2
    decide
  | np =>
    exact Nat.le_trans (beforeMaps_le hg.1 (hI (show 1 < 3 by decide)) hg.2.1) (by omega)
  | modes done left =>
    exact Nat.le_trans (beforeMaps_le hg.1 (hI (show 1 < 4 by decide)) hg.2.1) (by omega)
  | trees isL =>
    obtain ⟨h1, h2⟩ := hmap isL rfl
    have := mapTail_le (t := 0) (Nat.zero_le _) h2 hg.2.1 h1
    have := hS isL
    show mapPre (mapSize g isL) + mapFin g isL + mapAfter g isL 0 ≤ _
    unfold mapPre
    omega
  | rlemax isL t =>
    obtain ⟨h1, h2⟩ := hmap isL rfl
    have := imtfTail_le hp h2 hg.2.1 h1
    have := hS isL
    show 770 + zb (mapSize g isL) + zb (mapSize g isL) + mapOwnerR g isL t ≤ _
    unfold zb mapOwnerR hdrRate
    omega
  | vals isL t r code done left =>
    obtain ⟨h1, h2⟩ := hmap isL rfl
    obtain ⟨_, _, _, _, _, ht, _, _, _, _, _, _, _, _⟩ := hm
    have hT := imtfTail_le ht h2 hg.2.1 h1
    have hl : left ≤ 16384 := hp
    show (if left = 0 then 3 + imtfTail g isL t
      else match runOf r code with
        | some _ => 2 * left + 2 * t + 23 + imtfTail g isL t
        | none => 3 + imtfTail g isL t) ≤ _
    split
    · omega
    · split <;> omega
  | imtf isL t vals =>
    obtain ⟨h1, h2⟩ := hmap isL rfl
    obtain ⟨_, _, _, _, ht, _⟩ := hm
    have hT := imtfTail_le ht h2 hg.2.1 h1
    show imtfTail g isL t ≤ _
    omega
  | codes k done left =>
    obtain ⟨_, _, _, _, hl, hc, _⟩ := hm
    have hst : 7 ≤ stageOf (.codes k done left) := by
      show 7 ≤ ckIdx k + 7
      omega
    exact Nat.le_trans (codesPot_le (by omega) (hI (by omega)) (hD (by omega))) (by omega)

end Brotli.Decoder
