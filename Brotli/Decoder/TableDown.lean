import Brotli.Decoder.TableSize

/-!
# Building a table longest codes first

`buildDown` writes a canonical code's table visiting the code words longest first. A long code word whose root slot is
still empty is the deepest under its root, so it opens the root's sub-table at the end of the array, as deep as itself,
and the root slot records how deep and where; the code words after it under the same root find the sub-table there.
Sub-tables are placed in the order they open, so this section states the table's layout for any offsets whose
sub-tables don't overlap.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### Zeros, and the slots of opened sub-tables -/

/-- `n` zero bytes. -/
def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate n 0)

theorem size_zeros (n : Nat) : (zeros n).size = n := by
  show (Array.replicate _ _).size = _
  simp

/-- A slot in zeros appended to an array is empty. -/
theorem slotAt_zeros {t : ByteArray} {n q : Nat} (h1 : t.size ≤ 2 * q) (h2 : 2 * q + 1 < t.size + n) :
    slotAt (t ++ zeros n) q = (0, 0) := by
  have key : ∀ i, t.size ≤ i → i < t.size + n → (t ++ zeros n).data[i]? = some 0 := by
    intro i h1 h2
    rw [ByteArray.data_append, Array.getElem?_append_right h1]
    show (Array.replicate n 0)[i - t.size]? = some 0
    rw [Array.getElem?_replicate, ite_eq_left (by omega)]
  simp only [slotAt, slotNum]
  rw [key _ (by omega) (by omega), key _ (by omega) (by omega)]
  rfl

/-- The slots of the sub-tables of the root slots in `ops`, below root slot `n`. -/
def opSum (ops : List Nat) (D : Array Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => opSum ops D n + if n ∈ ops then subSize (D.getD n 0) else 0

theorem opSum_nil (D : Array Nat) : ∀ n, opSum [] D n = 0
  | 0 => rfl
  | n + 1 => by simp [opSum, opSum_nil D n]

theorem opSum_cons {ops : List Nat} {D : Array Nat} {r : Nat} (hr : r ∉ ops) :
    ∀ n, opSum (r :: ops) D n = opSum ops D n + if r < n then subSize (D.getD r 0) else 0
  | 0 => by simp [opSum]
  | n + 1 => by
    simp only [opSum, opSum_cons hr n, List.mem_cons]
    by_cases h1 : n = r
    · subst h1
      simp [hr]
    · by_cases h2 : r < n
      · simp [h1, h2, show r < n + 1 by omega]
        omega
      · simp [h1, h2, show ¬ r < n + 1 by omega]

theorem opSum_le (ops : List Nat) (D : Array Nat) : ∀ n, opSum ops D n ≤ offSum D n
  | 0 => Nat.le_refl _
  | n + 1 => by
    have := opSum_le ops D n
    simp only [opSum, offSum]
    split <;> omega

/-- With every root slot that has a sub-table in `ops`, the sub-tables take the slots `offSum` counts. -/
theorem opSum_full {ops : List Nat} {D : Array Nat} : ∀ n, (∀ r, r < n → D.getD r 0 ≠ 0 → r ∈ ops) →
    opSum ops D n = offSum D n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [opSum, offSum]
    rw [opSum_full n fun r hr => h r (by omega)]
    by_cases hz : D.getD n 0 = 0
    · simp [subSize, hz]
    · simp [h n (by omega) hz]

/-! ### Where each bit pattern's slot is, for any placement of the sub-tables -/

/-- The slot a bit pattern's lookup ends at, relative to the table's start, with root slot `r`'s sub-table at `o r`. -/
def slotPosO (D : Array Nat) (o : Nat → Nat) (w : Nat) : Nat :=
  if D.getD (w % 256) 0 = 0 then w % 256 else 256 + o (w % 256) + (w / 256) % 2 ^ D.getD (w % 256) 0

/-- The sub-tables of root slots `r` and `r'` don't overlap. -/
def Disj (D : Array Nat) (o : Nat → Nat) (r r' : Nat) : Prop :=
  o r + 2 ^ D.getD r 0 ≤ o r' ∨ o r' + 2 ^ D.getD r' 0 ≤ o r

/-- Bit patterns with the same slot agree on the bits their lookup looks at. -/
theorem slotPosO_low {D : Array Nat} {o : Nat → Nat} {w w' : Nat} (h : slotPosO D o w = slotPosO D o w')
    (hd : D.getD (w % 256) 0 ≠ 0 → D.getD (w' % 256) 0 ≠ 0 → w % 256 ≠ w' % 256 → Disj D o (w % 256) (w' % 256)) :
    D.getD (w' % 256) 0 = D.getD (w % 256) 0 ∧ w' % 2 ^ (8 + D.getD (w % 256) 0) = w % 2 ^ (8 + D.getD (w % 256) 0) := by
  have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
  have hr' : w' % 256 < 256 := Nat.mod_lt _ (by decide)
  have hrr : w' % 256 = w % 256 ∧ (D.getD (w % 256) 0 = 0 ∨
      (w / 256) % 2 ^ D.getD (w % 256) 0 = (w' / 256) % 2 ^ D.getD (w % 256) 0) := by
    unfold slotPosO at h
    by_cases hz : D.getD (w % 256) 0 = 0
    · by_cases hz' : D.getD (w' % 256) 0 = 0
      · simp only [hz, hz', ↓reduceIte] at h
        exact ⟨h.symm, Or.inl hz⟩
      · simp only [hz, hz', ↓reduceIte] at h
        omega
    · by_cases hz' : D.getD (w' % 256) 0 = 0
      · simp only [hz, hz', ↓reduceIte] at h
        omega
      · simp only [hz, hz', ↓reduceIte] at h
        have hlt1 : (w / 256) % 2 ^ D.getD (w % 256) 0 < 2 ^ D.getD (w % 256) 0 := Nat.mod_lt _ (Nat.two_pow_pos _)
        have hlt2 : (w' / 256) % 2 ^ D.getD (w' % 256) 0 < 2 ^ D.getD (w' % 256) 0 := Nat.mod_lt _ (Nat.two_pow_pos _)
        have heq : w' % 256 = w % 256 := by
          refine Classical.byContradiction fun hne => ?_
          rcases hd hz hz' (Ne.symm hne) with hd | hd <;> omega
        rw [heq] at h
        exact ⟨heq, Or.inr (by omega)⟩
  obtain ⟨e, hj⟩ := hrr
  refine ⟨by rw [e], ?_⟩
  rw [pow_split, pow_split, e]
  rcases hj with hz | hj
  · simp [hz, Nat.mod_one]
  · rw [hj]

section Build

variable {lens : List Nat}

/-- A position written by a code word is the slot of a bit pattern that begins with it. -/
theorem written_hitO (hC : Complete (.canonical lens)) (o : Nat → Nat) {s l c : Nat} (hs : lens[s]? = some l)
    (h0 : l ≠ 0) (hc : code lens s = some c) {base k : Nat}
    (hk : k < (if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD (rootOf l c) 0 - (l - 8)))) :
    ∃ w, revBits l w = c ∧
      (if l ≤ 8 then base + revBits l c + k * 2 ^ l
       else base + 256 + o (rootOf l c) + revBits l c / 256 + k * 2 ^ (l - 8)) =
        base + slotPosO (depths lens) o w := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hlt : c < 2 ^ l := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte] at hk ⊢
    have hi := (range_iff hl hst (revBits l c + k * 2 ^ l)).mpr ⟨k, hk, rfl⟩
    have hrev : revBits l (revBits l c + k * 2 ^ l) = c := (revBits_eq_iff hlt).mpr hi.2
    refine ⟨_, hrev, ?_⟩
    have hhit : Hit (.canonical lens) (revBits l c + k * 2 ^ l) l s := ⟨hs, h0, by rw [hc, hrev]⟩
    have hz := hit_short_zero hC hhit hl
    have hmod : (revBits l c + k * 2 ^ l) % 256 = revBits l c + k * 2 ^ l := Nat.mod_eq_of_lt hi.1
    unfold slotPosO
    rw [ite_eq_left hz, hmod, Nat.add_assoc]
  · simp only [hl, ↓reduceIte] at hk ⊢
    have hd := (depths_spec hC.1).2.2.2 s l c ⟨hs, by omega, hc⟩
    generalize hdd : (depths lens).getD (rootOf l c) 0 = d at hk hd ⊢
    have hle : l - 8 ≤ d := hd
    have hst8 : 2 ^ l = 256 * 2 ^ (l - 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      congr 1
      omega
    have hj0 : revBits l c / 256 < 2 ^ (l - 8) := Nat.div_lt_of_lt_mul (by rw [← hst8]; exact hst)
    have hj := (range_iff hle hj0 (revBits l c / 256 + k * 2 ^ (l - 8))).mpr ⟨k, hk, rfl⟩
    generalize hjd : revBits l c / 256 + k * 2 ^ (l - 8) = j at hj
    have hr : rootOf l c < 256 := rootOf_lt l c
    have hwm : (rootOf l c + 256 * j) % 256 = rootOf l c := by omega
    have hwd : (rootOf l c + 256 * j) / 256 = j := by omega
    have hwl : (rootOf l c + 256 * j) % 2 ^ l = revBits l c := by
      rw [pow_split' (by omega), hwm, hwd, hj.2]
      unfold rootOf
      omega
    have hrev : revBits l (rootOf l c + 256 * j) = c := (revBits_eq_iff hlt).mpr hwl
    refine ⟨_, hrev, ?_⟩
    have hpos : d ≠ 0 := by omega
    unfold slotPosO
    rw [hwm, hdd, ite_eq_right hpos, hwd, Nat.mod_eq_of_lt hj.1, ← hjd]
    omega

/-- The slot of a bit pattern that begins with a code word is a position that code word writes. -/
theorem hit_writtenO (hC : Complete (.canonical lens)) (o : Nat → Nat) {s l c w : Nat} (hs : lens[s]? = some l)
    (h0 : l ≠ 0) (hc : code lens s = some c) (hw : revBits l w = c) (base : Nat) :
    ∃ k, k < (if l ≤ 8 then 2 ^ (8 - l) else 2 ^ ((depths lens).getD (rootOf l c) 0 - (l - 8))) ∧
      base + slotPosO (depths lens) o w =
        (if l ≤ 8 then base + revBits l c + k * 2 ^ l
         else base + 256 + o (rootOf l c) + revBits l c / 256 + k * 2 ^ (l - 8)) := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hlt : c < 2 ^ l := code_lt_two_pow (Nat.le_of_eq hC.2) hs h0 hl15 hc
  have hst : revBits l c < 2 ^ l := revBits_lt l c
  have hm : w % 2 ^ l = revBits l c := (revBits_eq_iff hlt).mp hw
  have hhit : Hit (.canonical lens) w l s := ⟨hs, h0, by rw [hc, hw]⟩
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte]
    have hz := hit_short_zero hC hhit hl
    have hi : w % 256 < 2 ^ 8 := Nat.mod_lt _ (by decide)
    have hmm : w % 256 % 2 ^ l = revBits l c := by
      rw [← hm]
      exact Nat.mod_mod_of_dvd w (Nat.pow_dvd_pow 2 hl)
    obtain ⟨k, hk, e⟩ := (range_iff hl hst (w % 256)).mp ⟨hi, hmm⟩
    refine ⟨k, hk, ?_⟩
    unfold slotPosO
    rw [ite_eq_left hz, e, Nat.add_assoc]
  · simp only [hl, ↓reduceIte]
    have hl8 : 8 < l := by omega
    obtain ⟨hd, hroot⟩ := hit_long hC hhit hl8
    rw [hw] at hroot
    rw [hroot]
    generalize hdd : (depths lens).getD (w % 256) 0 = d at hd ⊢
    have hst8 : 2 ^ l = 256 * 2 ^ (l - 8) := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_add]
      congr 1
      omega
    have hj0 : revBits l c / 256 < 2 ^ (l - 8) := Nat.div_lt_of_lt_mul (by rw [← hst8]; exact hst)
    have hsplit : w % 2 ^ l = w % 256 + 256 * ((w / 256) % 2 ^ (l - 8)) := pow_split' (by omega) w
    have hjm : (w / 256) % 2 ^ (l - 8) = revBits l c / 256 := by
      have h256 : w % 256 < 256 := Nat.mod_lt _ (by decide)
      omega
    have hj : (w / 256) % 2 ^ d < 2 ^ d := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hjj : (w / 256) % 2 ^ d % 2 ^ (l - 8) = revBits l c / 256 := by
      rw [← hjm]
      exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hd)
    obtain ⟨k, hk, e⟩ := (range_iff hd hj0 ((w / 256) % 2 ^ d)).mp ⟨hj, hjj⟩
    refine ⟨k, hk, ?_⟩
    have hpos : d ≠ 0 := by omega
    unfold slotPosO
    rw [hdd, ite_eq_right hpos, e]
    omega

/-- Writes a code word's slots, with root slot `r`'s sub-table at `o r`. -/
def writeCodeO (base : Nat) (D : Array Nat) (o : Nat → Nat) (t : ByteArray) (s l c : Nat) : ByteArray :=
  if l ≤ 8 then writeRange l s (2 ^ l) (2 ^ (8 - l)) t (base + revBits l c)
  else
    writeRange l s (2 ^ (l - 8)) (2 ^ (D.getD (rootOf l c) 0 - (l - 8))) t
      (base + 256 + o (rootOf l c) + revBits l c / 256)

theorem size_writeCodeO (base : Nat) (D : Array Nat) (o : Nat → Nat) (t : ByteArray) (s l c : Nat) :
    (writeCodeO base D o t s l c).size = t.size := by
  unfold writeCodeO
  split <;> exact size_writeRange ..

/-- What a code word's write does to the slots, when the slots of the bit patterns that begin with it are in the
array. -/
theorem slotAt_writeCodeO (hC : Complete (.canonical lens)) (o : Nat → Nat) {s l c base : Nat} {t : ByteArray}
    (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c) (hval : s < 4096)
    (hin : ∀ w, revBits l w = c → 2 * (base + slotPosO (depths lens) o w) + 1 < t.size) (q : Nat) :
    ((∃ w, revBits l w = c ∧ q = base + slotPosO (depths lens) o w) →
        slotAt (writeCodeO base (depths lens) o t s l c) q = (l, s)) ∧
      ((¬ ∃ w, revBits l w = c ∧ q = base + slotPosO (depths lens) o w) →
        slotAt (writeCodeO base (depths lens) o t s l c) q = slotAt t q) := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hbits : l < 16 := by omega
  unfold writeCodeO
  by_cases hl : l ≤ 8
  · simp only [hl, ↓reduceIte]
    rw [slotAt_writeRange hbits hval]
    · constructor
      · rintro ⟨w, hw, e⟩
        obtain ⟨k, hk, ew⟩ := hit_writtenO hC o hs h0 hc hw base
        simp only [hl, ↓reduceIte] at hk ew
        rw [ite_eq_left ⟨k, hk, by rw [e, ew]⟩]
      · intro hn
        rw [ite_eq_right]
        rintro ⟨k, hk, e⟩
        have := written_hitO hC o (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
        simp only [hl, ↓reduceIte] at this
        obtain ⟨w, hw, ew⟩ := this
        exact hn ⟨w, hw, by rw [e, ew]⟩
    · intro k hk
      have := written_hitO hC o (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
      simp only [hl, ↓reduceIte] at this
      obtain ⟨w, hw, ew⟩ := this
      have := hin w hw
      omega
  · simp only [hl, ↓reduceIte]
    rw [slotAt_writeRange hbits hval]
    · constructor
      · rintro ⟨w, hw, e⟩
        obtain ⟨k, hk, ew⟩ := hit_writtenO hC o hs h0 hc hw base
        simp only [hl, ↓reduceIte] at hk ew
        rw [ite_eq_left ⟨k, hk, by rw [e, ew]⟩]
      · intro hn
        rw [ite_eq_right]
        rintro ⟨k, hk, e⟩
        have := written_hitO hC o (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
        simp only [hl, ↓reduceIte] at this
        obtain ⟨w, hw, ew⟩ := this
        exact hn ⟨w, hw, by rw [e, ew]⟩
    · intro k hk
      have := written_hitO hC o (base := base) hs h0 hc (k := k) (by simpa [hl] using hk)
      simp only [hl, ↓reduceIte] at this
      obtain ⟨w, hw, ew⟩ := this
      have := hin w hw
      omega

/-! ### The builder -/

/-- Opens root slot `r`'s sub-table at the end of the array, for a code word of length `l`: the root slot records the
length and where the sub-table starts, counted from the table's start. -/
def openSub (base : Nat) (t : ByteArray) (r l : Nat) : ByteArray :=
  writeSlot (t ++ zeros (2 * 2 ^ (l - 8))) (base + r) l (t.size / 2 - base)

/-- Writes a code word's slots, longest code words first. A long code word whose root slot is empty is the deepest
under its root, and opens the root's sub-table; the others find it in the root slot. -/
def downStep (base : Nat) (t : ByteArray) (s l c : Nat) : ByteArray :=
  if l ≤ 8 then writeRange l s (2 ^ l) (2 ^ (8 - l)) t (base + revBits l c)
  else
    let e := slotAt t (base + rootOf l c)
    if e.1 = 0 then writeRange l s (2 ^ (l - 8)) 1 (openSub base t (rootOf l c) l) (t.size / 2 + revBits l c / 256)
    else writeRange l s (2 ^ (l - 8)) (2 ^ (e.1 - l)) t (base + e.2 + revBits l c / 256)

/-- Appends a canonical code's table to the array. Its slots start at `t.size / 2`. -/
def buildDown (t : ByteArray) (lens : List Nat) : ByteArray :=
  walkDown (downStep (t.size / 2)) lens (t ++ zeros 512)

/-- What holds of the table at `base` while it is built, with the symbols `done` written: the root slots in `ops` have
their sub-tables, root slot `r`'s at `o r` past the root, apart from each other; the other root slots that will have one
are empty; and each bit pattern that begins with a code word written has its slot. -/
structure DownInv (lens : List Nat) (t0 : ByteArray) (base : Nat) (done : List Nat) (t : ByteArray) (ops : List Nat)
    (o : Nat → Nat) : Prop where
  size : t.size = 2 * (base + 256 + opSum ops (depths lens) 256)
  frame : ∀ q, q < base → slotAt t q = slotAt t0 q
  opsOk : ∀ r ∈ ops, r < 256 ∧ (depths lens).getD r 0 ≠ 0 ∧
    slotAt t (base + r) = (8 + (depths lens).getD r 0, 256 + o r) ∧
    o r + 2 ^ (depths lens).getD r 0 ≤ opSum ops (depths lens) 256
  disj : ∀ r ∈ ops, ∀ r' ∈ ops, r ≠ r' → Disj (depths lens) o r r'
  empty : ∀ r, r < 256 → r ∉ ops → (depths lens).getD r 0 ≠ 0 → (slotAt t (base + r)).1 = 0
  roots : ∀ s ∈ done, ∀ l c, Long lens s l c → rootOf l c ∈ ops
  hits : ∀ s l w, s ∈ done → Hit (.canonical lens) w l s → slotAt t (base + slotPosO (depths lens) o w) = (l, s)

/-- A bit pattern whose root slot has a sub-table or none has its slot in the array. -/
theorem DownInv.pos_in {t0 t : ByteArray} {base : Nat} {done ops : List Nat} {o : Nat → Nat}
    (h : DownInv lens t0 base done t ops o) {w : Nat} (hw : (depths lens).getD (w % 256) 0 = 0 ∨ w % 256 ∈ ops) :
    2 * (base + slotPosO (depths lens) o w) + 1 < t.size := by
  have hs := h.size
  have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
  unfold slotPosO
  by_cases hz : (depths lens).getD (w % 256) 0 = 0
  · rw [ite_eq_left hz]
    omega
  · rw [ite_eq_right hz]
    have hm := hw.resolve_left hz
    have hb := (h.opsOk _ hm).2.2.2
    have hj : (w / 256) % 2 ^ (depths lens).getD (w % 256) 0 < 2 ^ (depths lens).getD (w % 256) 0 :=
      Nat.mod_lt _ (Nat.two_pow_pos _)
    omega

/-- The root slot of a bit pattern that begins with a code word written has its sub-table, if it has one. -/
theorem DownInv.root_mem (hC : Complete (.canonical lens)) {t0 t : ByteArray} {base : Nat} {done ops : List Nat}
    {o : Nat → Nat} (h : DownInv lens t0 base done t ops o) {s l w : Nat} (hs : s ∈ done)
    (hh : Hit (.canonical lens) w l s) : (depths lens).getD (w % 256) 0 = 0 ∨ w % 256 ∈ ops := by
  by_cases hl : l ≤ 8
  · exact Or.inl (hit_short_zero hC hh hl)
  · obtain ⟨_, hroot⟩ := hit_long hC hh (by omega)
    refine Or.inr ?_
    rw [← hroot]
    exact h.roots s hs l _ ⟨hh.1, by omega, hh.2.2⟩

/-- No code word writes below the table or over a root slot that has or will have a sub-table. -/
private theorem not_written {o : Nat → Nat} {base l c q : Nat}
    (hq : q < base ∨ ∃ r, r < 256 ∧ q = base + r ∧ (depths lens).getD r 0 ≠ 0) :
    ¬ ∃ w, revBits l w = c ∧ q = base + slotPosO (depths lens) o w := by
  rintro ⟨w, _, e⟩
  unfold slotPosO at e
  rcases hq with hq | ⟨r, hr, rfl, hz⟩
  · split at e <;> omega
  · by_cases hw : (depths lens).getD (w % 256) 0 = 0
    · rw [ite_eq_left hw] at e
      have : r = w % 256 := by omega
      subst this
      exact hz hw
    · rw [ite_eq_right hw] at e
      omega

/-- Writing a code word whose root slot, if long, has its sub-table keeps the invariant. -/
theorem DownInv.write (hC : Complete (.canonical lens)) (hlen : lens.length ≤ 704) {t0 t : ByteArray} {base : Nat}
    {done ops : List Nat} {o : Nat → Nat} (h : DownInv lens t0 base done t ops o) {s l c : Nat}
    (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c) (hr : 8 < l → rootOf l c ∈ ops) :
    DownInv lens t0 base (s :: done) (writeCodeO base (depths lens) o t s l c) ops o := by
  have hval : s < 4096 := by
    have := (List.getElem?_eq_some_iff.mp hs).1
    omega
  -- The bit patterns that begin with the code word have their slots in the array.
  have hcode : ∀ w, revBits l w = c → (depths lens).getD (w % 256) 0 = 0 ∨ w % 256 ∈ ops := by
    intro w hw
    have hh : Hit (.canonical lens) w l s := ⟨hs, h0, by rw [hc, hw]⟩
    by_cases hl : l ≤ 8
    · exact Or.inl (hit_short_zero hC hh hl)
    · obtain ⟨_, hroot⟩ := hit_long hC hh (by omega)
      rw [hw] at hroot
      exact Or.inr (hroot ▸ hr (by omega))
  have key := slotAt_writeCodeO hC o (t := t) (base := base) hs h0 hc hval (fun w hw => h.pos_in (hcode w hw))
  refine ⟨?_, ?_, ?_, h.disj, ?_, ?_, ?_⟩
  · rw [size_writeCodeO]
    exact h.size
  · intro q hq
    rw [(key q).2 (not_written (Or.inl hq))]
    exact h.frame q hq
  · intro r hm
    obtain ⟨h1, h2, h3, h4⟩ := h.opsOk r hm
    refine ⟨h1, h2, ?_, h4⟩
    rw [(key _).2 (not_written (Or.inr ⟨r, h1, rfl, h2⟩))]
    exact h3
  · intro r hr' hn hz
    rw [(key _).2 (not_written (Or.inr ⟨r, hr', rfl, hz⟩))]
    exact h.empty r hr' hn hz
  · intro s' hm l' c' hL
    rcases List.mem_cons.mp hm with e | hm
    · subst e
      have e1 := hL.1
      rw [hs] at e1
      simp only [Option.some.injEq] at e1
      have e2 := hL.2.2
      rw [hc] at e2
      simp only [Option.some.injEq] at e2
      subst e1
      subst e2
      exact hr hL.2.1
    · exact h.roots s' hm l' c' hL
  · intro s' l' w hm hh
    rcases List.mem_cons.mp hm with e | hm
    · subst e
      have e1 : l' = l := by
        have := hh.1
        rw [hs] at this
        exact (Option.some.inj this).symm
      rw [e1] at hh ⊢
      have hw : revBits l w = c := by
        have e2 := hh.2.2
        rw [hc] at e2
        simp only [Option.some.injEq] at e2
        exact e2.symm
      exact (key _).1 ⟨w, hw, rfl⟩
    · by_cases hq : ∃ w2, revBits l w2 = c ∧ base + slotPosO (depths lens) o w = base + slotPosO (depths lens) o w2
      · obtain ⟨w2, hw2, e⟩ := hq
        have hpos : slotPosO (depths lens) o w2 = slotPosO (depths lens) o w := by omega
        have hh2 : Hit (.canonical lens) w2 l s := ⟨hs, h0, by rw [hc, hw2]⟩
        obtain ⟨_, hlow⟩ := slotPosO_low hpos (fun hz2 hz e' => by
          have m2 := (hcode w2 hw2).resolve_left hz2
          have m1 := (h.root_mem hC hm hh).resolve_left hz
          exact h.disj _ m2 _ m1 e')
        have hle : l ≤ 8 + (depths lens).getD (w2 % 256) 0 := by
          by_cases hl8 : l ≤ 8
          · omega
          · have := (hit_long hC hh2 (by omega)).1
            omega
        have hh3 := Hit.transfer hh2 hle hlow
        obtain ⟨e1, e2⟩ := hh3.unique hh hC
        subst e1
        subst e2
        exact (key _).1 ⟨w2, hw2, e⟩
      · rw [(key _).2 hq]
        exact h.hits s' l' w hm hh

/-- An empty root slot of a long code word, with every longer code word written, opens the root's sub-table, as deep
as the code word, and keeps the invariant. -/
theorem DownInv.openR (hC : Complete (.canonical lens)) (hlen : lens.length ≤ 704) {t0 t : ByteArray} {base : Nat}
    {done ops : List Nat} {o : Nat → Nat} (h : DownInv lens t0 base done t ops o) {s l c : Nat}
    (hs : lens[s]? = some l) (hc : code lens s = some c) (hl8 : 8 < l)
    (hlong : ∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) (hz : (slotAt t (base + rootOf l c)).1 = 0) :
    (depths lens).getD (rootOf l c) 0 = l - 8 ∧
      DownInv lens t0 base done (openSub base t (rootOf l c) l) (rootOf l c :: ops)
        (fun x => if x = rootOf l c then opSum ops (depths lens) 256 else o x) := by
  have hl15 : l ≤ 15 := hC.1 l (List.mem_of_getElem? hs)
  have hrlt := rootOf_lt l c
  have hdge := (depths_spec hC.1).2.2.2 s l c ⟨hs, hl8, hc⟩
  have hD0 : (depths lens).getD (rootOf l c) 0 ≠ 0 := by omega
  have hnot : rootOf l c ∉ ops := by
    intro hm
    have := (h.opsOk _ hm).2.2.1
    rw [this] at hz
    simp at hz
  have hdeq : (depths lens).getD (rootOf l c) 0 = l - 8 := by
    refine Nat.le_antisymm (Nat.le_of_not_lt fun hgt => ?_) hdge
    obtain ⟨s', l', c', hL, hroot, he⟩ := depths_attain hC.1 _ hD0
    have hmem := hlong s' l' hL.1 (by omega)
    exact hnot (hroot ▸ h.roots s' hmem l' c' hL)
  refine ⟨hdeq, ?_⟩
  generalize hR : rootOf l c = r at hrlt hD0 hnot hdeq ⊢
  generalize hoff : opSum ops (depths lens) 256 = off
  have hsize := h.size
  rw [hoff] at hsize
  have hbound : 256 + off < 4096 := by
    have h1 := opSum_le ops (depths lens) 256
    have h2 := offSum_le hC
    have h3 := longCount_le lens
    omega
  have hop' : opSum (r :: ops) (depths lens) 256 = off + 2 ^ (l - 8) := by
    rw [opSum_cons hnot, ite_eq_left hrlt, hoff]
    unfold subSize
    rw [ite_eq_right hD0, hdeq]
  have hzs := size_zeros (2 * 2 ^ (l - 8))
  have hsz1 : (openSub base t r l).size = t.size + 2 * 2 ^ (l - 8) := by
    unfold openSub
    rw [size_writeSlot, ByteArray.size_append, hzs]
  -- Slots before the old end other than the root slot are unchanged.
  have hkeep : ∀ q, q ≠ base + r → 2 * q + 1 < t.size → slotAt (openSub base t r l) q = slotAt t q := by
    intro q hq hin
    unfold openSub
    rw [slotAt_writeSlot_ne hq, slotAt_append hin]
  have hrootv : slotAt (openSub base t r l) (base + r) = (l, 256 + off) := by
    unfold openSub
    rw [show t.size / 2 - base = 256 + off by omega]
    exact slotAt_writeSlot_same (by rw [ByteArray.size_append, hzs]; omega) (by omega) hbound
  refine ⟨?_, ?_, ?_, ?_, ?_, fun s' hm l' c' hL => List.mem_cons_of_mem _ (h.roots s' hm l' c' hL), ?_⟩
  · rw [hsz1, hop']
    omega
  · intro q hq
    rw [hkeep q (by omega) (by omega)]
    exact h.frame q hq
  · intro x hm
    rcases List.mem_cons.mp hm with e | hm
    · subst e
      refine ⟨hrlt, hD0, ?_, ?_⟩
      · rw [hrootv, hdeq, ite_eq_left rfl]
        congr 1
        omega
      · rw [ite_eq_left rfl, hop', hdeq]
        exact Nat.le_refl _
    · have hxr : x ≠ r := fun e => hnot (e ▸ hm)
      obtain ⟨h1, h2, h3, h4⟩ := h.opsOk x hm
      refine ⟨h1, h2, ?_, ?_⟩
      · rw [hkeep _ (by omega) (by omega), h3, ite_eq_right hxr]
      · rw [ite_eq_right hxr, hop']
        rw [hoff] at h4
        omega
  · intro x hx y hy hxy
    unfold Disj
    dsimp only
    rcases List.mem_cons.mp hx with ex | hx' <;> rcases List.mem_cons.mp hy with ey | hy'
    · exact absurd (ex.trans ey.symm) hxy
    · subst ex
      have hyr : y ≠ x := fun e => hnot (e ▸ hy')
      have := (h.opsOk y hy').2.2.2
      rw [hoff] at this
      rw [ite_eq_left rfl, ite_eq_right hyr]
      exact Or.inr this
    · subst ey
      have hxr : x ≠ y := fun e => hnot (e ▸ hx')
      have := (h.opsOk x hx').2.2.2
      rw [hoff] at this
      rw [ite_eq_left rfl, ite_eq_right hxr]
      exact Or.inl this
    · have hxr : x ≠ r := fun e => hnot (e ▸ hx')
      have hyr : y ≠ r := fun e => hnot (e ▸ hy')
      rw [ite_eq_right hxr, ite_eq_right hyr]
      exact h.disj x hx' y hy' hxy
  · intro x hx hn hz'
    have hxr : x ≠ r := fun e => hn (e ▸ List.mem_cons_self)
    have hn' : x ∉ ops := fun e => hn (List.mem_cons_of_mem _ e)
    rw [hkeep _ (by omega) (by omega)]
    exact h.empty x hx hn' hz'
  · intro s' l' w hm hh
    have hw := h.root_mem hC hm hh
    have hpos : slotPosO (depths lens) (fun x => if x = r then off else o x) w = slotPosO (depths lens) o w := by
      unfold slotPosO
      dsimp only
      by_cases hzw : (depths lens).getD (w % 256) 0 = 0
      · rw [ite_eq_left hzw, ite_eq_left hzw]
      · have hwr : w % 256 ≠ r := fun e => hnot (e ▸ hw.resolve_left hzw)
        rw [ite_eq_right hzw, ite_eq_right hzw, ite_eq_right hwr]
    rw [hpos]
    have hin := h.pos_in hw
    have hne : base + slotPosO (depths lens) o w ≠ base + r := by
      unfold slotPosO
      by_cases hzw : (depths lens).getD (w % 256) 0 = 0
      · rw [ite_eq_left hzw]
        intro e
        have : w % 256 = r := by omega
        exact hD0 (this ▸ hzw)
      · rw [ite_eq_right hzw]
        omega
    rw [hkeep _ hne hin]
    exact h.hits s' l' w hm hh

private theorem writeRange_congr {bits val step count count' pos pos' : Nat} {t : ByteArray} (h1 : count = count')
    (h2 : pos = pos') : writeRange bits val step count t pos = writeRange bits val step count' t pos' := by
  subst h1
  subst h2
  rfl

/-- Each step of `buildDown`, with every longer code word written, keeps the invariant. -/
theorem DownInv.step (hC : Complete (.canonical lens)) (hlen : lens.length ≤ 704) {t0 t : ByteArray} {base : Nat}
    {done ops : List Nat} {o : Nat → Nat} (h : DownInv lens t0 base done t ops o) {s l c : Nat}
    (hs : lens[s]? = some l) (h0 : l ≠ 0) (hc : code lens s = some c)
    (hlong : ∀ s' l', lens[s']? = some l' → l < l' → s' ∈ done) :
    ∃ ops' o', DownInv lens t0 base (s :: done) (downStep base t s l c) ops' o' := by
  unfold downStep
  by_cases hl : l ≤ 8
  · rw [ite_eq_left hl]
    have := h.write hC hlen hs h0 hc (fun h8 => absurd h8 (by omega))
    unfold writeCodeO at this
    rw [ite_eq_left hl] at this
    exact ⟨ops, o, this⟩
  · rw [ite_eq_right hl]
    dsimp only
    have hdge := (depths_spec hC.1).2.2.2 s l c ⟨hs, by omega, hc⟩
    by_cases hz : (slotAt t (base + rootOf l c)).1 = 0
    · rw [ite_eq_left hz]
      obtain ⟨hdeq, h1⟩ := h.openR hC hlen hs hc (by omega) hlong hz
      have h2 := h1.write hC hlen hs h0 hc (fun _ => List.mem_cons_self)
      refine ⟨rootOf l c :: ops, fun x => if x = rootOf l c then opSum ops (depths lens) 256 else o x, ?_⟩
      have hsize := h.size
      have e : writeCodeO base (depths lens) (fun x => if x = rootOf l c then opSum ops (depths lens) 256 else o x)
          (openSub base t (rootOf l c) l) s l c =
          writeRange l s (2 ^ (l - 8)) 1 (openSub base t (rootOf l c) l) (t.size / 2 + revBits l c / 256) := by
        unfold writeCodeO
        rw [ite_eq_right hl, hdeq, Nat.sub_self, Nat.pow_zero]
        dsimp only
        rw [ite_eq_left rfl]
        exact writeRange_congr rfl (by omega)
      rw [← e]
      exact h2
    · rw [ite_eq_right hz]
      have hm : rootOf l c ∈ ops := Classical.byContradiction fun hn =>
        hz (h.empty _ (rootOf_lt l c) hn (by omega))
      obtain ⟨_, _, hslot, _⟩ := h.opsOk _ hm
      have e : writeCodeO base (depths lens) o t s l c =
          writeRange l s (2 ^ (l - 8)) (2 ^ ((slotAt t (base + rootOf l c)).1 - l)) t
            (base + (slotAt t (base + rootOf l c)).2 + revBits l c / 256) := by
        unfold writeCodeO
        rw [ite_eq_right hl, hslot]
        exact writeRange_congr (congrArg (2 ^ ·) (by dsimp only; omega)) (by dsimp only; omega)
      rw [← e]
      exact ⟨ops, o, h.write hC hlen hs h0 hc (fun _ => hm)⟩

/-- The empty table: the root slots appended, all empty. -/
theorem DownInv.init {t : ByteArray} {base : Nat} (hsz : t.size = 2 * base) :
    DownInv lens t base [] (t ++ zeros 512) [] (fun _ => 0) := by
  have h512 := size_zeros 512
  refine ⟨?_, ?_, fun r hm => absurd hm (by simp), fun r hm => absurd hm (by simp), ?_,
    fun s hm => absurd hm (by simp), fun s l w hm => absurd hm (by simp)⟩
  · rw [ByteArray.size_append, h512, opSum_nil]
    omega
  · intro q hq
    exact slotAt_append (by omega)
  · intro r hr _ _
    rw [slotAt_zeros (by omega) (by omega)]

/-- A canonical code's table, built longest code words first, does its job, takes exactly `tableSlots`, and leaves the
tables before it alone. -/
theorem buildDown_spec {t : ByteArray} (hC : Complete (.canonical lens)) (ht : t.size % 2 = 0)
    (hlen : lens.length ≤ 704) :
    TableOk (buildDown t lens) (t.size / 2) (.canonical lens) ∧ (buildDown t lens).size % 2 = 0 ∧
      (∀ q, q < t.size / 2 → slotAt (buildDown t lens) q = slotAt t q) ∧
      (buildDown t lens).size = t.size + 2 * tableSlots (.canonical lens) := by
  generalize hbase : t.size / 2 = base
  have hsz : t.size = 2 * base := by omega
  have hinit : DownInv lens t base [] (t ++ zeros 512) [] (fun _ => 0) := DownInv.init hsz
  obtain ⟨done, ⟨ops, o, inv⟩, hall⟩ := walkDown_ind (f := downStep base) hC
    (fun done t' => ∃ ops o, DownInv lens t base done t' ops o)
    (fun done s l c acc ⟨ops, o, h⟩ hs h0 hc hlong => h.step hC hlen hs h0 hc hlong) ⟨[], fun _ => 0, hinit⟩
  unfold buildDown
  rw [hbase]
  generalize walkDown (downStep base) lens (t ++ zeros 512) = T at inv
  obtain ⟨dS, dLe, dEx, _⟩ := depths_spec hC.1
  -- Every root slot that has a sub-table has it.
  have hops : ∀ r, r < 256 → (depths lens).getD r 0 ≠ 0 → r ∈ ops := by
    intro r _ hz
    obtain ⟨s, l, c, hL, hr⟩ := dEx r hz
    rw [← hr]
    exact inv.roots s (hall s l hL.1 (by have := hL.2.1; omega)) l c hL
  have hsum := opSum_full 256 hops
  have hsize := inv.size
  rw [hsum] at hsize
  refine ⟨⟨⟨by omega, ?_⟩, ?_⟩, by omega, fun q hq => inv.frame q hq, by simp only [tableSlots]; omega⟩
  · intro r hr hbig
    by_cases hm : r ∈ ops
    · obtain ⟨_, _, h3, h4⟩ := inv.opsOk r hm
      rw [hsum] at h4
      rw [h3]
      have := dLe r
      refine ⟨by dsimp only; omega, ?_⟩
      dsimp only
      rw [show 8 + (depths lens).getD r 0 - 8 = (depths lens).getD r 0 by omega]
      omega
    · exfalso
      have hz : (depths lens).getD r 0 = 0 := Classical.byContradiction fun hz => hm (hops r hr hz)
      obtain ⟨l, s, hh⟩ := hit_exists hC r
      have hk := inv.hits s l r (hall s l hh.1 hh.2.1) hh
      have hmod : r % 256 = r := Nat.mod_eq_of_lt hr
      have hp : slotPosO (depths lens) o r = r := by
        unfold slotPosO
        rw [hmod, ite_eq_left hz]
      rw [hp] at hk
      rw [hk] at hbig
      have := (hit_long hC hh hbig).1
      rw [hmod, hz] at this
      simp only at hbig
      omega
  · intro w
    obtain ⟨l, s, hh⟩ := hit_exists hC w
    have hk := inv.hits s l w (hall s l hh.1 hh.2.1) hh
    unfold slotPosO at hk
    unfold lookupSlots
    dsimp only
    by_cases hz : (depths lens).getD (w % 256) 0 = 0
    · rw [ite_eq_left hz] at hk
      have hl8 : l ≤ 8 := Nat.le_of_not_lt fun hg => by
        have := (hit_long hC hh hg).1
        omega
      rw [hk]
      simp only [hl8, ↓reduceIte]
      exact hh
    · rw [ite_eq_right hz] at hk
      have hr : w % 256 < 256 := Nat.mod_lt _ (by decide)
      obtain ⟨_, _, h3, _⟩ := inv.opsOk _ (hops _ hr hz)
      rw [h3]
      simp only [show ¬ 8 + (depths lens).getD (w % 256) 0 ≤ 8 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [show base + (256 + o (w % 256)) + w / 256 % 2 ^ (depths lens).getD (w % 256) 0 =
        base + (256 + o (w % 256) + w / 256 % 2 ^ (depths lens).getD (w % 256) 0) by omega, hk]
      exact hh

end Build

/-! ### A code's table -/

/-- Appends a single-symbol code's table: all 256 root slots hold the symbol, with no bits to read. -/
def buildSingle (t : ByteArray) (sym : Nat) : ByteArray :=
  writeRange 0 sym 1 256 (t ++ zeros 512) (t.size / 2)

theorem buildSingle_spec {t : ByteArray} {sym : Nat} (ht : t.size % 2 = 0) (hsym : sym < 4096) :
    TableOk (buildSingle t sym) (t.size / 2) (.single sym) ∧ (buildSingle t sym).size % 2 = 0 ∧
      (∀ q, q < t.size / 2 → slotAt (buildSingle t sym) q = slotAt t q) ∧
      (buildSingle t sym).size = t.size + 2 * 256 := by
  have h512 := size_zeros 512
  generalize ht1 : t ++ zeros 512 = t1 at *
  have hs1 : t1.size = t.size + 512 := by
    rw [← ht1, ByteArray.size_append, h512]
  unfold buildSingle
  rw [ht1]
  have hsz := size_writeRange 0 sym 1 256 t1 (t.size / 2)
  have hin : ∀ k, k < 256 → 2 * (t.size / 2 + k * 1) + 1 < t1.size := by
    intro k hk
    omega
  have hat := slotAt_writeRange (bits := 0) (val := sym) (step := 1) (by decide) hsym 256 t1 (t.size / 2)
  have hroot : ∀ r, r < 256 → slotAt (writeRange 0 sym 1 256 t1 (t.size / 2)) (t.size / 2 + r) = (0, sym) := by
    intro r hr
    rw [hat _ hin, ite_eq_left ⟨r, hr, by omega⟩]
  refine ⟨⟨⟨by rw [hsz, hs1]; omega, ?_⟩, ?_⟩, by rw [hsz, hs1]; omega, ?_, by rw [hsz, hs1]⟩
  · intro r hr hb
    rw [hroot r hr] at hb
    simp at hb
  · intro w
    unfold lookupSlots
    dsimp only
    rw [hroot _ (Nat.mod_lt _ (by decide))]
    exact ⟨rfl, rfl⟩
  · intro q hq
    rw [hat _ hin, ite_eq_right (by
      rintro ⟨k, _, e⟩
      omega), ← ht1]
    exact slotAt_append (by omega)

/-- Appends a code's table to the arena. Its slots start at `t.size / 2`. -/
def buildTable (t : ByteArray) : PrefixCode → ByteArray
  | .single sym => buildSingle t sym
  | .canonical lens => buildDown t lens

/-- The symbols of a code fit in a slot, with room for the sub-tables' places. -/
def SlotFits : PrefixCode → Prop
  | .single sym => sym < 4096
  | .canonical lens => lens.length ≤ 704

/-- A built table does its job, takes exactly `tableSlots`, and leaves the tables before it alone. -/
theorem buildTable_spec {t : ByteArray} {c : PrefixCode} (hC : Complete c) (ht : t.size % 2 = 0) (hf : SlotFits c) :
    TableOk (buildTable t c) (t.size / 2) c ∧ (buildTable t c).size % 2 = 0 ∧
      (∀ q, q < t.size / 2 → slotAt (buildTable t c) q = slotAt t q) ∧
      (buildTable t c).size = t.size + 2 * tableSlots c := by
  cases c with
  | single sym =>
    simp only [buildTable, tableSlots]
    exact buildSingle_spec ht hf
  | canonical lens =>
    simp only [buildTable]
    exact buildDown_spec hC ht hf

end Brotli.Decoder
