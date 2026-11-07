module

public import Brotli.Decoder.StreamCall

@[expose] public section

/-!
# What a state holds

Memory usage correctness's measure and demand, and what each step does to what the state holds. The demand counts the window the stream
declares, the bytes the decoder reserves for the tables of its headers' groups of prefix codes, one meta-block at a time,
and a fixed cost for the rest.
-/

namespace Brotli.Decoder

open Brotli.Spec

/-! ### The demand -/

/-- What a state holds besides its window and the groups' tables: the arena's reservation for the categories' codes, the
bounds `HSize` gives, which are more than an empty header reading and the bounds `HSmall` give, since a header's reading
and a meta-block's fast header are never held together, 38 bytes of a dictionary word, and its fields; and `smallMax`
more, for an array a step still holds while it builds the array that replaces it: the categories' arena, which the
groups' reservation copies (`arena_reserve_le`), a context map's table, or the code length code's table and its lists
(`HSize.replaced_le`), or a dictionary word. The decoder's constant arrays, 202558 bytes (`constArrays_size`), are the
program's and are not counted. -/
def fixedCost : Nat := 71820

/-- At a place of stage at most 6, which a context map's place is, the categories' arena is at most `smallMax`. -/
theorem arena_reserve_le {d : Done} {g : Gh} {n : Nat} (hu : Upto d g n) (hn : n ≤ 6) : d.arena.size ≤ smallMax :=
  Nat.le_trans hu.le (Nat.le_of_eq (hu.small hn))

/-- A context map's table, and the code length code's table with its lists' 68 bytes, are each at most `smallMax`. -/
theorem HSize.replaced_le {st : Hd} (h : HSize st) : st.mapT.t.size ≤ smallMax ∧ st.clt.t.size + 68 ≤ smallMax := by
  have h1 := h.mapT
  have h2 := h.clt
  have hs : smallMax = 6472 := rfl
  omega

/-- The decoder's constant arrays: the dictionary, the zero block, the lookup tables, and the arrays an empty state holds. -/
theorem constArrays_size : dictBytes.size + zeroBlock.size + cmdLut.size + transLut.size + contextLut.size + nextNone.size +
    Tab.none.t.size + rev8Lut.size + mtfInitLut.size + countLut.size + lenLut.size + headNone.size + clOrderLut.size =
      202558 := by
  have h1 : zeroBlock.size = 65536 := by
    show zeroBlock.data.size = _
    rw [zeroBlock_data, Array.size_replicate]
  have h2 : Tab.none.t.size = 512 := by
    show (zeroBytes 512).size = 512
    exact zeroBytes_size (by decide)
  have h3 := dictBytes_size
  have h4 := cmdLut_size
  have h5 := transLut_size
  have h6 := contextLut_size
  have h7 := nextNone_size
  have h8 := rev8Lut_size
  have h9 := mtfInit_is.sz
  have h10 := countLut_size
  have h11 := lenLut_size
  have h12 := headNone_size
  have h13 := clOrderLut_size
  generalize dictBytes.size = a1 at h3 ⊢
  generalize zeroBlock.size = a2 at h1 ⊢
  generalize cmdLut.size = a3 at h4 ⊢
  generalize transLut.size = a4 at h5 ⊢
  generalize contextLut.size = a5 at h6 ⊢
  generalize nextNone.size = a6 at h7 ⊢
  generalize Tab.none.t.size = a7 at h2 ⊢
  generalize rev8Lut.size = a8 at h8 ⊢
  generalize mtfInitLut.size = a9 at h9 ⊢
  generalize countLut.size = a10 at h10 ⊢
  generalize lenLut.size = a11 at h11 ⊢
  generalize headNone.size = a12 at h12 ⊢
  generalize clOrderLut.size = a13 at h13 ⊢
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  rfl

/-- What a state's fields cost. -/
def fieldBytes : Nat := 1024

/-- A header's reading, counting the bytes the decoder reserves for its groups' tables once both context maps are read:
`treeMax` of each group's alphabet for each of its codes. These are the decoder's own table layout's bytes, from the
header's fields, not a size RFC 7932 defines. -/
def tableK : HK Nat := ⟨fun _ _ => some 0, fun g x => some (resBytes g + x.getD 0)⟩

/-- The bytes of the tables a meta-block's header needs, as far as its bits go. -/
def headerTables (bs : List Bool) : Nat :=
  match metaStart bs with
  | some (.data _ _ false, b) => (hrest tableK Gh.start (.cat .L) b).getD 0
  | _ => 0

/-- The most bytes of tables any meta-block from here needs, as far as the bits go. -/
def blocksT (w : Nat) (st : StreamState) (bs : List Bool) : Nat :=
  max (headerTables bs) (match _h : readMetaBlock w st bs with
    | some ((st1, last), b) => if last then 0 else blocksT w st1 b
    | none => 0)
termination_by bs.length
decreasing_by exact readMetaBlock_lt _h

theorem blocksT_eq (w : Nat) (st : StreamState) (bs : List Bool) : blocksT w st bs =
    max (headerTables bs) ((readMetaBlock w st bs).elim 0 fun p => if p.1.2 then 0 else blocksT w p.1.1 p.2) := by
  conv => lhs; rw [blocksT]
  split <;> rename_i h <;> rw [h] <;> rfl

theorem headerTables_le (w : Nat) (st : StreamState) (bs : List Bool) : headerTables bs ≤ blocksT w st bs := by
  rw [blocksT_eq]
  exact Nat.le_max_left _ _

/-- What a place is worth to the demand: the most bytes of tables the meta-blocks after it need. -/
def demandSem : Sem Nat where
  after w last st bs := some (if last then 0 else blocksT w st bs)
  block w st bs := some (blocksT w st bs)
  finish _ _ := some 0
  first bs := readWBITS bs >>= fun p => some (blocksT (windowSize p.1) ⟨[], 0, initialDistances⟩ p.2)
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- The window the decoder allocates, from a meta-block's start with nothing produced and a declared window `w`: at the
stream's first meta-block with data, past any metadata, the declared window for uncompressed bytes, and for compressed
ones the window they are read with (`blockWindow`), which for a last meta-block holds just its bytes. None if the stream
ends first, or its bits do. -/
def winFrom (w : Nat) (bs : List Bool) : Option Nat :=
  match _h : metaStart bs with
  | some (.metadata last skip, b) =>
    match _h2 : readFill b with
    | some b1 => if b1.length < skip * 8 then none else if last then none else winFrom w (b1.drop (skip * 8))
    | none => none
  | some (.data last mlen unc, b) => if unc then (readFill b).map fun _ => w else some (blockWindow w ⟨[], 0, initialDistances⟩ last mlen)
  | some (.lastEmpty, _) => none
  | none => none
termination_by bs.length
decreasing_by
  have h3 := takes_one faith_metaStart rfl _h
  have h4 := readFill_len _h2
  simp only [List.length_drop]
  omega

/-- What a place is worth to the window: the window the decoder allocates from there, while it has none. -/
def winSem : Sem Nat where
  after w last st bs := if last then none else if st.produced = 0 then winFrom w bs else some w
  block w st bs := if st.produced = 0 then winFrom w bs else some w
  finish _ _ := none
  first bs := readWBITS bs >>= fun p => winFrom (windowSize p.1) p.2
  after_true _ _ _ := rfl
  after_false _ _ _ := rfl
  first_eq _ := rfl

/-- The bytes of the window the decoder allocates for a stream, as far as its bits go. -/
def windowBytes (bs : List Bool) : Nat := (winSem.first bs).elim 0 (· + 16)

/-- What the input so far demands. -/
def demand (y : List UInt8) : Nat := fixedCost + windowBytes (bits y) + (demandSem.first (bits y)).getD 0

theorem window_eq (bs : List Bool) : (winSem.first bs).elim 0 (· + 16) = windowBytes bs := rfl

/-- A meta-block of data from a meta-block's start with nothing produced: the window it allocates. -/
theorem winFrom_data {w : Nat} {bs b : List Bool} {last : Bool} {mlen : Nat} {unc : Bool}
    (h : metaStart bs = some (.data last mlen unc, b)) :
    winFrom w bs = if unc then (readFill b).map (fun _ => w) else some (blockWindow w ⟨[], 0, initialDistances⟩ last mlen) := by
  rw [winFrom]
  split <;> rename_i e <;> rw [h] at e <;> cases e <;> rfl

/-- Metadata from a meta-block's start with nothing produced: the window after it. -/
theorem winFrom_meta {w : Nat} {bs b : List Bool} {last : Bool} {skip : Nat} (h : metaStart bs = some (.metadata last skip, b)) :
    winFrom w bs = readFill b >>= fun b1 => if b1.length < skip * 8 then none else if last then none else winFrom w (b1.drop (skip * 8)) := by
  rw [winFrom]
  split <;> rename_i e <;> rw [h] at e <;> cases e
  split <;> rename_i e2 <;> rw [e2] <;> rfl

/-- Neither metadata nor data from a meta-block's start: no window. -/
theorem winFrom_none {w : Nat} {bs : List Bool} (h : ∀ v b, metaStart bs = some (v, b) → v = .lastEmpty) : winFrom w bs = none := by
  rw [winFrom]
  split <;> rename_i e <;> first | rfl | cases h _ _ e

/-- Away from data, the window allocated from a meta-block's start with nothing produced is what leaving it is worth. -/
theorem winFrom_leave {w : Nat} {st : StreamState} {bs b : List Bool} {v : MetaStart} (hst : st.produced = 0)
    (hm : metaStart bs = some (v, b)) (hv : ∀ l ml u, v ≠ .data l ml u) : winFrom w bs = sLeave winSem (.mblock w st) bs := by
  show _ = (metaStart bs >>= fun p => afterStart w (winSem.after w) st p.1 p.2)
  rw [hm]
  cases v with
  | lastEmpty =>
    rw [winFrom_none (fun v' b' e => by rw [hm] at e; cases e; rfl)]
    rfl
  | metadata last skip =>
    rw [winFrom_meta hm]
    show _ = (readFill b >>= fun b1 => if b1.length < skip * 8 then none else
      (if last = true then none else if st.produced = 0 then winFrom w (b1.drop (skip * 8)) else some w))
    simp only [hst, ↓reduceIte]
  | data l ml u => exact absurd rfl (hv l ml u)

/-- The window allocated is at most the declared one. -/
theorem winFrom_le (w : Nat) : ∀ (n : Nat) (bs : List Bool), bs.length = n → ∀ v, winFrom w bs = some v → v ≤ w := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro bs hn v hv
    cases hm : metaStart bs with
    | none =>
      rw [winFrom_none (fun v b e => by rw [hm] at e; cases e)] at hv
      cases hv
    | some p =>
      obtain ⟨ms, b⟩ := p
      have hlt := takes_one faith_metaStart rfl hm
      cases ms with
      | lastEmpty =>
        rw [winFrom_none (fun v b' e => by rw [hm] at e; cases e; rfl)] at hv
        cases hv
      | metadata last skip =>
        rw [winFrom_meta hm] at hv
        cases hf : readFill b with
        | none => rw [hf] at hv; cases hv
        | some b1 =>
          rw [hf] at hv
          have hl := readFill_len hf
          dsimp only [bind, Option.bind] at hv
          split at hv
          · cases hv
          · split at hv
            · cases hv
            · exact ih _ (by rw [← hn, List.length_drop]; omega) _ rfl v hv
      | data last mlen unc =>
        rw [winFrom_data hm] at hv
        cases unc with
        | true =>
          cases hf : readFill b with
          | none => rw [ite_eq_left rfl, hf] at hv; simp at hv
          | some b1 =>
            rw [ite_eq_left rfl, hf] at hv
            simp only [Option.map_some, Option.some.injEq] at hv
            omega
        | false =>
          rw [ite_eq_right (fun e => Bool.noConfusion e)] at hv
          cases hv
          exact blockWindow_le _ _ _ _

/-- Leaving a meta-block's start is worth no more than arriving at it. -/
theorem leave_le (w : Nat) (st : StreamState) (bs : List Bool) : (sLeave demandSem (.mblock w st) bs).getD 0 ≤ blocksT w st bs := by
  show (metaStart bs >>= fun p => afterStart w (demandSem.after w) st p.1 p.2).getD 0 ≤ _
  rw [← block_start w (demandSem.after w) st bs, blocksT_eq]
  cases readMetaBlock w st bs with
  | none => exact Nat.zero_le _
  | some p =>
    show (if p.1.2 = true then 0 else blocksT w p.1.1 p.2) ≤ max (headerTables bs) (if p.1.2 = true then 0 else blocksT w p.1.1 p.2)
    exact Nat.le_max_right _ _

/-- What a move's hook adds to the demand: the groups' reservation. -/
def resOf : Option Hook → Nat
  | some (.res g) => resBytes g
  | _ => 0

theorem wr_tableK (oc : Option Hook) (x : Option Nat) : (Wr tableK oc x).getD 0 = resOf oc + x.getD 0 := by
  match oc with
  | none => exact (Nat.zero_add _).symm
  | some (.table _) => exact (Nat.zero_add _).symm
  | some (.res _) => rfl

/-! ### A ceiling on the demand -/

private theorem bind_getD_le {α : Type} {o : Option α} {f : α → Option Nat} {M : Nat} (h : ∀ a, o = some a → (f a).getD 0 ≤ M) :
    (o >>= f).getD 0 ≤ M := by
  cases ho : o with
  | none => exact Nat.zero_le _
  | some a => exact h a ho

private theorem hCodesR_le {size M : Nat} {G : List PrefixCode → List Bool → Option Nat} (hG : ∀ cs b, (G cs b).getD 0 ≤ M) :
    ∀ (n : Nat) (done : List PrefixCode) (bs : List Bool), (hCodesR size G done n bs).getD 0 ≤ M
  | 0, done, bs => hG done bs
  | n + 1, done, _ => bind_getD_le fun q _ => hCodesR_le hG n (done ++ [q.1]) q.2

private theorem hCodesL_le (g : Gh) (done : List PrefixCode) (left : Nat) (bs : List Bool) :
    (hCodesL tableK g done left bs).getD 0 ≤ 0 :=
  hCodesR_le (fun _ b => hCodesR_le (fun _ b' => hCodesR_le (fun _ _ => Nat.le_refl 0) g.treesD [] b') g.m.insertCopy.n [] b)
    left done bs

/-- A context map's number of trees is at most 256. -/
private theorem readTreesAndMap_trees {size : Nat} {bs r : List Bool} {p : Nat × List Nat} (h : readTreesAndMap size bs = some (p, r)) :
    p.1 ≤ 256 := by
  unfold readTreesAndMap at h
  cases h1 : readVarLen bs with
  | none => rw [h1] at h; cases h
  | some q =>
    obtain ⟨n, b1⟩ := q
    rw [h1] at h
    have hn := (readVarLen_range h1).2
    dsimp only [bind, Option.bind] at h
    split at h
    · cases h
      exact hn
    · cases h2 : readContextMap size n b1 with
      | none => rw [h2] at h; cases h
      | some u =>
        rw [h2] at h
        cases h
        exact hn

private theorem hMap_le (g : Gh) (hI : g.m.insertCopy.n ≤ 256) (hp : g.m.npostfix ≤ 3) (hn : g.m.ndirect ≤ 120) (bs : List Bool) :
    (hMap tableK g true bs).getD 0 ≤ resMax := by
  refine bind_getD_le fun p hp1 => ?_
  have h1 := readTreesAndMap_trees hp1
  show (readTreesAndMap (distanceContextMapSize g.m.distance.n) p.2 >>= fun q =>
    tableK.r { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 }
      (hCodesL tableK { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 }
        [] p.1.1 q.2)).getD 0 ≤ _
  refine bind_getD_le fun q hq => ?_
  have h2 := readTreesAndMap_trees hq
  have h3 := hCodesL_le { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 }
    [] p.1.1 q.2
  have h4 := resBytes_bound (g := { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 })
    h1 hI h2 hp hn
  show resBytes { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 } +
    (hCodesL tableK { g with m := { g.m with literalMap := p.1.2, distanceMap := q.1.2 }, treesL := p.1.1, treesD := q.1.1 }
      [] p.1.1 q.2).getD 0 ≤ _
  omega

private theorem hModes_le (g : Gh) (hI : g.m.insertCopy.n ≤ 256) (hp : g.m.npostfix ≤ 3) (hn : g.m.ndirect ≤ 120)
    (done : List Nat) (left : Nat) (bs : List Bool) : (hModes tableK g done left bs).getD 0 ≤ resMax :=
  bind_getD_le fun p _ => hMap_le _ hI hp hn p.2

private theorem hNp_le (g : Gh) (hI : g.m.insertCopy.n ≤ 256) (bs : List Bool) : (hNp tableK g bs).getD 0 ≤ resMax :=
  bind_getD_le fun np h1 => bind_getD_le fun nd h2 => by
    have a1 : np.1 < 2 ^ 2 := readInt_lt 2 _ np.1 np.2 h1
    have a2 : nd.1 < 2 ^ 4 := readInt_lt 4 _ nd.1 nd.2 h2
    have key : ∀ x, x < 4 → ∀ y, y < 16 → y <<< x ≤ 120 := by decide
    have hd : nd.1 <<< np.1 ≤ 120 := key _ (by omega) _ (by omega)
    exact hModes_le { g with m := { g.m with npostfix := np.1, ndirect := nd.1 <<< np.1 } } hI (show np.1 ≤ 3 by omega) hd []
      g.m.literal.n nd.2

private theorem hCatR_le {N : BlockCategory → List Bool → Option Nat} {M : Nat} (hN : ∀ c b, c.n ≤ 256 → (N c b).getD 0 ≤ M)
    (bs : List Bool) : (hCatR N bs).getD 0 ≤ M := by
  refine bind_getD_le fun p hp => ?_
  have hn := (readVarLen_range hp).2
  split
  · exact hN _ _ hn
  · exact bind_getD_le fun q _ => bind_getD_le fun u _ => bind_getD_le fun v _ => hN ⟨p.1, q.1, u.1, v.1⟩ v.2 hn

private theorem hCatD_le (g : Gh) (hI : g.m.insertCopy.n ≤ 256) (bs : List Bool) : (hCatD tableK g bs).getD 0 ≤ resMax :=
  hCatR_le (fun c b _ => hNp_le { g with m := { g.m with distance := c } } hI b) bs

private theorem hCatI_le (g : Gh) (bs : List Bool) : (hCatI tableK g bs).getD 0 ≤ resMax :=
  hCatR_le (fun c b hc => hCatD_le { g with m := { g.m with insertCopy := c } } hc b) bs

private theorem hCatL_le (g : Gh) (bs : List Bool) : (hCatL tableK g bs).getD 0 ≤ resMax :=
  hCatR_le (fun c b _ => hCatI_le { g with m := { g.m with literal := c } } b) bs

/-- What a header reserves for its tables is at most `resMax`, whatever its bits. -/
theorem headerTables_le_max (bs : List Bool) : headerTables bs ≤ resMax := by
  unfold headerTables
  split
  · exact hCatL_le _ _
  · exact Nat.zero_le _

theorem blocksT_le_max : ∀ (n w : Nat) (st : StreamState) (bs : List Bool), bs.length = n → blocksT w st bs ≤ resMax := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro w st bs hn
    rw [blocksT_eq]
    refine Nat.max_le.mpr ⟨headerTables_le_max bs, ?_⟩
    cases h : readMetaBlock w st bs with
    | none => exact Nat.zero_le _
    | some p =>
      show (if p.1.2 then 0 else blocksT w p.1.1 p.2) ≤ _
      split
      · exact Nat.zero_le _
      · exact ih _ (by rw [← hn]; exact readMetaBlock_lt h) w p.1.1 p.2 rfl

/-- The demand never exceeds the declared window by more than a constant: the fixed cost, the ring's 16 bytes beyond the
window, and the most a header reserves for its tables. The window allocated is at most the declared one. -/
theorem demand_ceiling : DemandCeiling demand (fixedCost + 16 + resMax) := by
  intro y
  unfold demand declaredWindow windowBytes
  have ht : (demandSem.first (bits y)).getD 0 ≤ resMax :=
    bind_getD_le fun p _ => blocksT_le_max _ _ _ _ rfl
  show fixedCost + (readWBITS (bits y) >>= fun p => winFrom (windowSize p.1) p.2).elim 0 (· + 16) + _ ≤ _
  cases h : readWBITS (bits y) with
  | none =>
    show fixedCost + 0 + _ ≤ 0 + _
    omega
  | some p =>
    show fixedCost + (winFrom (windowSize p.1) p.2).elim 0 (· + 16) + _ ≤ windowSize p.1 + _
    cases hw : winFrom (windowSize p.1) p.2 with
    | none =>
      show fixedCost + 0 + _ ≤ windowSize p.1 + _
      omega
    | some v =>
      have := winFrom_le (windowSize p.1) _ p.2 rfl v hw
      show fixedCost + (v + 16) + _ ≤ windowSize p.1 + _
      omega

/-! ### The measure -/

/-- The bytes a settled record holds: its arena's reservation, and its arrays. -/
def Done.holds (d : Done) : Nat := d.arenaCap.toNat + d.modes.size + d.lMap.size + d.dMap.size + d.litBase.size + d.icBase.size + d.dBase.size

/-- The bytes a header's reading holds. -/
def Hd.holds (h : Hd) : Nat := h.d.holds + h.fill.size + h.head.size + h.next.size + h.clLens.size + h.clt.t.size + h.mapT.t.size +
  h.xf.size + h.mtf.size + h.seenR.size + h.seenX.size

/-- The bytes a meta-block's fast header holds: its arena's reservation, and its arrays. -/
def Hdr.holds (H : Hdr) : Nat := H.arenaCap.toNat + H.litBase.size + H.lMap.size + H.icBase.size + H.dBase.size + H.dMap.size + H.modes.size +
  H.lTriv.size

/-- The bytes a state holds, and a constant for its fields. -/
def Dec.holds (D : Dec) : Nat := D.cmd.ring.size + D.cmd.wordBuf.size + D.hd.holds + D.H.holds + fieldBytes

/-- The bytes a fast header holds outside its arena, with bounds set by the format. -/
structure HSmall (H : Hdr) : Prop where
  litBase : H.litBase.size ≤ 1024
  lMap : H.lMap.size ≤ 16384
  icBase : H.icBase.size ≤ 1024
  dBase : H.dBase.size ≤ 1024
  dMap : H.dMap.size ≤ 1024
  modes : H.modes.size ≤ 256
  lTriv : H.lTriv.size ≤ 1024

/-- A fast header's shared table bases: 4 bytes for each literal block type, of which there are at most 256. -/
theorem triv_le {H : Hdr} (h : H.lMap.size ≤ 16384) : H.lTriv.size ≤ 1024 := by
  have := H.trivSize
  have := H.lMapSize
  omega

/-- Why a stream's memory limit was reached: `L` is below what it needs, and not because it was clipped. -/
def MemWhy (Ws : Option Nat) (X L : Nat) : Prop := L < Ws.elim 0 (· + 16) + X ∧ L < 4294958151

/-- What a state holds, for a stream whose window's worth is `Ws`, whose tables' worth is `X`, and with `L` left for the window and
the tables. `B` is the bits still to be read. In a header, the arena's reservation and what the rest of the header reserves
are within the categories' reservation and `X`, and the arena's tables still to come fit what it reserved. -/
structure MemD (Ws : Option Nat) (X L : Nat) (D : Dec) (B : List Bool) : Prop where
  place : ∃ p, DRel D p ∧ (sLeave demandSem p B).getD 0 ≤ X
  block : D.tag = .mblock → headerTables B ≤ X
  hdr : D.tag = .hdr → ∃ g q, HRel D.hd g q ∧ D.hd.d.arenaCap.toNat + (hrest tableK g q B).getD 0 ≤ smallMax + X ∧
    D.hd.d.arenaMax = D.limit ∧ D.hd.d.arena.size + budH g q ≤ D.hd.d.arenaCap.toNat
  cmds : D.tag = .cmds → D.H.arenaCap.toNat ≤ smallMax + X ∧ D.H.arenaCap.toNat ≤ smallMax + D.limit.toNat ∧
    D.H.arena.size ≤ D.H.arenaCap.toNat
  hdOut : D.tag ≠ .hdr → D.hd = Hd.none
  HOut : D.tag ≠ .cmds → D.H = Hdr.none
  hd : HSize D.hd
  H : HSmall D.H
  win : (D.cmd.ring.size = 0 ∧ D.cmd.wordBuf.size = 0 ∧ D.limit.toNat = L ∧ ∃ p, DRel D p ∧ srest winSem p B = Ws) ∨
    (D.cmd.ring.size ≠ 0 ∧ ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L)

/-- What a state's place says of its arrays, once it has a window. -/
theorem DRel.arrays {D : Dec} {p : SPhase} (h : DRel D p) (hr : D.cmd.ring.size ≠ 0) :
    D.cmd.ring.size = 2 ^ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.cmd.wordBuf.size ≤ 38 := by
  have hwin : ∀ {w st}, WinAll D w st → D.cmd.ring.size = 2 ^ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.cmd.wordBuf.size ≤ 38 :=
    fun a => ⟨a.win.ring.size, a.win.k24, a.win.wordLe⟩
  have hat : ∀ {w st}, WinAt D w st → D.cmd.ring.size = 2 ^ D.k.toNat ∧ D.k.toNat ≤ 24 ∧ D.cmd.wordBuf.size ≤ 38 := by
    intro w st a
    rcases a with ⟨a, _⟩ | a
    · exact hwin a
    · exact absurd a.ring hr
  cases p with
  | wbits => exact absurd h.2.2.2.2 hr
  | mblock => exact hat h.2.2
  | skip => exact hat h.2.2.1
  | raw => exact hwin h.2.2.1
  | hdr => exact hwin h.2.1
  | cmds => exact h.2.2.2.2.1.arrays
  | ended =>
    obtain ⟨_, _, _, a⟩ := h
    exact hat a

/-- A state with no window is at WBITS, a meta-block's start, metadata or the stream's end. -/
theorem DRel.noRing {D : Dec} {p : SPhase} (h : DRel D p) (hr : D.cmd.ring.size = 0) :
    D.tag ≠ .hdr ∧ D.tag ≠ .cmds ∧ D.tag ≠ .raw := by
  have hwin : ∀ {w st}, WinAll D w st → False := fun a => by
    have h1 := a.win.ring.size
    have h2 := Nat.two_pow_pos D.k.toNat
    omega
  cases p with
  | raw => exact absurd h.2.2.1 (fun a => hwin a)
  | hdr => exact absurd h.2.1 (fun a => hwin a)
  | cmds =>
    have h1 := h.2.2.2.2.1.arrays.1
    have h2 := Nat.two_pow_pos D.k.toNat
    omega
  | wbits => rw [h.1]; decide
  | mblock => rw [h.1]; decide
  | skip => rw [h.1]; decide
  | ended => rw [h.1]; decide

/-- A place with no window yet. -/
theorem WinAt.noRing {D : Dec} {w : Nat} {st : StreamState} (h : WinAt D w st) (hr : D.cmd.ring.size = 0) : NoRing D w st := by
  rcases h with ⟨a, _⟩ | a
  · have h1 := a.win.ring.size
    have h2 := Nat.two_pow_pos D.k.toNat
    omega
  · exact a

/-- A state with no window yet stands for one place. -/
theorem DRel.noRing_eq {D : Dec} {p q : SPhase} (hp : DRel D p) (hq : DRel D q) (hr : D.cmd.ring.size = 0) : p = q := by
  obtain ⟨n1, n2, n3⟩ := hp.noRing hr
  have ht : ∀ {x y : DTag}, D.tag = x → D.tag = y → x = y := fun a b => a.symm.trans b
  cases p with
  | raw => exact absurd hp.1 n3
  | hdr => exact absurd hp.1 n1
  | cmds => exact absurd hp.1 n2
  | wbits =>
    cases q with
    | wbits => rfl
    | _ => exact absurd (ht hp.1 hq.1) (fun e => DTag.noConfusion e)
  | mblock w st =>
    cases q with
    | mblock w' st' =>
      have a := hp.2.2.noRing hr
      have b := hq.2.2.noRing hr
      have e1 : w = w' := by have := a.win; have := b.win; omega
      rw [e1, a.st, b.st]
    | _ => exact absurd (ht hp.1 hq.1) (fun e => DTag.noConfusion e)
  | skip w st last n =>
    cases q with
    | skip w' st' last' n' =>
      have a := hp.2.2.1.noRing hr
      have b := hq.2.2.1.noRing hr
      have e1 : w = w' := by have := a.win; have := b.win; omega
      have e2 : last = last' := hp.2.2.2.1.symm.trans hq.2.2.2.1
      have e3 : n = n' := hp.2.2.2.2.1.symm.trans hq.2.2.2.2.1
      rw [e1, e2, e3, a.st, b.st]
    | _ => exact absurd (ht hp.1 hq.1) (fun e => DTag.noConfusion e)
  | ended st =>
    cases q with
    | ended st' =>
      obtain ⟨_, _, w, a⟩ := hp
      obtain ⟨_, _, w', b⟩ := hq
      rw [(a.noRing hr).st, (b.noRing hr).st]
    | _ => exact absurd (ht hp.1 hq.1) (fun e => DTag.noConfusion e)

/-- What a header reading holds, for any reading. -/
private theorem holds_eq (h : Hd) : h.holds = h.d.holds + h.fill.size + h.head.size + h.next.size + h.clLens.size +
    h.clt.t.size + h.mapT.t.size + h.xf.size + h.mtf.size + h.seenR.size + h.seenX.size := rfl

private theorem dholds_eq (d : Done) : d.holds = d.arenaCap.toNat + d.modes.size + d.lMap.size + d.dMap.size +
    d.litBase.size + d.icBase.size + d.dBase.size := rfl

/-- An empty header reading holds its two lists and two empty tables. Proved field by field: unfolding `Hd.holds` at
`Hd.none` directly cost the kernel 66 s, as it unfolded the constant first (lean-facts). -/
theorem hdNone_holds : Hd.none.holds = 2464 := by
  have h1 : Hd.none.head.size = 32 := headNone_size
  have h2 : Hd.none.next.size = 1408 := nextNone_size
  have h3 : Hd.none.clt.t.size = 512 := by show (zeroBytes 512).size = 512; exact zeroBytes_size (by decide)
  have h4 : Hd.none.mapT.t.size = 512 := by show (zeroBytes 512).size = 512; exact zeroBytes_size (by decide)
  have f0 : Hd.none.fill.size = 0 := rfl
  have c0 : Hd.none.clLens.size = 0 := rfl
  have x0 : Hd.none.xf.size = 0 := rfl
  have m0 : Hd.none.mtf.size = 0 := rfl
  have r0 : Hd.none.seenR.size = 0 := rfl
  have s0 : Hd.none.seenX.size = 0 := rfl
  have d0 : Hd.none.d.holds = 0 := by
    rw [dholds_eq]
    rfl
  rw [holds_eq, h1, h2, h3, h4, f0, c0, x0, m0, r0, s0, d0]

/-- An empty fast header holds nothing. -/
theorem hdrNone_holds : Hdr.none.holds = 0 := rfl

/-- What a state holds is within what the stream demands and what's left of the limit. -/
theorem MemD.holds_le {Ws : Option Nat} {X L : Nat} {D : Dec} {B : List Bool} (M : MemD Ws X L D B) :
    D.holds ≤ fixedCost + Ws.elim 0 (· + 16) + X ∧ D.holds ≤ fixedCost + L := by
  obtain ⟨p, hrel, _⟩ := M.place
  have a1 := M.hd.fill
  have a2 := M.hd.lens
  have a3 := M.hd.clLens
  have a4 := M.hd.clt
  have a5 := M.hd.mapT
  have a6 := M.hd.modes
  have a7 := M.hd.lMap
  have a8 := M.hd.dMap
  have a9 := M.hd.litBase
  have a10 := M.hd.icBase
  have a11 := M.hd.dBase
  have a12 := M.hd.work
  have b1 := M.H.litBase
  have b2 := M.H.lMap
  have b3 := M.H.icBase
  have b4 := M.H.dBase
  have b5 := M.H.dMap
  have b6 := M.H.modes
  have b7 := M.H.lTriv
  have hsm : smallMax = 6472 := rfl
  have hhd : D.hd.holds ≤ D.hd.d.arenaCap.toNat + 57814 := by unfold Hd.holds Done.holds; omega
  have hHH : D.H.holds ≤ D.H.arenaCap.toNat + 21760 := by unfold Hdr.holds; omega
  have h0 : Hd.none.d.arenaCap.toNat = 0 := rfl
  have h0' : Hdr.none.arenaCap.toNat = 0 := rfl
  -- A header's reading and a meta-block's fast header are never held together.
  have hex : D.hd.holds + D.H.holds ≤ D.hd.d.arenaCap.toNat + D.H.arenaCap.toNat + 57814 := by
    by_cases t1 : D.tag = .hdr
    · rw [M.HOut (by rw [t1]; decide), hdrNone_holds]
      omega
    · rw [M.hdOut t1, hdNone_holds]
      omega
  unfold Dec.holds fixedCost fieldBytes
  rcases M.win with ⟨r0, w0, hl, _⟩ | ⟨ht, w, hw, hk, hl⟩
  · obtain ⟨n1, n2, _⟩ := hrel.noRing r0
    rw [M.hdOut n1, M.HOut n2, hdNone_holds, hdrNone_holds]
    omega
  · obtain ⟨r1, _, w1⟩ := hrel.arrays ht
    have he : (some w : Option Nat).elim 0 (· + 16) = w + 16 := rfl
    rw [hw, he]
    have hA : D.hd.d.arenaCap.toNat + D.H.arenaCap.toNat ≤ smallMax + X ∧
        D.hd.d.arenaCap.toNat + D.H.arenaCap.toNat ≤ smallMax + D.limit.toNat := by
      by_cases t1 : D.tag = .hdr
      · obtain ⟨g, q, hR, h1, h2, _⟩ := M.hdr t1
        have h3 : D.H.arenaCap.toNat = 0 := by rw [M.HOut (by rw [t1]; decide)]; rfl
        have hle := hR.2.1.capLe
        rw [h2] at hle
        omega
      · have h3 : D.hd.d.arenaCap.toNat = 0 := by rw [M.hdOut t1]; rfl
        by_cases t2 : D.tag = .cmds
        · obtain ⟨c1, c2, -⟩ := M.cmds t2
          omega
        · have h4 : D.H.arenaCap.toNat = 0 := by rw [M.HOut t2]; rfl
          omega
    omega

/-- A state with what it holds unchanged, but for its place. -/
theorem MemD.move {Ws : Option Nat} {X L : Nat} {D D' : Dec} {B B' : List Bool} (M : MemD Ws X L D B) (hB : B' = B) (hp : ∃ p, DRel D' p ∧ (sLeave demandSem p B').getD 0 ≤ X)
    (hR : ∀ p, DRel D p → DRel D' p)
    (e1 : D'.tag = D.tag) (e2 : D'.cmd.ring = D.cmd.ring) (e4 : D'.cmd.wordBuf = D.cmd.wordBuf) (e5 : D'.hd = D.hd) (e6 : D'.H = D.H)
    (e7 : D'.k = D.k) (e8 : D'.limit = D.limit) : MemD Ws X L D' B' := by
  subst hB
  refine ⟨hp, fun h => M.block (e1 ▸ h), fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_, ?_, ?_⟩
  · rw [e5, e8]
    exact M.hdr (e1 ▸ h)
  · rw [e6, e8]
    exact M.cmds (e1 ▸ h)
  · rw [e5]
    exact M.hdOut (e1 ▸ h)
  · rw [e6]
    exact M.HOut (e1 ▸ h)
  · rw [e5]
    exact M.hd
  · rw [e6]
    exact M.H
  · rw [e2, e4, e7, e8]
    rcases M.win with ⟨a1, a2, a3, p, a4, a5⟩ | h
    · exact Or.inl ⟨a1, a2, a3, p, hR p a4, a5⟩
    · exact Or.inr h

/-! ### What a step leaves -/

/-- Arriving at a place, what the state holds is settled for leaving it. -/
theorem arrive {X : Nat} {D : Dec} {p : SPhase} {B : List Bool} (hrel : DRel D p) (h : (srest demandSem p B).getD 0 ≤ X) :
    (sLeave demandSem p B).getD 0 ≤ X ∧ (D.tag = .mblock → headerTables B ≤ X) := by
  cases p with
  | mblock w st =>
    have h' : blocksT w st B ≤ X := h
    exact ⟨Nat.le_trans (leave_le w st B) h', fun _ => Nat.le_trans (headerTables_le w st B) h'⟩
  | wbits => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | skip => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | raw => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | hdr => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | cmds => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩
  | ended => exact ⟨h, fun e => absurd (hrel.1.symm.trans e) (by decide)⟩

/-- A step's place and bits, given what the place was worth. -/
theorem placed {X : Nat} {a : ByteArray} {stop : USize} {p : SPhase} {D r : Dec} {t : List UInt8}
    (hrel : DRel D p) (hstep : DStepOk demandSem a stop p D D.pos r) (hw : (sLeave demandSem p (D.bits a D.pos stop (bits t))).getD 0 ≤ X)
    (hblock : D.tag = .mblock → headerTables (D.bits a D.pos stop (bits t)) ≤ X) (hn0 : r.status ≠ .memory) (hn1 : r.status ≠ .bad) (hpaused : r.status ≠ .next → r.tag = D.tag) :
    (∃ p', DRel r p' ∧ (sLeave demandSem p' (r.bits a r.pos stop (bits t))).getD 0 ≤ X) ∧ (r.tag = .mblock → headerTables (r.bits a r.pos stop (bits t)) ≤ X) := by
  cases hs : r.status with
  | memory => exact absurd hs hn0
  | bad => exact absurd hs hn1
  | next =>
    obtain ⟨p', hR, _, _, heq, _, _⟩ := hstep.next hs
    rw [heq] at hw
    obtain ⟨h1, h2⟩ := arrive hR hw
    exact ⟨⟨p', hR, h1⟩, h2⟩
  | needsInput =>
    obtain ⟨_, _, p', hR, heq, _, _, hb, _⟩ := hstep.needsInput hs
    rw [heq] at hw
    refine ⟨⟨p', hR, hw⟩, fun e => ?_⟩
    have ht : D.tag = .mblock := by rw [← hpaused (by rw [hs]; decide)]; exact e
    cases p with
    | mblock w st =>
      rw [hb w st rfl t]
      exact hblock ht
    | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | needsOutput =>
    obtain ⟨p', hR, _, _, heq, _, _, hb, _⟩ := hstep.needsOutput hs
    rw [heq] at hw
    refine ⟨⟨p', hR, hw⟩, fun e => ?_⟩
    have ht : D.tag = .mblock := by rw [← hpaused (by rw [hs]; decide)]; exact e
    cases p with
    | mblock w st =>
      rw [hb w st rfl t]
      exact hblock ht
    | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)

/-- What the loop or a step leaves, for what a state holds. -/
structure StepM (Ws : Option Nat) (X L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (r : Dec) : Prop where
  go : r.status ≠ .memory → r.status ≠ .bad → MemD Ws X L r (r.bits a r.pos stop (bits t))
  why : r.status = .memory → MemWhy Ws X L

/-- The cap on waiting bytes doesn't matter to what a state holds. -/
theorem MemD.withCap {Ws : Option Nat} {X L : Nat} {D : Dec} {B : List Bool} (M : MemD Ws X L D B) (x : USize) :
    MemD Ws X L { D with cmd := { D.cmd with cap := x } } B := by
  obtain ⟨p, h1, h2⟩ := M.place
  refine ⟨⟨p, h1.withCap x, h2⟩, M.block, M.hdr, M.cmds, M.hdOut, M.HOut, M.hd, M.H, ?_⟩
  rcases M.win with ⟨a1, a2, a3, q, a4, a5⟩ | h
  · exact Or.inl ⟨a1, a2, a3, q, a4.withCap x, a5⟩
  · exact Or.inr h

/-- What a state outside a header holds for its window, moved on with the same window. -/
def MemD.winOf (Ws : Option Nat) (L : Nat) (r : Dec) (B' : List Bool) : Prop :=
  (r.cmd.ring.size = 0 ∧ r.cmd.wordBuf.size = 0 ∧ r.limit.toNat = L ∧ ∃ p, DRel r p ∧ srest winSem p B' = Ws) ∨
    (r.cmd.ring.size ≠ 0 ∧ ∃ w, Ws = some w ∧ w + 16 = 2 ^ r.k.toNat ∧ r.limit.toNat + 2 ^ r.k.toNat = L)

/-- A window kept by a step. -/
theorem MemD.winKeep {Ws : Option Nat} {X L : Nat} {D r : Dec} {B B' : List Bool} (M : MemD Ws X L D B) (hr : D.cmd.ring.size ≠ 0)
    (ek : r.k = D.k) (el : r.limit = D.limit) (er : r.cmd.ring.size = D.cmd.ring.size) : MemD.winOf Ws L r B' := by
  rcases M.win with ⟨a1, _⟩ | ⟨_, w, h1, h2, h3⟩
  · exact absurd a1 hr
  · exact Or.inr ⟨by rw [er]; exact hr, w, h1, by rw [ek]; exact h2, by rw [ek, el]; exact h3⟩

/-- A state outside a header, moved to another such state. -/
theorem MemD.keep {Ws : Option Nat} {X L : Nat} {D r : Dec} {B B' : List Bool} (M : MemD Ws X L D B) (hnh : D.tag ≠ .hdr)
    (ed : r.hd = D.hd) (hrh : r.tag ≠ .hdr) (hH : HSmall r.H)
    (hc : r.tag = .cmds → r.H.arenaCap.toNat ≤ smallMax + X ∧ r.H.arenaCap.toNat ≤ smallMax + r.limit.toNat ∧
      r.H.arena.size ≤ r.H.arenaCap.toNat)
    (hO : r.tag ≠ .cmds → r.H = Hdr.none)
    (hp : ∃ p, DRel r p ∧ (sLeave demandSem p B').getD 0 ≤ X) (hb : r.tag = .mblock → headerTables B' ≤ X)
    (hw : MemD.winOf Ws L r B') : MemD Ws X L r B' :=
  ⟨hp, hb, fun e => absurd e hrh, hc, fun _ => by rw [ed]; exact M.hdOut hnh, hO, by rw [ed]; exact M.hd, hH, hw⟩

private theorem ite_status_ne (c : Prop) [Decidable c] : (if c then DStatus.next else DStatus.needsInput) ≠ .memory := by
  split <;> decide

theorem stepDSkip_keeps (stop : USize) (D : Dec) (pos : USize) (ht : D.tag = .skip) :
    (stepDSkip stop D pos).k = D.k ∧ (stepDSkip stop D pos).limit = D.limit ∧ (stepDSkip stop D pos).hd = D.hd ∧ (stepDSkip stop D pos).H = D.H ∧
      (stepDSkip stop D pos).status ≠ .memory ∧ ((stepDSkip stop D pos).status ≠ .next → (stepDSkip stop D pos).tag = D.tag) ∧
      (stepDSkip stop D pos).tag ≠ .wbits ∧ (stepDSkip stop D pos).tag ≠ .hdr ∧ (stepDSkip stop D pos).tag ≠ .cmds := by
  unfold stepDSkip moveOn
  dsimp only
  have h1 : D.tag ≠ .wbits ∧ D.tag ≠ .hdr ∧ D.tag ≠ .cmds := by rw [ht]; decide
  split
  · refine ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, ?_⟩
    show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _
    split <;> decide
  · split
    · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, h1⟩
    · split
      · refine ⟨rfl, rfl, rfl, rfl, ?_, fun _ => rfl, h1⟩
        exact ite_status_ne _
      · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩

theorem stepDRaw_keeps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) (ht : D.tag = .raw) :
    (stepDRaw a stop hs D pos).k = D.k ∧ (stepDRaw a stop hs D pos).limit = D.limit ∧ (stepDRaw a stop hs D pos).hd = D.hd ∧ (stepDRaw a stop hs D pos).H = D.H ∧
      (stepDRaw a stop hs D pos).status ≠ .memory ∧ ((stepDRaw a stop hs D pos).status ≠ .next → (stepDRaw a stop hs D pos).tag = D.tag) ∧
      (stepDRaw a stop hs D pos).tag ≠ .wbits ∧ (stepDRaw a stop hs D pos).tag ≠ .hdr ∧ (stepDRaw a stop hs D pos).tag ≠ .cmds := by
  unfold stepDRaw takeRing moveOn
  dsimp only
  have h1 : D.tag ≠ .wbits ∧ D.tag ≠ .hdr ∧ D.tag ≠ .cmds := by rw [ht]; decide
  split
  · refine ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, ?_⟩
    show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _
    split <;> decide
  · split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩
      · unfold rawFinish
        dsimp only
        refine ⟨rfl, rfl, rfl, rfl, ?_, fun _ => rfl, h1⟩
        exact ite_status_ne _
    · exact ⟨rfl, rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, h1⟩

theorem stepDCmds_keeps (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    (stepDCmds a stop hs D pos).k = D.k ∧ (stepDCmds a stop hs D pos).limit = D.limit ∧ (stepDCmds a stop hs D pos).hd = D.hd ∧
      (stepDCmds a stop hs D pos).status ≠ .memory ∧ ((stepDCmds a stop hs D pos).status ≠ .next → (stepDCmds a stop hs D pos).tag = D.tag) ∧
      (((stepDCmds a stop hs D pos).tag = D.tag ∧ (stepDCmds a stop hs D pos).H = D.H) ∨
        ((stepDCmds a stop hs D pos).tag ≠ .wbits ∧ (stepDCmds a stop hs D pos).tag ≠ .hdr ∧ (stepDCmds a stop hs D pos).tag ≠ .cmds ∧ (stepDCmds a stop hs D pos).H = Hdr.none)) := by
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmd D.H D.k a stop hs cmdBudget D.cmd pos = r
  split
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩
  · split
    · refine ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun e => absurd rfl e, Or.inr ?_⟩
      show (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ (if D.last = true then DTag.ended else DTag.mblock) ≠ _ ∧ _
      refine ⟨?_, ?_, ?_, rfl⟩ <;> split <;> decide
    · exact ⟨rfl, rfl, rfl, (fun e => DStatus.noConfusion e), fun _ => rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- Metadata's step keeps the window and the dictionary word. -/
theorem stepDSkip_win (stop : USize) (D : Dec) (pos : USize) :
    (stepDSkip stop D pos).cmd.ring = D.cmd.ring ∧ (stepDSkip stop D pos).cmd.wordBuf = D.cmd.wordBuf := by
  unfold stepDSkip moveOn
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- The loop for uncompressed bytes keeps the window's size. -/
theorem rawRun_size (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24)
    (hmask : mask.toNat = 2 ^ k - 1) : ∀ (N : Nat) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray)
    (wpos : USize) (p1 p2 : UInt8) (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k),
    n.toNat = N → (rawRun a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp).ring.size = 2 ^ k := by
  intro N
  induction N with
  | zero =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp hN
    rw [rawRun, dite_eq_left (usize_zero hN)]
    exact hsize
  | succ N ih =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp hN
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [rawRun, dite_eq_right hn]
    dsimp only
    split
    · exact ih _ _ _ _ _ _ _ _ _ _ _ (by rw [hpred]; omega)
    · split
      · exact ih _ _ _ _ _ _ _ _ _ _ _ (by rw [hpred]; omega)
      · exact hsize

/-- Uncompressed bytes' step keeps the window's size. -/
theorem stepDRaw_ring (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (D : Dec) (pos : USize) :
    (stepDRaw a stop hs D pos).cmd.ring.size = D.cmd.ring.size := by
  unfold stepDRaw takeRing moveOn rawFinish clearCmd clearRing
  dsimp only
  split
  · rfl
  · split
    · rename_i h
      split
      · rfl
      · exact (rawRun_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl).trans (winCheck_size h.1).symm
    · rfl

/-- The commands' step keeps the window's size. -/
theorem stepDCmds_ring {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m p)) (hp : pos.toNat ≤ stop.toNat) :
    (stepDCmds a stop hs D pos).status ≠ .bad → (stepDCmds a stop hs D pos).cmd.ring.size = D.cmd.ring.size := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨_, _, _, hH, hR, -⟩ := hrel
  have hstep := runCmd_ok (hs := hs) (K := cmdK w (specSem.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
  have h0 : cmd.ring.size = 2 ^ k.toNat := hR.arrays.1
  unfold stepDCmds takeCmd
  dsimp only
  generalize runCmd H k a stop hs cmdBudget cmd pos = r at hstep
  intro hb
  cases hst : r.status with
  | next =>
    obtain ⟨p', hR', -⟩ := hstep.next hst
    show r.ring.size = cmd.ring.size
    rw [hR'.arrays.1, h0]
  | needsInput =>
    obtain ⟨-, -, p', hR', -⟩ := hstep.needsInput hst
    show r.ring.size = cmd.ring.size
    rw [hR'.arrays.1, h0]
  | needsOutput =>
    obtain ⟨p', hR', -⟩ := hstep.needsOutput hst
    show r.ring.size = cmd.ring.size
    rw [hR'.arrays.1, h0]
  | done =>
    obtain ⟨s, hR', -⟩ := hstep.done hst
    have e : r.ring.size = cmd.ring.size := by rw [hR'.arrays.1, h0]
    dsimp only
    split <;> exact e
  | bad =>
    rw [hst] at hb
    exact absurd rfl hb

/-- The commands' step keeps the window's size, whatever its status. -/
theorem stepDCmds_ring' {w : Nat} {last : Bool} {m : MetaBlockHeader} {p : Phase} {a : ByteArray} {stop : USize}
    {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} (hrel : DRel D (.cmds w last m p)) (hp : pos.toNat ≤ stop.toNat) :
    (stepDCmds a stop hs D pos).cmd.ring.size = D.cmd.ring.size := by
  by_cases hb : (stepDCmds a stop hs D pos).status = .bad
  · revert hb
    obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
    obtain ⟨_, _, _, hH, hR, -⟩ := hrel
    have hstep := runCmd_ok (hs := hs) (K := cmdK w (specSem.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
    have hbad := runCmd_badWin (hs := hs) (K := cmdK w (specSem.after w last') m) (a := a) (fun s bs h0 => cmdK_step s bs h0) hH _ cmdBudget p cmd pos rfl hR hp
    have h0 : cmd.ring.size = 2 ^ k.toNat := hR.arrays.1
    unfold stepDCmds takeCmd
    dsimp only
    generalize runCmd H k a stop hs cmdBudget cmd pos = r at hstep hbad
    cases hst : r.status with
    | bad =>
      intro _
      obtain ⟨p1, st1, h1, h2⟩ := hbad hst
      show r.ring.size = cmd.ring.size
      rw [h2.1, h1.arrays.1, h0]
    | done =>
      obtain ⟨s, hR', -⟩ := hstep.done hst
      have e : r.ring.size = cmd.ring.size := by rw [hR'.arrays.1, h0]
      dsimp only
      split <;> (intro _; exact e)
    | next => intro e; cases e
    | needsInput => intro e; cases e
    | needsOutput => intro e; cases e
  · exact stepDCmds_ring hrel hp hb

/-- `Hdr.none` holds nothing. -/
theorem hsmall_none : HSmall Hdr.none :=
  ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-- `Hd.none` holds only small tables. -/
theorem hsize_none : HSize Hd.none where
  fill := Nat.zero_le _
  lens := ⟨Nat.le_of_eq Hd.none.headSz, Nat.le_of_eq Hd.none.nextSz⟩
  clLens := Nat.zero_le _
  clt := by
    show (zeroBytes 512).size ≤ 788
    rw [zeroBytes_size (by decide)]
    decide
  mapT := by
    show (zeroBytes 512).size ≤ 1296
    rw [zeroBytes_size (by decide)]
    decide
  modes := Nat.zero_le _
  lMap := Nat.zero_le _
  dMap := Nat.zero_le _
  litBase := Nat.zero_le _
  icBase := Nat.zero_le _
  dBase := Nat.zero_le _
  work := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

/-! ### WBITS -/

/-- What WBITS's step does to what a state holds: nothing, as it allocates no window. -/
structure WbitsFacts (D : Dec) (r : Dec) : Prop where
  hd : r.hd = D.hd
  H : r.H = D.H
  same : r.limit = D.limit ∧ r.cmd.ring = D.cmd.ring ∧ r.cmd.wordBuf = D.cmd.wordBuf
  paused : r.status ≠ .next → r.tag = D.tag
  next : r.status = .next → r.tag = .mblock
  memory : r.status ≠ .memory

theorem stepDWbits_facts {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize} :
    WbitsFacts D (stepDWbits a stop hs D pos) := by
  unfold stepDWbits
  split
  · dsimp only
    split
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, fun e => absurd rfl e, fun _ => rfl, fun e => DStatus.noConfusion e⟩
  · exact ⟨rfl, rfl, ⟨rfl, rfl, rfl⟩, fun _ => rfl, fun e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩

/-- WBITS's step. -/
theorem wbits_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .wbits) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDWbits a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  have hp0 : p = .wbits := by
    cases p with
    | wbits => rfl
    | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
    | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
    | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
    | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
    | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
    | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  subst hp0
  have hWin : D.cmd.ring.size = 0 ∧ D.cmd.wordBuf.size = 0 ∧ D.limit.toNat = L ∧
      srest winSem .wbits (D.bits a D.pos stop (bits t)) = Ws := by
    rcases M.win with ⟨a1, a2, a3, q, a4, a5⟩ | ⟨a1, _⟩
    · rw [hrel.noRing_eq a4 a1]
      exact ⟨a1, a2, a3, a5⟩
    · exact absurd hrel.2.2.2.2 a1
  obtain ⟨hr0, hwb0, hL, hWs⟩ := hWin
  have hF := stepDWbits_facts (a := a) (stop := stop) (hs := hs) (D := D) (pos := D.pos)
  have hD := stepDWbits_ok (S := demandSem) (a := a) (hs := hs) hrel hp
  have hW := stepDWbits_ok (S := winSem) (a := a) (hs := hs) hrel hp
  generalize stepDWbits a stop hs D D.pos = r at hF hD hW
  obtain ⟨g1, g2, g3⟩ := hF.same
  refine ⟨fun h0 h1 => ?_, fun e => absurd e hF.memory⟩
  obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) h0 h1 hF.paused
  have hHO : D.H = Hdr.none := M.HOut (by rw [ht]; decide)
  have hdO : D.hd = Hd.none := M.hdOut (by rw [ht]; decide)
  have htag : r.tag ≠ .hdr ∧ r.tag ≠ .cmds := by
    by_cases hn : r.status = .next
    · rw [hF.next hn]; decide
    · rw [hF.paused hn, ht]; decide
  have hwin : ∃ p', DRel r p' ∧ srest winSem p' (r.bits a r.pos stop (bits t)) = Ws := by
    cases hst : r.status with
    | next =>
      obtain ⟨p', hR, _, _, heq, _⟩ := hW.next hst
      exact ⟨p', hR, by rw [← heq t]; exact hWs⟩
    | needsInput =>
      obtain ⟨_, _, p', hR, heq, _, hdown, _⟩ := hW.needsInput hst
      cases p' with
      | wbits => exact ⟨.wbits, hR, by rw [← hWs]; exact (heq t).symm⟩
      | _ => exact hdown.elim
    | needsOutput =>
      obtain ⟨p', hR, _, _, heq, _, hdown, _⟩ := hW.needsOutput hst
      cases p' with
      | wbits => exact ⟨.wbits, hR, by rw [← hWs]; exact (heq t).symm⟩
      | _ => exact hdown.elim
    | memory => exact absurd hst h0
    | bad => exact absurd hst h1
  exact ⟨hA, hB, fun e => absurd e htag.1, fun e => absurd e htag.2, fun _ => by rw [hF.hd]; exact hdO, fun _ => by rw [hF.H]; exact hHO,
    by rw [hF.hd]; exact M.hd, by rw [hF.H]; exact M.H, Or.inl ⟨by rw [g2]; exact hr0, by rw [g3]; exact hwb0, by rw [g1]; exact hL, hwin⟩⟩

/-! ### A meta-block's start -/

/-- What a meta-block's start does to what a state holds. With no window yet, the stream's first meta-block with data
allocates it, or finds the limit too low for it. -/
structure MetaFacts (a : ByteArray) (stop : USize) (D : Dec) (pos : USize) (r : Dec) : Prop where
  H : r.H = D.H
  paused : r.status ≠ .next → r.tag = D.tag
  other : r.tag ≠ .hdr → r.hd = D.hd
  tag : r.tag ≠ .wbits ∧ r.tag ≠ .cmds
  start : r.tag = .hdr → r.status = .next ∧ (∀ t : List UInt8, ∃ last mlen, metaStart (D.bits a pos stop (bits t)) = some (.data last mlen false, r.bits a r.pos stop (bits t))) ∧
    HRel r.hd Gh.start (.cat .L) ∧ r.hd.d.arena.size = arenaPre ∧ r.hd.d.arenaCap.toNat = smallMax ∧ r.hd.d.arenaMax = r.limit ∧
    HSize r.hd
  plain : r.status = .next → r.tag ≠ .hdr → ∀ t : List UInt8, ∃ v rest, metaStart (D.bits a pos stop (bits t)) = some (v, rest) ∧
    ∀ l ml, v ≠ .data l ml false
  same : r.status ≠ .memory → (D.cmd.ring.size ≠ 0 ∨ ¬ (r.status = .next ∧ (r.tag = .raw ∨ r.tag = .hdr))) →
    r.k = D.k ∧ r.limit = D.limit ∧ r.cmd.ring = D.cmd.ring ∧ r.cmd.wordBuf = D.cmd.wordBuf
  nodata : r.status = .next → (r.tag = .skip ∨ r.tag = .ended) → ∀ t : List UInt8, ∃ v rest,
    metaStart (D.bits a pos stop (bits t)) = some (v, rest) ∧ ∀ l ml u, v ≠ .data l ml u
  alloc : D.cmd.ring.size = 0 → r.status = .next → (r.tag = .raw ∨ r.tag = .hdr) →
    r.limit.toNat + 2 ^ r.k.toNat = D.limit.toNat ∧ r.cmd.ring.size = 2 ^ r.k.toNat ∧ r.cmd.wordBuf.size = 0 ∧
    ∀ t : List UInt8, ∃ W, winFrom (2 ^ D.k.toNat - 16) (D.bits a pos stop (bits t)) = some W ∧ W + 16 = 2 ^ r.k.toNat
  memory : r.status = .memory → D.cmd.ring.size = 0 ∧ r.limit = D.limit ∧ pos.toNat ≤ r.pos.toNat ∧ r.pos.toNat ≤ stop.toNat ∧
    8 * r.pos.toNat + D.cmd.count.toNat ≤ 8 * pos.toNat + 64 ∧
    (∀ s : List UInt8, ∃ W, winFrom (2 ^ D.k.toNat - 16) ((BitBuffer.mk D.cmd.word D.cmd.count).held ++ (chunkBits a pos.toNat r.pos.toNat ++ bits s)) = some W ∧
      D.limit.toNat < W + 16) ∧
    ∀ t : List UInt8, ∃ W, winFrom (2 ^ D.k.toNat - 16) (D.bits a pos stop (bits t)) = some W ∧ D.limit.toNat < W + 16

/-- The header machine's first state holds only small tables. -/
theorem hsize_start (word count limit : UInt64) : HSize (hdStart word count limit) where
  fill := Nat.zero_le _
  lens := ⟨Nat.le_of_eq (hdStart word count limit).headSz, Nat.le_of_eq (hdStart word count limit).nextSz⟩
  clLens := Nat.zero_le _
  clt := hsize_none.clt
  mapT := hsize_none.mapT
  modes := Nat.zero_le _
  lMap := Nat.zero_le _
  dMap := Nat.zero_le _
  litBase := Nat.zero_le _
  icBase := Nat.zero_le _
  dBase := Nat.zero_le _
  work := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem stepDMeta_facts {w : Nat} {st : StreamState} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {pos : USize}
    (hrel : DRel D (.mblock w st)) (hpos : pos.toNat ≤ stop.toNat) : MetaFacts a stop D pos (stepDMeta a stop hs D pos) := by
  obtain ⟨tag, cmd, hd, H, k, last', left, limit, pos', status⟩ := D
  obtain ⟨ht, hw, hall⟩ := hrel
  have ht' : tag = .mblock := ht
  subst ht'
  have hlim : limit.toNat + 9144 < 2 ^ 32 := hall.limit
  have hdec : (DTag.mblock ≠ DTag.wbits) ∧ (DTag.mblock ≠ DTag.cmds) := by decide
  have hnh : DTag.mblock ≠ DTag.hdr := by decide
  have hku : k.toUInt64.toNat = k.toNat := USize.toNat_toUInt64 k
  unfold stepDMeta
  by_cases hz0 : cmd.pend = 0
  rotate_left
  · rw [ite_eq_right hz0]
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  rw [ite_eq_left hz0]
  rw [dite_eq_left (USize.le_iff_toNat_le.mpr hpos)]
  dsimp only
  obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := cmd.word) (count := cmd.count) hs hpos hw
  have hbits : ∀ F, availBits cmd.word cmd.count a pos stop F =
      availBits (refill cmd.word cmd.count a pos stop hs hpos).word (refill cmd.word cmd.count a pos stop hs hpos).count a
        (refill cmd.word cmd.count a pos stop hs hpos).pos stop F := by
    intro F
    show (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
      (refill cmd.word cmd.count a pos stop hs hpos).buf.held ++ (chunkBits a (refill cmd.word cmd.count a pos stop hs hpos).pos.toNat stop.toNat ++ F)
    rw [← List.append_assoc, ← List.append_assoc, r4]
  obtain ⟨l1, l2⟩ := refill_local (word := cmd.word) (count := cmd.count) hs hpos hw
  generalize refill cmd.word cmd.count a pos stop hs hpos = rf at r1 r2 r3 r4 r5 hbits l1 l2
  have hloc : ∀ s : List UInt8, (BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits s) =
      (BitBuffer.mk rf.word rf.count).held ++ bits s := by
    intro s
    rw [← List.append_assoc, ← l1]
    rfl
  have hwhole : ∀ t : List UInt8, (bits t).length % 8 = 0 := fun t => by rw [bits_length]; omega
  have R := metaStartFast_ok (b0 := ⟨rf.word, rf.count⟩) r1
  have hval := R.ok
  generalize metaStartFast ⟨rf.word, rf.count⟩ = r at hval
  cases hsr : r.status with
  | short =>
    dsimp only
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | bad =>
    dsimp only
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
      fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
  | ok =>
    dsimp only
    have hw2 := (hval hsr).1
    have hms : ∀ t : List UInt8, metaStart (availBits cmd.word cmd.count a pos stop (bits t)) =
        some (msValue r, r.buf.held ++ (chunkBits a rf.pos.toNat stop.toNat ++ bits t)) := fun t => by
      rw [hbits]
      exact (hval hsr).2 _
    have hmsL : ∀ s : List UInt8, metaStart ((BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits s)) =
        some (msValue r, r.buf.held ++ bits s) := fun s => by
      rw [hloc]
      exact (hval hsr).2 _
    unfold metaGo
    by_cases h0 : r.a = 0
    · rw [ite_eq_left h0]
      have hv0 : msValue r = .lastEmpty := by
        unfold msValue
        rw [ite_eq_left h0]
      exact ⟨rfl, fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
        fun e => DTag.noConfusion e, fun _ _ t => ⟨msValue r, _, hms t, fun l ml e => MetaStart.noConfusion (hv0.symm.trans e)⟩,
        fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ t => ⟨msValue r, _, hms t, fun l ml u e => MetaStart.noConfusion (hv0.symm.trans e)⟩,
        (fun _ _ h => by rcases h with e | e <;> cases e), fun e => DStatus.noConfusion e⟩
    rw [ite_eq_right h0]
    by_cases h1 : r.a = 1
    · rw [ite_eq_left h1]
      have hv1 : msValue r = .metadata (r.b != 0) r.c.toNat := by
        unfold msValue
        rw [ite_eq_right h0, ite_eq_left h1]
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        exact ⟨rfl, fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
          fun e => DTag.noConfusion e, fun _ _ t => ⟨msValue r, _, hms t, fun l ml e => MetaStart.noConfusion (hv1.symm.trans e)⟩,
          fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, fun _ _ t => ⟨msValue r, _, hms t, fun l ml u e => MetaStart.noConfusion (hv1.symm.trans e)⟩,
          (fun _ _ h => by rcases h with e | e <;> cases e), fun e => DStatus.noConfusion e⟩
      · rw [ite_eq_right hz]
        exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
          fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    rw [ite_eq_right h1]
    have hv : msValue r = .data (r.b != 0) r.c.toNat (r.d != 0) := by
      unfold msValue
      rw [ite_eq_right h0, ite_eq_right h1]
    rw [hv] at hms hmsL
    -- With no window yet, `k` is the declared window's log size.
    have hnr : cmd.ring.size = 0 → 10 ≤ k.toNat ∧ k.toNat ≤ 24 := fun hr0 => by
      have hn := hall.noRing hr0
      exact ⟨hn.k10, hn.k24⟩
    by_cases hu : (r.d != 0) = true
    · rw [ite_eq_left hu]
      by_cases hz : r.buf.peek (r.count &&& 7) = 0
      · rw [ite_eq_left hz]
        dsimp only
        have hne : ∀ l ml, MetaStart.data (r.b != 0) r.c.toNat (r.d != 0) ≠ .data l ml false := fun l ml e => by
          injection e with _ _ e3
          rw [hu] at e3
          cases e3
        have hwF : ∀ t : List UInt8, winFrom (2 ^ k.toNat - 16) (availBits cmd.word cmd.count a pos stop (bits t)) = some (2 ^ k.toNat - 16) := by
          intro t
          rw [winFrom_data (hms t), ite_eq_left hu, readFill_held _ (whole_bytes hs t),
            ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        have hwL : ∀ s : List UInt8, winFrom (2 ^ k.toNat - 16) ((BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits s)) =
            some (2 ^ k.toNat - 16) := by
          intro s
          rw [winFrom_data (hmsL s), ite_eq_left hu, readFill_held _ (hwhole s),
            ite_eq_left (show r.buf.peek (r.buf.count &&& 7) = 0 from hz)]
          rfl
        by_cases hr0 : cmd.ring.size = 0
        · rw [ite_eq_left hr0]
          obtain ⟨hk10, hk24⟩ := hnr hr0
          have hpk : 1024 ≤ 2 ^ k.toNat := Nat.le_trans (by decide) (Nat.pow_le_pow_right (by decide) hk10)
          have hneed : ((1 : UInt64) <<< k.toUInt64).toNat = 2 ^ k.toNat := by
            rw [need_toNat (by rw [hku]; exact hk24), hku]
          by_cases hc : (1 : UInt64) <<< k.toUInt64 ≤ limit
          · rw [ite_eq_left hc]
            have hle := UInt64.le_iff_toNat_le.mp hc
            rw [hneed] at hle
            refine ⟨rfl, fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
              fun e => DTag.noConfusion e, fun _ _ t => ⟨_, _, hms t, hne⟩, fun _ h => ?_, (fun _ h => by rcases h with e | e <;> cases e),
              fun _ _ _ => ⟨?_, ?_, rfl, fun t => ⟨2 ^ k.toNat - 16, hwF t, show 2 ^ k.toNat - 16 + 16 = 2 ^ k.toNat by omega⟩⟩,
              fun e => DStatus.noConfusion e⟩
            · rcases h with h | h
              · exact absurd hr0 h
              · exact absurd ⟨rfl, Or.inl rfl⟩ h
            · show (limit - (1 : UInt64) <<< k.toUInt64).toNat + 2 ^ k.toNat = limit.toNat
              rw [UInt64.toNat_sub_of_le _ _ hc, hneed]
              omega
            · show (zeroBytes ((1 : UInt64) <<< k.toUInt64).toNat).size = 2 ^ k.toNat
              rw [hneed, zeroBytes_size (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk24; omega)]
          · rw [ite_eq_right hc]
            have hlt : limit.toNat < 2 ^ k.toNat := Nat.lt_of_not_le fun e => hc (UInt64.le_iff_toNat_le.mpr (by rw [hneed]; exact e))
            exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun e => absurd rfl e,
              fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e,
              fun _ => ⟨hr0, rfl, r2, r3, l2, fun s => ⟨_, hwL s, show limit.toNat < 2 ^ k.toNat - 16 + 16 by omega⟩,
                fun t => ⟨_, hwF t, show limit.toNat < 2 ^ k.toNat - 16 + 16 by omega⟩⟩⟩
        · rw [ite_eq_right hr0]
          exact ⟨rfl, fun e => absurd rfl e, fun _ => rfl, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
            fun e => DTag.noConfusion e, fun _ _ t => ⟨_, _, hms t, hne⟩, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
            (fun _ h => by rcases h with e | e <;> cases e), fun h => absurd h hr0, fun e => DStatus.noConfusion e⟩
      · rw [ite_eq_right hz]
        exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩,
          fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e, fun e => DStatus.noConfusion e⟩
    · rw [ite_eq_right hu]
      have hu' : (r.d != 0) = false := by simpa using hu
      rw [hu'] at hms hmsL
      have hstart : ∀ t : List UInt8, metaStart (availBits cmd.word cmd.count a pos stop (bits t)) =
          some (.data (r.b != 0) r.c.toNat false, availBits r.word r.count a rf.pos stop (bits t)) := hms
      by_cases hr0 : cmd.ring.size = 0
      · rw [ite_eq_left hr0]
        obtain ⟨hk10, hk24⟩ := hnr hr0
        dsimp only
        have hpw : (2 ^ k.toNat - 16) + 16 = 2 ^ k.toNat := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hk10
          have h1024 : (2 : Nat) ^ 10 = 1024 := rfl
          omega
        obtain ⟨hbw, hkb24, hkb10⟩ := allocBits_window (r.b != 0) r.c hpw hk24 hk10
        have hwF : ∀ t : List UInt8, winFrom (2 ^ k.toNat - 16) (availBits cmd.word cmd.count a pos stop (bits t)) =
            some (blockWindow (2 ^ k.toNat - 16) ⟨[], 0, initialDistances⟩ (r.b != 0) r.c.toNat) := fun t => by
          rw [winFrom_data (hms t)]
          rfl
        have hwL : ∀ s : List UInt8, winFrom (2 ^ k.toNat - 16) ((BitBuffer.mk cmd.word cmd.count).held ++ (chunkBits a pos.toNat rf.pos.toNat ++ bits s)) =
            some (blockWindow (2 ^ k.toNat - 16) ⟨[], 0, initialDistances⟩ (r.b != 0) r.c.toNat) := fun s => by
          rw [winFrom_data (hmsL s)]
          rfl
        generalize allocBits k (r.b != 0) r.c = kb at hbw hkb24 hkb10 ⊢
        have hus : kb.toUSize.toNat = kb.toNat := word_toUSize (by omega)
        have hneed := need_toNat hkb24
        by_cases hc : (1 : UInt64) <<< kb ≤ limit
        · rw [ite_eq_left hc]
          have hle := UInt64.le_iff_toNat_le.mp hc
          rw [hneed] at hle
          have hlim' : (limit - (1 : UInt64) <<< kb).toNat + 9144 < 2 ^ 32 := by
            rw [UInt64.toNat_sub_of_le _ _ hc, hneed]
            omega
          refine ⟨rfl, fun e => absurd rfl e, fun e => absurd rfl e, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
            fun _ => ⟨rfl, fun t => ⟨r.b != 0, r.c.toNat, hstart t⟩, hdStart_rel hw2 hlim', hdStart_arena_size _ _ _, u64_lit (by decide), rfl, hsize_start _ _ _⟩,
            fun _ e => absurd rfl e, fun _ h => ?_, (fun _ h => by rcases h with e | e <;> cases e),
            fun _ _ _ => ⟨?_, ?_, rfl, fun t => ⟨_, hwF t, by rw [hbw]; show _ = 2 ^ kb.toUSize.toNat; rw [hus]⟩⟩,
            fun e => DStatus.noConfusion e⟩
          · rcases h with h | h
            · exact absurd hr0 h
            · exact absurd ⟨rfl, Or.inr rfl⟩ h
          · show (limit - (1 : UInt64) <<< kb).toNat + 2 ^ kb.toUSize.toNat = limit.toNat
            rw [UInt64.toNat_sub_of_le _ _ hc, hneed, hus]
            omega
          · show (zeroBytes ((1 : UInt64) <<< kb).toNat).size = 2 ^ kb.toUSize.toNat
            rw [hneed, hus, zeroBytes_size (by have := Nat.pow_le_pow_right (show 0 < 2 by decide) hkb24; omega)]
        · rw [ite_eq_right hc]
          have hlt : limit.toNat < 2 ^ kb.toNat := Nat.lt_of_not_le fun e => hc (UInt64.le_iff_toNat_le.mpr (by rw [hneed]; exact e))
          exact ⟨rfl, fun _ => rfl, fun _ => rfl, hdec, fun e => absurd e hnh, fun e _ => DStatus.noConfusion e, fun e => absurd rfl e,
            fun e => DStatus.noConfusion e, fun _ e => DStatus.noConfusion e,
            fun _ => ⟨hr0, rfl, r2, r3, l2, fun s => ⟨_, hwL s, show limit.toNat < _ + 16 by rw [hbw]; exact hlt⟩,
              fun t => ⟨_, hwF t, show limit.toNat < _ + 16 by rw [hbw]; exact hlt⟩⟩⟩
      · rw [ite_eq_right hr0]
        exact ⟨rfl, fun e => absurd rfl e, fun e => absurd rfl e, ⟨fun e => DTag.noConfusion e, fun e => DTag.noConfusion e⟩,
          fun _ => ⟨rfl, fun t => ⟨r.b != 0, r.c.toNat, hstart t⟩, hdStart_rel hw2 hlim, hdStart_arena_size _ _ _, u64_lit (by decide), rfl, hsize_start _ _ _⟩,
          fun _ e => absurd rfl e, fun _ _ => ⟨rfl, rfl, rfl, rfl⟩, (fun _ h => by rcases h with e | e <;> cases e), fun h => absurd h hr0,
          fun e => DStatus.noConfusion e⟩

/-- A meta-block's start. -/
theorem mblock_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .mblock) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDMeta a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock w st =>
    have hF := stepDMeta_facts (a := a) (hs := hs) hrel hp
    have hD := stepDMeta_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    have hW := stepDMeta_ok (S := winSem) (a := a) (hs := hs) hrel hp
    generalize stepDMeta a stop hs D D.pos = r at hF hD hW
    have hHO : D.H = Hdr.none := M.HOut (by rw [ht]; decide)
    -- With no window yet, the window's worth is what the meta-blocks from here allocate.
    have hNR : D.cmd.ring.size = 0 → D.cmd.wordBuf.size = 0 ∧ D.limit.toNat = L ∧ st = ⟨[], 0, initialDistances⟩ ∧
        w + 16 = 2 ^ D.k.toNat ∧ winFrom (2 ^ D.k.toNat - 16) (D.bits a D.pos stop (bits t)) = Ws := by
      intro hr0
      rcases M.win with ⟨_, a2, a3, q, a4, a5⟩ | ⟨a1, _⟩
      · rw [← hrel.noRing_eq a4 hr0] at a5
        have hn := hrel.2.2.noRing hr0
        have hw0 : w = 2 ^ D.k.toNat - 16 := by have := hn.win; omega
        refine ⟨a2, a3, hn.st, hn.win, ?_⟩
        rw [← hw0]
        have e : srest winSem (.mblock w st) (D.bits a D.pos stop (bits t)) = winFrom w (D.bits a D.pos stop (bits t)) := by
          show (if st.produced = 0 then _ else _) = _
          rw [hn.st]
          rfl
        rw [← e]
        exact a5
      · exact absurd hr0 a1
    refine ⟨fun h0 h1 => ?_, fun e => ?_⟩
    · obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 hF.paused
      have hwin : MemD.winOf Ws L r (r.bits a r.pos stop (bits t)) := by
        by_cases hr0 : D.cmd.ring.size = 0
        · obtain ⟨hwb, hL, hst, hwk, hWs⟩ := hNR hr0
          subst hst
          by_cases hal : r.status = .next ∧ (r.tag = .raw ∨ r.tag = .hdr)
          · obtain ⟨e1, e2, _, e4⟩ := hF.alloc hr0 hal.1 hal.2
            obtain ⟨W, hW1, hW2⟩ := e4 t
            refine Or.inr ⟨by rw [e2]; exact Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _), W, by rw [← hWs, hW1], hW2, by omega⟩
          · obtain ⟨s1, s2, s3, s4⟩ := hF.same h0 (Or.inr hal)
            refine Or.inl ⟨by rw [s3]; exact hr0, by rw [s4]; exact hwb, by rw [s2]; exact hL, ?_⟩
            have hwF : winFrom w (D.bits a D.pos stop (bits t)) = Ws := by
              have hw0 : w = 2 ^ D.k.toNat - 16 := by omega
              rw [hw0]
              exact hWs
            cases hst : r.status with
            | next =>
              obtain ⟨p', hR, _, _, heq, hdown, _⟩ := hW.next hst
              cases p' with
              | skip w' st' last n =>
                obtain ⟨v, rest, hm, hv⟩ := hF.nodata hst (Or.inl hR.1) t
                exact ⟨_, hR, by rw [← heq t, ← winFrom_leave rfl hm hv]; exact hwF⟩
              | ended st' =>
                obtain ⟨v, rest, hm, hv⟩ := hF.nodata hst (Or.inr hR.1) t
                exact ⟨_, hR, by rw [← heq t, ← winFrom_leave rfl hm hv]; exact hwF⟩
              | raw => exact absurd ⟨hst, Or.inl hR.1⟩ hal
              | hdr => exact absurd ⟨hst, Or.inr hR.1⟩ hal
              | wbits => exact hdown.elim
              | mblock => exact hdown.elim
              | cmds => exact hdown.elim
            | needsInput =>
              obtain ⟨_, _, p', hR, _, _, hdown, hb, _⟩ := hW.needsInput hst
              cases p' with
              | mblock w' st' =>
                have hr0' : r.cmd.ring.size = 0 := by rw [s3]; exact hr0
                have hn' := hR.2.2.noRing hr0'
                have hw' : w' = w := by have := hn'.win; rw [s1] at this; omega
                refine ⟨_, hR, ?_⟩
                show (if st'.produced = 0 then _ else _) = _
                rw [hn'.st, hw', hb w _ rfl t]
                exact hwF
              | _ => exact hdown.elim
            | needsOutput =>
              obtain ⟨p', hR, _, _, _, _, hdown, hb, _⟩ := hW.needsOutput hst
              cases p' with
              | mblock w' st' =>
                have hr0' : r.cmd.ring.size = 0 := by rw [s3]; exact hr0
                have hn' := hR.2.2.noRing hr0'
                have hw' : w' = w := by have := hn'.win; rw [s1] at this; omega
                refine ⟨_, hR, ?_⟩
                show (if st'.produced = 0 then _ else _) = _
                rw [hn'.st, hw', hb w _ rfl t]
                exact hwF
              | _ => exact hdown.elim
            | memory => exact absurd hst h0
            | bad => exact absurd hst h1
        · obtain ⟨s1, s2, s3, _⟩ := hF.same h0 (Or.inl hr0)
          exact M.winKeep hr0 s1 s2 (congrArg ByteArray.size s3)
      by_cases hth : r.tag = .hdr
      · obtain ⟨_, s2, s3, s4, s4', s5, s6⟩ := hF.start hth
        obtain ⟨last, mlen, hm⟩ := s2 t
        have hTables : headerTables (D.bits a D.pos stop (bits t)) = (hrest tableK Gh.start (.cat .L) (r.bits a r.pos stop (bits t))).getD 0 := by
          unfold headerTables
          rw [hm]
        have hb0 := M.block ht
        rw [hTables] at hb0
        refine ⟨hA, hB, fun _ => ⟨Gh.start, .cat .L, s3, by rw [s4']; omega, s5, ?_⟩, fun e => absurd (hth.symm.trans e) (by decide), fun e => absurd hth e,
          fun _ => by rw [hF.H]; exact hHO, s6, by rw [hF.H]; exact M.H, hwin⟩
        rw [s4, s4']
        show arenaPre + catMax * (2 + 1) ≤ 3 * catMax + arenaPre
        omega
      · exact M.keep (by rw [ht]; decide) (hF.other hth) hth (by rw [hF.H]; exact M.H) (fun e => absurd e hF.tag.2)
          (fun _ => by rw [hF.H]; exact hHO) hA hB hwin
    · obtain ⟨m1, _, _, _, _, _, m7⟩ := hF.memory e
      obtain ⟨_, hL, _, _, hWs⟩ := hNR m1
      obtain ⟨W, hW1, hW2⟩ := m7 t
      rw [hWs] at hW1
      have hwl := winFrom_le (2 ^ D.k.toNat - 16) _ (D.bits a D.pos stop (bits t)) rfl W (by rw [hWs]; exact hW1)
      have hk24 : D.k.toNat ≤ 24 := (hrel.2.2.noRing m1).k24
      have hpw : 2 ^ D.k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk24
      have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
      have he : Ws.elim 0 (· + 16) = W + 16 := by rw [hW1]; rfl
      exact ⟨by rw [he]; omega, by omega⟩

/-! ### Metadata, uncompressed bytes and commands -/

/-- Metadata's step. -/
theorem skip_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} (hs : stop.toNat ≤ a.size) {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .skip) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDSkip stop D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := stepDSkip_keeps stop D D.pos ht
  obtain ⟨c1, c2⟩ := stepDSkip_win stop D D.pos
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip w st last n =>
    have hD := stepDSkip_ok (S := demandSem) hs hrel hp
    have hW := stepDSkip_ok (S := winSem) hs hrel hp
    generalize stepDSkip stop D D.pos = r at hD hW k1 k2 k3 k4 k5 k6 k7 k8 k9 c1 c2
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k5⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 k6
    refine M.keep (by rw [ht]; decide) k3 k8 (by rw [k4]; exact M.H) (fun e => absurd e k9)
      (fun _ => by rw [k4]; exact M.HOut (by rw [ht]; decide)) hA hB ?_
    by_cases hr0 : D.cmd.ring.size = 0
    · rcases M.win with ⟨_, a2, a3, q, a4, a5⟩ | ⟨a1, _⟩
      · rw [← hrel.noRing_eq a4 hr0] at a5
        refine Or.inl ⟨by rw [c1]; exact hr0, by rw [c2]; exact a2, by rw [k2]; exact a3, ?_⟩
        cases hst : r.status with
        | next =>
          obtain ⟨p', hR, _, _, heq, _⟩ := hW.next hst
          exact ⟨p', hR, by rw [← heq t]; exact a5⟩
        | needsInput =>
          obtain ⟨_, _, p', hR, heq, _, hdown, _⟩ := hW.needsInput hst
          cases p' with
          | skip => exact ⟨_, hR, by rw [← a5]; exact (heq t).symm⟩
          | _ => exact hdown.elim
        | needsOutput =>
          obtain ⟨p', hR, _, _, heq, _, hdown, _⟩ := hW.needsOutput hst
          cases p' with
          | skip => exact ⟨_, hR, by rw [← a5]; exact (heq t).symm⟩
          | _ => exact hdown.elim
        | memory => exact absurd hst h0
        | bad => exact absurd hst h1
      · exact absurd hr0 a1
    · exact M.winKeep hr0 k1 k2 (congrArg ByteArray.size c1)

/-- Uncompressed bytes' step. -/
theorem raw_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .raw) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDRaw a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := stepDRaw_keeps a stop hs D D.pos ht
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw w st last n =>
    have hD := stepDRaw_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    have hr0 : D.cmd.ring.size ≠ 0 := by
      have := hrel.2.2.1.win.ring.size
      have := Nat.two_pow_pos D.k.toNat
      omega
    have kr := stepDRaw_ring a stop hs D D.pos
    generalize stepDRaw a stop hs D D.pos = r at hD k1 k2 k3 k4 k5 k6 k7 k8 k9 kr
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k5⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw M.block h0 h1 k6
    exact M.keep (by rw [ht]; decide) k3 k8 (by rw [k4]; exact M.H) (fun e => absurd e k9)
      (fun _ => by rw [k4]; exact M.HOut (by rw [ht]; decide)) hA hB (M.winKeep hr0 k1 k2 kr)

/-- The commands' step. -/
theorem cmds_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .cmds) (hp : D.pos.toNat ≤ stop.toNat) :
    StepM Ws X L a stop t (stepDCmds a stop hs D D.pos) := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := stepDCmds_keeps a stop hs D D.pos
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds w last m q =>
    have hD := stepDCmds_ok (S := demandSem) (a := a) (hs := hs) hrel hp
    have hr0 : D.cmd.ring.size ≠ 0 := by
      have := hrel.2.2.2.2.1.arrays.1
      have := Nat.two_pow_pos D.k.toNat
      omega
    have kr := stepDCmds_ring (a := a) (hs := hs) hrel hp
    generalize stepDCmds a stop hs D D.pos = r at hD k1 k2 k3 k4 k5 k6 kr
    refine ⟨fun h0 h1 => ?_, fun e => absurd e k4⟩
    obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) h0 h1 k5
    have hwin := M.winKeep (B' := r.bits a r.pos stop (bits t)) hr0 k1 k2 (kr h1)
    rcases k6 with ⟨t1, t2⟩ | ⟨t1, t2, t3, t4⟩
    · have hc := M.cmds ht
      rw [← t1] at ht
      exact M.keep (by rw [t1] at ht; rw [ht]; decide) k3 (by rw [ht]; decide) (by rw [t2]; exact M.H)
        (fun _ => by rw [t2, k2]; exact hc) (fun e => absurd ht e) hA hB hwin
    · exact M.keep (by rw [ht]; decide) k3 t2 (by rw [t4]; exact hsmall_none) (fun e => absurd e t3) (fun _ => t4) hA hB hwin

/-! ### A header -/

/-- The bits of a state in a header. -/
theorem Dec.bits_hdr {D : Dec} (h : D.tag = .hdr) (a : ByteArray) (pos stop : USize) (F : List Bool) :
    D.bits a pos stop F = availBits D.hd.word D.hd.count a pos stop F := by
  unfold Dec.bits Dec.word Dec.count
  rw [h]

/-- What a move does to the arena's reservation and what the rest of the header reserves. -/
private theorem move_mem {st r : Hd} {g g' : Gh} {q q' : HPhase} {oc : Option Hook} {X R R' : Nat} (hm : HMove st r g q g' q' oc)
    (hR : R = resOf oc + R') (h1 : st.d.arenaCap.toNat + R ≤ smallMax + X) (h3 : st.d.arena.size + budH g q ≤ st.d.arenaCap.toNat)
    (hle : st.d.arena.size ≤ st.d.arenaCap.toNat) :
    r.d.arenaCap.toNat + R' ≤ smallMax + X ∧ r.d.arena.size + budH g' q' ≤ r.d.arenaCap.toNat := by
  have hg := hm.grow
  have hc := hm.cap
  match oc with
  | some (.res g0) =>
    obtain ⟨c1, c2, c3, _⟩ := hc
    have e1 : tableOf (some (.res g0)) = 0 := rfl
    have e2 : resOf (some (.res g0)) = resBytes g0 := rfl
    rw [e1] at hg
    rw [e2] at hR
    omega
  | none =>
    obtain ⟨c1, c2⟩ := hc
    have e1 : tableOf none = 0 := rfl
    have e2 : resOf none = 0 := rfl
    rw [e1] at hg c2
    rw [e2] at hR
    rw [c1]
    omega
  | some (.table c) =>
    obtain ⟨c1, c2⟩ := hc
    have e1 : tableOf (some (.table c)) = tableBytes c := rfl
    have e2 : resOf (some (.table c)) = 0 := rfl
    rw [e1] at hg c2
    rw [e2] at hR
    rw [c1]
    omega

/-- A header's step. -/
theorem hdr_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (ht : D.tag = .hdr) (hp : D.pos.toNat ≤ stop.toNat) {hH : HIn D.hd} :
    StepM Ws X L a stop t (stepDHdr a stop hs D D.pos hH hp) := by
  obtain ⟨g, q, hR, h1, h2, h3⟩ := M.hdr ht
  rw [Dec.bits_hdr ht] at h1
  obtain ⟨p, hrel, hw⟩ := M.place
  have hr0 : D.cmd.ring.size ≠ 0 := fun e => (hrel.noRing e).1 ht
  have hWinr : ∃ w, Ws = some w ∧ w + 16 = 2 ^ D.k.toNat ∧ D.limit.toNat + 2 ^ D.k.toNat = L := by
    rcases M.win with ⟨h, _⟩ | ⟨_, h⟩
    · exact absurd h hr0
    · exact h
  obtain ⟨w0, g1, g2, g3⟩ := hWinr
  have hHO : D.H = Hdr.none := M.HOut (by rw [ht]; decide)
  obtain ⟨_, hk24, _⟩ := hrel.arrays hr0
  cases p with
  | wbits => exact absurd (hrel.1.symm.trans ht) (by decide)
  | mblock => exact absurd (hrel.1.symm.trans ht) (by decide)
  | skip => exact absurd (hrel.1.symm.trans ht) (by decide)
  | raw => exact absurd (hrel.1.symm.trans ht) (by decide)
  | cmds => exact absurd (hrel.1.symm.trans ht) (by decide)
  | ended => exact absurd (hrel.1.symm.trans ht) (by decide)
  | hdr w st last mlen g0 q0 =>
    have hD := stepDHdr_ok (S := demandSem) (a := a) (hs := hs) (hH := hH) hrel hp
    have hHs := stepH_ok (K := tableK) (a := a) (hs := hs) (h := ⟨g, q, hR, h3⟩) hR hp h3
    unfold stepDHdr takeHd at hD ⊢
    dsimp only at hD ⊢
    generalize hrr : stepHR a stop hs D.hd D.pos ⟨g, q, hR, h3⟩ hp = rr at hD ⊢
    obtain ⟨r, hr⟩ := rr
    have e : r = stepH a stop hs D.hd D.pos ⟨g, q, hR, h3⟩ hp := by rw [← stepHR_val (h := ⟨g, q, hR, h3⟩) (hp := hp), hrr]
    rw [← e] at hHs
    unfold hdrNext at hD ⊢
    dsimp only at hD ⊢
    have hbitsAt : ∀ D' : Dec, D'.tag = .hdr → D'.hd = r → D'.pos = r.pos → D'.bits a D'.pos stop (bits t) = availBits r.word r.count a r.pos stop (bits t) := by
      intro D' e1 e2 e3
      rw [Dec.bits_hdr e1, e2, e3]
    split <;> rename_i hst <;> split at hD <;> rename_i hst' <;>
      (try exact absurd (hst.symm.trans hst') (fun e => HStatus.noConfusion e))
    · obtain ⟨g', q', oc, hR', a1, a2, a3, _, hm, _⟩ := hHs.next hst
      have hT := a3 (bits t)
      have hN := congrArg (Option.getD · 0) hT
      simp only [wr_tableK] at hN
      have key := move_mem hm hN h1 h3 hR.2.1.le
      have htag : ({ clearHd D with hd := r, pos := r.pos, status := .next } : Dec).tag = .hdr := ht
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun e => absurd rfl e)
      refine ⟨hA, hB, fun _ => ⟨g', q', hR', ?_, ?_, key.2⟩, fun e => absurd (htag.symm.trans e) (by decide), fun e => absurd htag e, fun _ => hHO, hm.size M.hd, M.H,
        Or.inr ⟨hr0, w0, g1, g2, g3⟩⟩
      · rw [hbitsAt _ htag rfl rfl]
        exact key.1
      · show r.d.arenaMax = D.limit
        rw [hm.max, h2]
    · obtain ⟨a1, a2, hR', a3, _, hm, _⟩ := hHs.needsInput hst
      have hT := a3 (bits t)
      have key := move_mem (R' := (hrest tableK g q (availBits r.word r.count a r.pos stop (bits t))).getD 0) hm
        (by rw [hT]; exact (Nat.zero_add _).symm) h1 h3 hR.2.1.le
      have htag : ({ clearHd D with hd := r, pos := r.pos, status := .needsInput } : Dec).tag = .hdr := ht
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun _ => rfl)
      refine ⟨hA, hB, fun _ => ⟨g, q, hR', ?_, ?_, key.2⟩, fun e => absurd (htag.symm.trans e) (by decide), fun e => absurd htag e, fun _ => hHO, hm.size M.hd, M.H,
        Or.inr ⟨hr0, w0, g1, g2, g3⟩⟩
      · rw [hbitsAt _ htag rfl rfl]
        exact key.1
      · show r.d.arenaMax = D.limit
        rw [hm.max, h2]
    · exact ⟨fun _ e => absurd rfl e, fun e => DStatus.noConfusion e⟩
    · refine ⟨fun e => absurd rfl e, fun _ => ?_⟩
      obtain ⟨g', m1, m2, m3, m4⟩ := hHs.memory hst
      obtain ⟨x, hx⟩ := m4 (bits t)
      rw [hx] at h1
      have h1' : D.hd.d.arenaCap.toNat + (resBytes g' + x.getD 0) ≤ smallMax + X := h1
      rw [h2] at m1
      have hrm : resMax = 2197583 := rfl
      have hpw : 2 ^ D.k.toNat ≤ 2 ^ 24 := Nat.pow_le_pow_right (by decide) hk24
      have h224 : (2 : Nat) ^ 24 = 16777216 := rfl
      have he : (some w0 : Option Nat).elim 0 (· + 16) = w0 + 16 := rfl
      refine ⟨?_, by omega⟩
      rw [g1, he]
      omega
    · obtain ⟨g', hu, _, _, _, a3, hmax, _, hcapE, hsz, _⟩ := hHs.ready hst
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨hA, hB⟩ := placed hrel hD hw (fun e => absurd (ht.symm.trans e) (by decide)) (fun e => DStatus.noConfusion e) (fun e => DStatus.noConfusion e) (fun e => absurd rfl e)
      have hS := hsz M.hd
      have hle := hu.capLe
      have hT := congrArg (Option.getD · 0) (a3 (bits t))
      have hk0 : (tableK.k g'.m (availBits r.word r.count a r.pos stop (bits t))).getD 0 = 0 := rfl
      rw [hk0] at hT
      refine ⟨hA, hB, fun e => DTag.noConfusion e, fun _ => ⟨?_, ?_, ?_⟩, fun _ => rfl, fun e => absurd rfl e, hsize_none,
        ⟨hS.litBase, hS.lMap, hS.icBase, hS.dBase, hS.dMap, hS.modes, triv_le hS.lMap⟩,
        Or.inr ⟨hr0, w0, g1, g2, g3⟩⟩
      · show r.d.arenaCap.toNat ≤ smallMax + X
        rw [hcapE]
        omega
      · show r.d.arenaCap.toNat ≤ smallMax + D.limit.toNat
        rw [← h2, ← hmax]
        exact hle
      · exact mkHdr_size hu ⟨g', hu⟩

/-! ### The loop and a call -/

/-- A step of the stream. -/
theorem stepD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {D : Dec} {t : List UInt8}
    (M : MemD Ws X L D (D.bits a D.pos stop (bits t))) (he : D.tag ≠ .ended) (hp : D.pos.toNat ≤ stop.toNat) {h : DInv stop D} :
    StepM Ws X L a stop t (stepD a stop hs D h) := by
  cases ht : D.tag with
  | wbits => rw [stepD_wbits ht]; exact wbits_mem M ht hp
  | mblock => rw [stepD_mblock ht]; exact mblock_mem M ht hp
  | skip => rw [stepD_skip ht]; exact skip_mem hs M ht hp
  | raw => rw [stepD_raw ht]; exact raw_mem M ht hp
  | hdr => rw [stepD_hdr ht]; exact hdr_mem M ht h.2
  | cmds => rw [stepD_cmds ht]; exact cmds_mem M ht hp
  | ended => exact absurd ht he

/-- The loop. -/
theorem runD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {t : List UInt8} : ∀ x : RunArg a stop hs,
    MemD Ws X L x.D (x.D.bits a x.D.pos stop (bits t)) → StepM Ws X L a stop t (runD a stop hs x.D x.inv) := by
  intro x
  induction x using (runRel_wf a stop hs).induction with
  | _ x ih =>
    intro M
    obtain ⟨D, hinv⟩ := x
    dsimp only at M ⊢
    rw [runD]
    by_cases he : D.tag = .ended
    · rw [dite_eq_left he]
      refine ⟨fun _ _ => ?_, fun e => DStatus.noConfusion e⟩
      obtain ⟨p, hrel, hw⟩ := M.place
      exact M.move rfl ⟨p, hrel.congr rfl rfl rfl rfl rfl rfl rfl rfl, hw⟩ (fun q h => h.congr rfl rfl rfl rfl rfl rfl rfl rfl)
        rfl rfl rfl rfl rfl rfl rfl
    · rw [dite_eq_right he]
      dsimp only
      have hstep := stepD_mem (hs := hs) (h := hinv) M he hinv.2
      by_cases hn : (stepD a stop hs D hinv).status = .next
      · rw [dite_eq_left hn]
        have hM := hstep.go (by rw [hn]; decide) (by rw [hn]; decide)
        exact ih ⟨stepD a stop hs D hinv, hinv.step he hn⟩ ⟨he, hn, rfl⟩ hM
      · rw [dite_eq_right hn]
        exact hstep

/-- What a call leaves, for what a state holds. -/
structure CallMem (Ws : Option Nat) (X L : Nat) (a : ByteArray) (stop : USize) (t : List UInt8) (o : Out) : Prop where
  running : o.status.stopped = false → MemD Ws X L o.D (o.D.bits a o.pos stop (bits t))
  stopped : o.status.stopped = true → o.D = deadD
  why : o.status = .memoryLimit → MemWhy Ws X L

/-- Handing out a state's bytes keeps its window and its word buffer. -/
theorem flushD_rings {D : Dec} {p : SPhase} (hrel : DRel D p) (buf : ByteArray) (space : Nat) :
    (flushD D buf space).D.cmd.ring = D.cmd.ring ∧ (flushD D buf space).D.cmd.wordBuf = D.cmd.wordBuf := by
  rcases hrel.window with h0 | ⟨hring, hle, hout, hk⟩
  · have hf : flushAll D.k D.cmd buf space = ⟨D.cmd, buf, space⟩ := by
      rw [flushAll]
      dsimp only
      rw [ite_eq_left (Or.inl h0)]
    unfold flushD
    dsimp only
    rw [hf]
    exact ⟨rfl, rfl⟩
  · obtain ⟨_, _, _, _, a5, _, _, _⟩ := flushAll_spec hk _ D.cmd buf space rfl hring hle hout
    unfold flushD
    dsimp only
    rw [a5]
    exact ⟨rfl, rfl⟩

/-- Handing out a state's bytes leaves what it holds. -/
theorem MemD.flush {Ws : Option Nat} {X L : Nat} {D : Dec} {B : List Bool} (M : MemD Ws X L D B) (buf : ByteArray) (space : Nat) : MemD Ws X L (flushD D buf space).D B := by
  obtain ⟨p, hrel, hw⟩ := M.place
  obtain ⟨_, _, _, _, a4, _, _, _, _, _, _, _⟩ := flushD_spec hrel buf space
  have hrings := flushD_rings hrel buf space
  exact M.move rfl ⟨p, a4, hw⟩ (fun q h => by obtain ⟨_, _, _, _, a, _⟩ := flushD_spec h buf space; exact a) rfl hrings.1 hrings.2 rfl rfl rfl rfl

/-- Handing out a state's bytes leaves what it holds, with its bits as they were. -/
theorem MemD.flushed {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {D : Dec} {F : List Bool} (M : MemD Ws X L D (D.bits a D.pos stop F)) (buf : ByteArray) (space : Nat) :
    MemD Ws X L (flushD D buf space).D ((flushD D buf space).D.bits a (flushD D buf space).D.pos stop F) := by
  obtain ⟨p, hrel, _⟩ := M.place
  obtain ⟨_, _, _, _, _, _, _, _, a8, _, a9, _⟩ := flushD_spec hrel buf space
  rw [a8, a9]
  exact M.flush buf space

/-- A call that stopped. -/
private theorem callMem_dead {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {buf : ByteArray} {pos : USize} {s : Status} (hs : s.stopped = true)
    (hm : s = .memoryLimit → MemWhy Ws X L) : CallMem Ws X L a stop t ⟨deadD, buf, pos, s⟩ :=
  ⟨fun h => Bool.noConfusion (hs.symm.trans h), fun _ => rfl, hm⟩

/-- A call that paused with a state. -/
private theorem callMem_run {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {D : Dec} {buf : ByteArray} {pos : USize} {s : Status} (hs : s.stopped = false)
    (hn : s ≠ .memoryLimit) (M : MemD Ws X L D (D.bits a pos stop (bits t))) : CallMem Ws X L a stop t ⟨D, buf, pos, s⟩ :=
  ⟨fun _ => M, fun h => Bool.noConfusion (hs.symm.trans h), fun e => absurd e hn⟩

/-- The stream's end. -/
theorem endCheck_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {D : Dec} {B : List Bool} {t : List UInt8} {st : StreamState} {final : Bool} (buf : ByteArray)
    (M : MemD Ws X L D B) (hrel : DRel D (.ended st)) : CallMem Ws X L a stop t (endCheck D stop final buf) := by
  have ht : D.tag = .ended := hrel.1
  obtain ⟨a1, hw, w, a3⟩ := hrel
  unfold endCheck
  dsimp only
  by_cases hz : (BitBuffer.mk D.cmd.word D.cmd.count).peek (D.cmd.count &&& 7) = 0
  · rw [ite_eq_left hz]
    by_cases hc : ((BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)).count = 0 ∧ D.pos = stop
    · rw [ite_eq_left hc]
      cases final with
      | true => exact callMem_dead rfl (fun e => Status.noConfusion e)
      | false =>
        obtain ⟨_, fa2⟩ := fill_aligned hw
        refine callMem_run rfl (fun e => Status.noConfusion e) ?_
        have hne : ∀ d : DTag, d ≠ .ended → D.tag ≠ d := fun d h e => h (e.symm.trans ht)
        let b1 := (BitBuffer.mk D.cmd.word D.cmd.count).drop (D.cmd.count &&& 7)
        have hrel' : DRel { D with cmd := { D.cmd with word := b1.word, count := b1.count }, status := .needsInput } (.ended st) :=
          ⟨a1, fa2, w, a3.words rfl rfl rfl⟩
        refine M.keep (hne _ (by decide)) rfl (hne _ (by decide)) M.H (fun e => absurd e (hne _ (by decide)))
          M.HOut ⟨.ended st, hrel', Nat.zero_le _⟩ (fun e => absurd e (hne _ (by decide))) ?_
        rcases M.win with ⟨a1', a2', a3', q, a4', a5'⟩ | h
        · rw [← DRel.noRing_eq (p := .ended st) ⟨a1, hw, w, a3⟩ a4' a1'] at a5'
          exact Or.inl ⟨a1', a2', a3', .ended st, hrel', a5'⟩
        · exact Or.inr h
    · rw [ite_eq_right hc]
      exact callMem_dead rfl (fun e => Status.noConfusion e)
  · rw [ite_eq_right hz]
    exact callMem_dead rfl (fun e => Status.noConfusion e)

/-- What a call does with what the loop left. -/
theorem afterRun_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {t : List UInt8} {r : Dec} {final : Bool} (hr : StepM Ws X L a stop t r)
    (hend : r.status = .next → ∃ st, DRel r (.ended st)) (buf : ByteArray) (space : Nat) : CallMem Ws X L a stop t (afterRun r stop final buf space) := by
  unfold afterRun
  cases hst : r.status with
  | bad => exact callMem_dead rfl (fun e => Status.noConfusion e)
  | memory => exact callMem_dead rfl (fun _ => hr.why hst)
  | needsOutput => exact callMem_run rfl (fun e => Status.noConfusion e) (hr.go (by rw [hst]; decide) (by rw [hst]; decide))
  | needsInput =>
    have hM := (hr.go (by rw [hst]; decide) (by rw [hst]; decide)).flushed buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      cases final with
      | true => exact callMem_dead rfl (fun e => Status.noConfusion e)
      | false => exact callMem_run rfl (fun e => Status.noConfusion e) hM
    · rw [ite_eq_right hz]
      exact callMem_run rfl (fun e => Status.noConfusion e) hM
  | next =>
    have hM := (hr.go (by rw [hst]; decide) (by rw [hst]; decide)).flushed buf space
    obtain ⟨st, hrel⟩ := hend hst
    obtain ⟨_, _, _, _, a4, _, _, _, _, _, _, _⟩ := flushD_spec hrel buf space
    dsimp only
    by_cases hz : (flushD r buf space).D.cmd.pend = 0
    · rw [ite_eq_left hz]
      exact endCheck_mem _ hM a4
    · rw [ite_eq_right hz]
      exact callMem_run rfl (fun e => Status.noConfusion e) hM

/-- A call, for what a state holds. -/
theorem callD_mem {Ws : Option Nat} {X L : Nat} {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {final : Bool} {t : List UInt8} : ∀ (space : Nat) (D : Dec) (h : DInv stop D) (buf : ByteArray),
    MemD Ws X L D (D.bits a D.pos stop (bits t)) → CallMem Ws X L a stop t (callD a stop hs final D h buf space) := by
  intro space
  induction space using Nat.strongRecOn with
  | _ space ih =>
    intro D h buf M
    rw [callD]
    dsimp only
    have hr := runD_mem (hs := hs) (t := t) ⟨withCap D space, h.withCap space⟩ (M.withCap _)
    dsimp only at hr
    by_cases hO : (runD a stop hs (withCap D space) (h.withCap space)).status = .needsOutput
    · rw [dite_eq_left hO]
      have hM := (hr.go (by rw [hO]; decide) (by rw [hO]; decide)).flushed buf space
      obtain ⟨p, hrel⟩ := h.1
      obtain ⟨p', hR, _, _, _, _, hfull⟩ := (runD_ok (hs := hs) ⟨withCap D space, h.withCap space⟩ p (hrel.withCap _)).needsOutput hO
      obtain ⟨len, a1, _, a3, _, a5, _, _, _, _, _, _⟩ := flushD_spec hR buf space
      by_cases hz : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).D.cmd.pend = 0
      · rw [ite_eq_left hz]
        by_cases hlt : (flushD (runD a stop hs (withCap D space) (h.withCap space)) buf space).space < space
        · rw [dite_eq_left hlt]
          exact ih _ hlt _ _ _ hM
        · rw [dite_eq_right hlt]
          exact callMem_dead rfl (fun e => Status.noConfusion e)
      · rw [ite_eq_right hz]
        exact callMem_run rfl (fun e => Status.noConfusion e) hM
    · rw [dite_eq_right hO]
      obtain ⟨p, hrel⟩ := h.1
      refine afterRun_mem hr (fun e => ?_) _ _
      obtain ⟨st, b1, _⟩ := (runD_ok (hs := hs) ⟨withCap D space, h.withCap space⟩ p (hrel.withCap _)).next e
      exact ⟨st, b1⟩

end Brotli.Decoder
