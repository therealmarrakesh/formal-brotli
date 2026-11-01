import Brotli.Decoder.StreamStart

/-!
# Uncompressed bytes and metadata

Where the stream's bits go past whole bytes: the fill bits, metadata to skip, and uncompressed bytes through the window.
-/

namespace Brotli.Decoder

open Brotli.Spec Brotli.Properties

/-! ### In the spec's terms -/

/-- Metadata still to skip, and on. -/
def skipK (w : Nat) (st : StreamState) (last : Bool) (n : Nat) (bs : List Bool) : Option (List UInt8) :=
  if bs.length < n * 8 then none else amK w last st (bs.drop (n * 8))

/-- Uncompressed bytes still to read, and on. -/
def rawK (w : Nat) (st : StreamState) (last : Bool) (n : Nat) (bs : List Bool) : Option (List UInt8) :=
  readBytes n bs >>= fun p => amK w last ⟨p.1.reverse ++ st.output, st.produced + n, st.distances⟩ p.2

/-- With no uncompressed bytes left, what follows the meta-block. -/
theorem rawK_zero (w : Nat) (st : StreamState) (last : Bool) (bs : List Bool) : rawK w st last 0 bs = amK w last st bs := rfl

/-- One more uncompressed byte. -/
theorem rawK_succ (w : Nat) (st : StreamState) (last : Bool) (n : Nat) (bs : List Bool) :
    rawK w st last (n + 1) bs = readInt 8 bs >>= fun p => rawK w ⟨p.1 :: st.output, st.produced + 1, st.distances⟩ last n p.2 := by
  have hsome : ∀ {β γ : Type} (x : β) (f : β → Option γ), (some x >>= f) = f x := fun _ _ => rfl
  have hne : ∀ {β : Type} (f g : β → Option (List UInt8)) (y : Option β), (∀ x, f x = g x) → (y >>= f) = (y >>= g) := by
    intro β f g y h
    rw [funext h]
  unfold rawK
  simp only [readBytes]
  cases readInt 8 bs with
  | none => rfl
  | some q =>
    obtain ⟨b, r⟩ := q
    simp only [hsome]
    rw [bind_assoc]
    refine hne _ _ _ fun t => ?_
    obtain ⟨rest, r2⟩ := t
    simp only [hsome]
    have e1 : (b :: rest).reverse ++ st.output = rest.reverse ++ b :: st.output := by simp
    have e2 : st.produced + (n + 1) = st.produced + 1 + n := by omega
    rw [e1, e2]

/-- Metadata bytes held go first. -/
theorem skipK_prefix (w : Nat) (st : StreamState) (last : Bool) {n m : Nat} (l r : List Bool) (hl : l.length = m * 8) (hm : m ≤ n) :
    skipK w st last n (l ++ r) = skipK w st last (n - m) r := by
  unfold skipK
  have hlen : (l ++ r).length = m * 8 + r.length := by simp [hl]
  have hdrop : (l ++ r).drop (n * 8) = r.drop ((n - m) * 8) := by
    have hn : n * 8 = m * 8 + (n - m) * 8 := by
      rw [← Nat.add_mul]
      congr 1
      omega
    rw [hn, ← hl, List.drop_append]
    simp
  rw [hlen, hdrop]
  have hn : n * 8 = m * 8 + (n - m) * 8 := by
    rw [← Nat.add_mul]
    congr 1
    omega
  rw [hn]
  by_cases h : r.length < (n - m) * 8
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- With no metadata left, what follows the meta-block. -/
theorem skipK_zero (w : Nat) (st : StreamState) (last : Bool) (bs : List Bool) : skipK w st last 0 bs = amK w last st bs := by
  simp [skipK]

/-- With too few bits, nothing to give. -/
theorem skipK_short {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {bs : List Bool} (h : bs.length < n * 8) :
    skipK w st last n bs = none := by
  unfold skipK
  rw [ite_eq_left h]

/-! ### The fill bits -/

/-- The fill bits are the buffer's low bits, up to a whole byte, when what follows is whole bytes. -/
theorem readFill_held {b : BitBuffer} (f : List Bool) (hf : f.length % 8 = 0) :
    readFill (b.held ++ f) = if b.peek (b.count &&& 7) = 0 then some ((b.drop (b.count &&& 7)).held ++ f) else none := by
  have hk : (b.count &&& 7).toNat = b.count.toNat % 8 := by
    rw [UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hlen : (b.held ++ f).length % 8 = (b.count &&& 7).toNat := by
    simp only [List.length_append, BitBuffer.held, lowBits_length]
    rw [hk]
    omega
  have hle : (b.count &&& 7) ≤ b.count := UInt64.le_iff_toNat_le.mpr (by rw [hk]; omega)
  have hlt : (b.count &&& 7).toNat < 64 := by rw [hk]; omega
  have hread := read_int (b := b) f hlt hle
  unfold readFill
  rw [hlen, hread]
  show (if (b.peek (b.count &&& 7)).toNat = 0 then _ else _) = _
  by_cases hz : b.peek (b.count &&& 7) = 0
  · rw [ite_eq_left hz, ite_eq_left (show (b.peek (b.count &&& 7)).toNat = 0 by rw [hz]; rfl)]
  · rw [ite_eq_right hz, ite_eq_right (show ¬ (b.peek (b.count &&& 7)).toNat = 0 from fun e => hz (UInt64.toNat_inj.mp e))]

/-- After the fill bits, the buffer holds whole bytes. -/
theorem fill_aligned {b : BitBuffer} (hw : b.Wf) : (b.drop (b.count &&& 7)).count.toNat % 8 = 0 ∧ (b.drop (b.count &&& 7)).Wf := by
  have hk : (b.count &&& 7).toNat = b.count.toNat % 8 := by
    rw [UInt64.toNat_and, show (7 : UInt64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hle : (b.count &&& 7).toNat ≤ b.count.toNat := by rw [hk]; omega
  have hc := drop_count (b := b) hle
  exact ⟨by rw [hc, hk]; omega, BitBuffer.drop_wf hw (by rw [hk]; omega) hle⟩

/-! ### Uncompressed bytes -/

/-- What the loop for uncompressed bytes leaves. -/
structure RawRun where
  word : UInt64
  count : UInt64
  pos : USize
  ring : ByteArray
  wpos : USize
  p1 : UInt8
  p2 : UInt8
  left : USize

/-- Moves up to `n` bytes from the input into the window, stopping if the input runs out. -/
def rawRun (a : ByteArray) (stop : USize) (hs : stop.toNat ≤ a.size) (mask : USize) (k : Nat) (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1)
    (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
    (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) : RawRun :=
  if hn : n = 0 then ⟨word, count, pos, ring, wpos, p1, p2, n⟩
  else
    have hnext : (ringNext wpos mask).toNat < 2 ^ k := by
      unfold ringNext
      rw [USize.toNat_and, hmask, Nat.and_two_pow_sub_one_eq_mod]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    have hr : wpos.toNat < ring.size := by omega
    if 8 ≤ count then
      let byte := word.toUInt8
      rawRun a stop hs mask k hk hmask (n - USize.ofNat 1) (word >>> 8) (count - 8) pos (ringWrite ring wpos byte hr) (ringNext wpos mask)
        byte p1 hp ((size_ringWrite ring wpos byte hr).trans hsize) hnext
    else
      let r := refill word count a pos stop hs hp
      if h8 : 8 ≤ r.count ∧ r.pos ≤ stop then
        let byte := r.word.toUInt8
        rawRun a stop hs mask k hk hmask (n - USize.ofNat 1) (r.word >>> 8) (r.count - 8) r.pos (ringWrite ring wpos byte hr) (ringNext wpos mask)
          byte p1 (USize.le_iff_toNat_le.mp h8.2) ((size_ringWrite ring wpos byte hr).trans hsize) hnext
      else ⟨r.word, r.count, r.pos, ring, wpos, p1, p2, n⟩
termination_by n.toNat
decreasing_by
  all_goals
    have := usize_pred hn
    have := usize_ne hn
    omega

/-- What the loop for uncompressed bytes must do. -/
structure RawOk (a : ByteArray) (stop : USize) (k : Nat) (word count : UInt64) (pos : USize) (out : List Nat) (N : Nat) (moved : List Nat)
    (r : RawRun) : Prop where
  len : moved.length + r.left.toNat = N
  bytes : ∀ b ∈ moved, b < 256
  ring : RingOk r.ring k r.wpos.toNat (moved.reverse ++ out)
  ctx : contextBytes (moved.reverse ++ out) = (r.p1.toNat, r.p2.toNat)
  wf : (BitBuffer.mk r.word r.count).Wf
  posLe : pos.toNat ≤ r.pos.toNat
  posStop : r.pos.toNat ≤ stop.toNat
  short : r.left.toNat ≠ 0 → r.count.toNat < 8 ∧ r.pos = stop
  bits : ∀ (w : Nat) (st : StreamState) (last : Bool) (F : List Bool), st.output = out →
    rawK w st last N (availBits word count a pos stop F) =
      rawK w ⟨moved.reverse ++ out, st.produced + moved.length, st.distances⟩ last r.left.toNat (availBits r.word r.count a r.pos stop F)

/-- One byte taken from the buffer. -/
theorem RawOk.take {a : ByteArray} {stop : USize} {k : Nat} {word count : UInt64} {pos : USize} {out moved : List Nat} {N : Nat} {r : RawRun}
    (h8 : 8 ≤ count) (h : RawOk a stop k (word >>> 8) (count - 8) pos (word.toUInt8.toNat :: out) N moved r) :
    RawOk a stop k word count pos out (N + 1) (word.toUInt8.toNat :: moved) r := by
  have hb : (word.toUInt8.toNat) < 256 := word.toUInt8.toNat_lt
  have hrev : (word.toUInt8.toNat :: moved).reverse ++ out = moved.reverse ++ word.toUInt8.toNat :: out := by simp
  refine ⟨?_, ?_, ?_, ?_, h.wf, h.posLe, h.posStop, h.short, fun w st last F hst => ?_⟩
  · have := h.len
    simp only [List.length_cons]
    omega
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb
    · exact h.bytes x hx
  · rw [hrev]
    exact h.ring
  · rw [hrev]
    exact h.ctx
  · have hread := read_int (b := ⟨word, count⟩) (k := 8) (chunkBits a pos.toNat stop.toNat ++ F) (by decide) h8
    have hv : ((BitBuffer.mk word count).peek 8).toNat = word.toUInt8.toNat := by
      rw [BitBuffer.peek_toNat _ (by decide), UInt64.toNat_toUInt8]
      rfl
    rw [hv] at hread
    have hb1 := h.bits w ⟨word.toUInt8.toNat :: st.output, st.produced + 1, st.distances⟩ last F (by rw [hst])
    rw [avail_mk, rawK_succ, show readInt 8 ((BitBuffer.mk word count).held ++ (chunkBits a pos.toNat stop.toNat ++ F)) = _ from hread]
    show rawK w ⟨word.toUInt8.toNat :: st.output, st.produced + 1, st.distances⟩ last N (availBits (word >>> 8) (count - 8) a pos stop F) = _
    rw [hb1, hrev]
    simp only [List.length_cons]
    rw [show st.produced + 1 + moved.length = st.produced + (moved.length + 1) by omega]

/-- What the loop for uncompressed bytes does. -/
theorem rawRun_spec {a : ByteArray} {stop : USize} {hs : stop.toNat ≤ a.size} {mask : USize} {k : Nat} (hk : k ≤ 24) (hmask : mask.toNat = 2 ^ k - 1) :
    ∀ (N : Nat) (n : USize) (word count : UInt64) (pos : USize) (ring : ByteArray) (wpos : USize) (p1 p2 : UInt8)
      (hp : pos.toNat ≤ stop.toNat) (hsize : ring.size = 2 ^ k) (hwp : wpos.toNat < 2 ^ k) (out : List Nat), n.toNat = N →
      (BitBuffer.mk word count).Wf → RingOk ring k wpos.toNat out → contextBytes out = (p1.toNat, p2.toNat) →
      ∃ moved, RawOk a stop k word count pos out N moved (rawRun a stop hs mask k hk hmask n word count pos ring wpos p1 p2 hp hsize hwp) := by
  intro N
  induction N with
  | zero =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp out hN hw hr hc
    have hz := usize_zero hN
    rw [rawRun, dite_eq_left hz]
    refine ⟨[], ⟨by simp only [List.length_nil]; omega, by simp, by simpa using hr, by simpa using hc, hw, Nat.le_refl _, hp,
      fun h => absurd hN h, fun w st last F hst => ?_⟩⟩
    subst hst
    have e : (⟨([] : List Nat).reverse ++ st.output, st.produced + ([] : List Nat).length, st.distances⟩ : StreamState) = st := rfl
    rw [e]
    show rawK w st last 0 _ = rawK w st last n.toNat _
    rw [hN]
  | succ N ih =>
    intro n word count pos ring wpos p1 p2 hp hsize hwp out hN hw hr hc
    have hn : n ≠ 0 := fun e => by rw [e] at hN; exact Nat.succ_ne_zero _ hN.symm
    have hpred := usize_pred hn
    rw [rawRun, dite_eq_right hn]
    dsimp only
    by_cases h8 : 8 ≤ count
    · rw [ite_eq_left h8]
      have h8' := UInt64.le_iff_toNat_le.mp h8
      have hrw := hr.write (v := word.toUInt8) hk hmask (by rw [hsize]; exact hwp)
      have hw1 : (BitBuffer.mk (word >>> 8) (count - 8)).Wf := drop_wf' hw (k := 8) (by decide) h8
      obtain ⟨moved, hm⟩ := ih (n - USize.ofNat 1) (word >>> 8) (count - 8) pos _ _ word.toUInt8 p1 hp _ _ (word.toUInt8.toNat :: out) (by omega) hw1 hrw
        (by rw [contextBytes_push, hc])
      exact ⟨_, hm.take h8⟩
    · rw [ite_eq_right h8]
      have hc8 : count.toNat < 8 := Nat.lt_of_not_le fun e => h8 (UInt64.le_iff_toNat_le.mpr e)
      obtain ⟨r1, r2, r3, r4, r5⟩ := refill_spec (word := word) (count := count) hs hp hw
      have hbits : ∀ F, availBits word count a pos stop F =
          availBits (refill word count a pos stop hs hp).word (refill word count a pos stop hs hp).count a (refill word count a pos stop hs hp).pos stop F := by
        intro F
        show (BitBuffer.mk word count).held ++ (chunkBits a pos.toNat stop.toNat ++ F) =
          (refill word count a pos stop hs hp).buf.held ++ (chunkBits a (refill word count a pos stop hs hp).pos.toNat stop.toNat ++ F)
        rw [← List.append_assoc, ← List.append_assoc, r4]
      have hle : (refill word count a pos stop hs hp).pos ≤ stop := USize.le_iff_toNat_le.mpr r3
      by_cases h8r : 8 ≤ (refill word count a pos stop hs hp).count
      · rw [dite_eq_left ⟨h8r, hle⟩]
        have hrw := hr.write (v := (refill word count a pos stop hs hp).word.toUInt8) hk hmask (by rw [hsize]; exact hwp)
        have hw1 : (BitBuffer.mk ((refill word count a pos stop hs hp).word >>> 8) ((refill word count a pos stop hs hp).count - 8)).Wf :=
          drop_wf' r1 (k := 8) (by decide) h8r
        obtain ⟨moved, hm⟩ := ih (n - USize.ofNat 1) ((refill word count a pos stop hs hp).word >>> 8) ((refill word count a pos stop hs hp).count - 8)
          (refill word count a pos stop hs hp).pos _ _ (refill word count a pos stop hs hp).word.toUInt8 p1 (USize.le_iff_toNat_le.mp hle) _ _
          ((refill word count a pos stop hs hp).word.toUInt8.toNat :: out) (by omega) hw1 hrw (by rw [contextBytes_push, hc])
        have ht := hm.take h8r
        refine ⟨_, ⟨ht.len, ht.bytes, ht.ring, ht.ctx, ht.wf, Nat.le_trans r2 ht.posLe, ht.posStop, ht.short, fun w st last F hst => ?_⟩⟩
        rw [hbits]
        exact ht.bits w st last F hst
      · rw [dite_eq_right (fun h => h8r h.1)]
        have hcr : (refill word count a pos stop hs hp).count.toNat < 8 := Nat.lt_of_not_le fun e => h8r (UInt64.le_iff_toNat_le.mpr e)
        have hposS : (refill word count a pos stop hs hp).pos = stop := r5.resolve_left (by omega)
        refine ⟨[], ⟨by simp only [List.length_nil]; omega, by simp, by simpa using hr, by simpa using hc, r1, r2, r3,
          fun _ => ⟨hcr, hposS⟩, fun w st last F hst => ?_⟩⟩
        subst hst
        have e : (⟨([] : List Nat).reverse ++ st.output, st.produced + ([] : List Nat).length, st.distances⟩ : StreamState) = st := rfl
        rw [e, hbits]
        show rawK w st last (N + 1) _ = rawK w st last n.toNat _
        rw [hN]

/-- With input short of a byte, the spec has nothing to give. -/
theorem rawK_short {w : Nat} {st : StreamState} {last : Bool} {n : Nat} {b : BitBuffer} (h0 : n ≠ 0) (hc : b.count.toNat < 8) :
    rawK w st last n b.held = none := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [rawK_succ, readInt_short hc]
  rfl

end Brotli.Decoder
