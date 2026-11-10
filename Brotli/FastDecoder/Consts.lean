module

public import Brotli.FastDecoder.Prim

@[expose] public section

/-!
# The constant tables

What the format fixes for every stream, in the form the command loop reads (`DESIGN.md` 5.6, 5.7): what an
insert-and-copy symbol stands for, and the literal context of two bytes under each context mode. They are the
decoder's own, computed once when the program starts; the proofs will tie them to the specification's.
-/

namespace Brotli.FastDecoder

/-- The insert length codes: extra bits and base. -/
def insCodes : List (Nat × Nat) :=
  [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 6), (1, 8), (2, 10), (2, 14), (3, 18), (3, 26), (4, 34),
   (4, 50), (5, 66), (5, 98), (6, 130), (7, 194), (8, 322), (9, 578), (10, 1090), (12, 2114), (14, 6210), (24, 22594)]

/-- The copy length codes: extra bits and base. -/
def copyCodes : List (Nat × Nat) :=
  [(0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (0, 7), (0, 8), (0, 9), (1, 10), (1, 12), (2, 14), (2, 18), (3, 22),
   (3, 30), (4, 38), (4, 54), (5, 70), (5, 102), (6, 134), (7, 198), (8, 326), (9, 582), (10, 1094), (24, 2118)]

/-- What insert-and-copy symbol `s` stands for, in one word: the insert length's extra bits (bits 0 to 4), the copy
length's (5 to 9), whether the distance is the last one (10), the distance's context (11 and 12), the insert length's
base (16 to 31) and the copy length's (32 to 47). -/
def cmdWord (s : Nat) : UInt64 :=
  let cell := s / 64
  let ic := [0, 0, 0, 0, 8, 8, 0, 16, 8, 16, 16].getD cell 0 + s / 8 % 8
  let cc := [0, 8, 0, 8, 0, 8, 16, 0, 16, 8, 16].getD cell 0 + s % 8
  let (ie, ib) := insCodes.getD ic (0, 0)
  let (ce, cb) := copyCodes.getD cc (0, 0)
  let last := if cell < 2 then 1 else 0
  let dctx := if cc < 3 then cc else 3
  UInt64.ofNat ((last + dctx * 2) * 16 + (ie + ce) * 256 + ie * 65536 + ce * 16777216 + ib * 4294967296 +
    cb * 281474976710656)

/-- `cmdWord` for each of the 704 symbols, 8 bytes each. -/
def cmdInfo : ByteArray :=
  ⟨Array.ofFn (n := 5632) fun i => (cmdWord (i.val / 8) >>> UInt64.ofNat (8 * (i.val % 8))).toUInt8⟩

theorem cmdInfo_size : cmdInfo.size = 5632 :=
  Array.size_ofFn

/-- The first 128 values of the UTF-8 mode's table for the last byte (RFC 7932, 7.1, `Lut0`); the rest follow a
rule. -/
def utf8Low : List Nat :=
  [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  4,  4,  0,  0,  4,  0,  0,
    0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
    8, 12, 16, 12, 12, 20, 12, 16, 24, 28, 12, 12, 32, 12, 36, 12,
   44, 44, 44, 44, 44, 44, 44, 44, 44, 44, 32, 32, 24, 40, 28, 12,
   12, 48, 52, 52, 52, 48, 52, 52, 52, 48, 52, 52, 52, 52, 52, 48,
   52, 52, 52, 52, 52, 48, 52, 52, 52, 52, 52, 24, 12, 28, 12, 12,
   12, 56, 60, 60, 60, 56, 60, 60, 60, 56, 60, 60, 60, 60, 60, 56,
   60, 60, 60, 60, 60, 56, 60, 60, 60, 60, 60, 24, 12, 28, 12,  0]

/-- The UTF-8 mode's part for the last byte. -/
def utf8Last (b : Nat) : Nat :=
  if b < 128 then utf8Low.getD b 0 else if b < 192 then b % 2 else 2 + b % 2

/-- The UTF-8 mode's part for the byte before the last (`Lut1`). -/
def utf8Prev (b : Nat) : Nat :=
  if b < 33 then 0
  else if b < 48 then 1
  else if b < 58 then 2
  else if b < 65 then 1
  else if b < 91 then 2
  else if b < 97 then 1
  else if b < 123 then 3
  else if b < 127 then 1
  else if b < 224 then 0
  else 2

/-- The signed mode's class of a byte (`Lut2`). -/
def signedClass (b : Nat) : Nat :=
  if b = 0 then 0
  else if b < 16 then 1
  else if b < 64 then 2
  else if b < 128 then 3
  else if b < 192 then 4
  else if b < 240 then 5
  else if b < 255 then 6
  else 7

/-- The context table: 512 bytes for each context mode (least significant 6 bits, most significant 6 bits, UTF-8,
signed), the first 256 the part the last byte gives and the next 256 the part the byte before it gives. The context is
the two parts or-ed. -/
def ctxTab : ByteArray :=
  ⟨Array.ofFn (n := 2048) fun i =>
    let b := i.val % 256
    let last := i.val / 256 % 2 = 0
    UInt8.ofNat <| match i.val / 512 with
      | 0 => if last then b % 64 else 0
      | 1 => if last then b / 4 else 0
      | 2 => if last then utf8Last b else utf8Prev b
      | _ => if last then signedClass b * 8 else signedClass b⟩

theorem ctxTab_size : ctxTab.size = 2048 :=
  Array.size_ofFn

/-- The block count codes: extra bits and lowest count. -/
def countCodes : List (Nat × Nat) :=
  [(2, 1), (2, 5), (2, 9), (2, 13), (3, 17), (3, 25), (3, 33), (3, 41), (4, 49), (4, 65), (4, 81), (4, 97), (5, 113),
   (5, 145), (5, 177), (5, 209), (6, 241), (6, 305), (7, 369), (8, 497), (9, 753), (10, 1265), (11, 2289), (12, 4337),
   (13, 8433), (24, 16625)]

/-- What each of the 26 block count symbols stands for, 4 bytes each: the lowest count in the low 2 bytes and the
count of extra bits in the top one. -/
def countTab : ByteArray :=
  ⟨Array.ofFn (n := 104) fun i =>
    let (bits, lo) := countCodes.getD (i.val / 4) (0, 0)
    UInt8.ofNat ((lo + bits * 16777216) >>> (8 * (i.val % 4)))⟩

theorem countTab_size : countTab.size = 104 :=
  Array.size_ofFn

/-- The order in which the lengths of the code-length code's 18 symbols come. -/
def clOrder : ByteArray :=
  ⟨#[1, 2, 3, 4, 0, 5, 17, 6, 16, 7, 8, 9, 10, 11, 12, 13, 14, 15]⟩


/-- For a word with the one bit `3 * s + 2` set (symbol `s` of a code-length code, in a mask of its 18 symbols 3 bits
apart), the symbol times 8, at the index `(word * 0x03F79D71B4CB0A89) >> 58`: that multiplier sends each of the 64
single bits to a different index. -/
def clSym : ByteArray :=
  ⟨Array.ofFn (n := 64) fun i =>
    UInt8.ofNat (8 * ((List.range 18).find? fun s =>
      ((((1 : UInt64) <<< UInt64.ofNat (3 * s + 2)) * (0x03F79D71B4CB0A89 : UInt64)) >>> 58).toNat = i.val).getD 0)⟩
