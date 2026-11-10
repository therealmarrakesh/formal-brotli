# A clean decoder

The seed for a new Brotli decoder, written from scratch. This document is self-contained: it states what the decoder
must do, the principles it is designed by, how Lean compiles the kind of code it needs, and the design itself, part by
part. It refers to no other document.

Each part of the design carries a status:
- **decided:** settled, by argument or by a probe of the generated code;
- **proposed:** the position the design takes, not yet built;
- **to measure:** a choice between alternatives that only running code on real streams can make (section 8).

A *probe* in this document is a small throwaway Lean file, compiled, whose generated C or assembly was read. Probes
give counts of instructions and of values kept on the stack. They do not give time.

## 1. Purpose and scope

A complete streaming decoder for the Brotli compressed data format (RFC 7932), written in Lean, designed for speed
from first principles, and afterwards proved correct against a formal specification of the format.

- **Complete:** the whole decoder, from the first byte of a stream to its last: the stream's framing, every kind of
  meta-block, the headers and their tables, the commands, the window and the output.
- **From scratch:** it is not derived from the specification's executable definitions or from any earlier decoder. It is
  designed as a decoder, and tied to the specification by proof afterwards.
- **Design first, proofs once:** the design is free until it is settled. The large proofs (section 7) are written once,
  against the settled design. Small local obligations are proved as the code is written.
- **Out of scope:** RFC 9841 (Shared Brotli); an encoder; any use other than decoding a stream through the interface of
  section 2.3.

## 2. Fixed points

What the design accepts as given.

### 2.1 The format

A summary for orientation, checked against the specification (2.2), which fixes every detail.

- **A stream** is a sequence of bits, read from each byte's least significant bit first. It starts with the window size
  (WBITS, 10 to 24, in 1, 4 or 7 bits: the window is `2 ^ WBITS - 16` bytes) and continues with meta-blocks until one
  marked last. After the last, the bits to the next byte boundary must be zero and nothing may follow.
- **A meta-block's start** is at most 31 bits: whether it is the last (and if so whether it is empty), the size of its
  length field and its length MLEN (1 to 16,777,216 bytes), and for a block that is not the last, whether it is
  uncompressed. A meta-block is one of: *compressed*, producing MLEN bytes from commands; *uncompressed*, MLEN bytes
  copied from the input at a byte boundary; *metadata*, bytes to skip that produce nothing; or the *empty last* block.
- **A compressed meta-block's header** declares, in this order: for each of three categories (literals L,
  insert-and-copy lengths I, distances D), the number of *block types* (1 to 256) and, where there is more than one,
  a prefix code for switching type, a prefix code for block lengths and the first block's length; the distance
  parameters NPOSTFIX and NDIRECT; a *context mode* for each literal block type; the number of literal prefix codes
  with their *context map* (64 entries a block type), and the same for distances (4 entries a block type); and then the
  prefix codes themselves: the literal codes (256 symbols), one insert-and-copy code for each I block type (704
  symbols), and the distance codes (`16 + NDIRECT + (48 << NPOSTFIX)` symbols, at most 520).
- **A prefix code** is given in simple form (one to four symbols, each named in as many bits as the alphabet needs) or
  by code lengths. Code lengths are themselves prefix coded, by a code of 18 symbols whose own lengths come first: 16
  lengths, a repeat of the last non-zero length (which starts at 8), and a repeat of zero, consecutive repeats
  combining. The lengths end exactly when the code is complete. No code is longer than 15 bits; a code of one symbol has
  length zero and is read from no bits. Codes are assigned in order of length and, within a length, of symbol.
- **A context map** is a small prefix code's values with runs of zeros, optionally followed by an inverse move-to-front
  transform. Every code of its category must occur in it.
- **A command** is an insert-and-copy symbol, giving an insert length (up to 16,799,809) and a copy length (up to
  16,779,333), each a base and up to 24 extra bits, and whether the distance is the last one used; then that many
  *literals*; then, unless implied, a *distance*; then the *copy*. Commands repeat until the meta-block's MLEN bytes are
  produced. Literals that reach MLEN exactly end the meta-block, and that command's distance and copy are not read;
  literals or a copy that pass it are invalid.
- **A literal** is read with the prefix code that the context map gives for the current literal block type and a
  context computed from the previous two output bytes (zero at the stream's start) under that block type's context
  mode: 64 contexts.
- **A distance** is read with the code the distance context map gives for the current distance block type and a context
  from the copy length (4 contexts). Symbols 0 to 15 are one of the last two distances with an offset of -3 to 3, or the
  third or fourth last; a result of zero or less is invalid. The next NDIRECT are direct distances; the rest are a base
  and up to 24 extra bits shifted by NPOSTFIX. A distance is pushed onto the last four unless it came from symbol 0 (or
  was implied) or is a dictionary reference.
- **A copy** repeats bytes already output, `distance` back, one at a time, so it may overlap what it writes. A distance
  beyond the smaller of the window and the bytes produced so far refers to the *static dictionary*: the copy length is
  the word's length (4 to 24, anything else invalid), and the excess selects a word and one of 121 *transforms* (a
  prefix, an elementary change to the word, a suffix; a transform number of 121 or more is invalid); the transformed
  word, under 40 bytes, is output in place of the copy.
- **Block switching:** each category counts down a block length (at most 16,793,840); when it is zero before an element
  of that category, a block type and a new length are read first. A switch may not name the type already current, and
  every declared block type must be used in the meta-block. A category with one type has a length no meta-block can
  exhaust.

### 2.2 The reference

`Brotli.Spec.decode : List UInt8 → Option (List UInt8)` defines the format: the output of a valid stream, or `none` for
an invalid one. The specification is separate from the decoder and never depends on it.

**The reading of a prefix — proposed.** `decode` judges whole streams, and its readers fail alike on an invalid stream
and on one that has merely run out. A streaming decoder's properties are about prefixes. So the specification is to
gain a *reading* of any sequence of bytes, by its own readers made to tell the two failures apart, giving the output
produced so far and one of three verdicts: *more* (the reading needs a bit that is not there), *invalid*, or
*complete*. Two facts about it belong to the specification: the reading of a longer input extends the output of a
shorter one's unless the shorter is already invalid or complete; and `decode x` is the output of `x`'s reading when
that is complete and `none` otherwise, so the format means what it meant. The contract (2.4) is stated against this
reading.

### 2.3 The interface

One call takes the decoder's state, an input array with the start and stop of the chunk inside it, the caller's output
buffer, the output space, and a flag saying the input ends with this chunk. It returns the new state, how many input
bytes it used, the buffer with output appended, and a status: *needs input*, *needs output*, *done*, *rejected* or
*memory limit*. The decoder is started with a memory limit. A caller may deliver the stream in chunks of any sizes and
offer any amount of output space on each call.

### 2.4 The contract

The correctness properties the decoder is to be proved to have, for every input and every way of delivering it. They
are requirements, to be proved, not aims: speed is an aim, to be measured.

**1. The verdict.** For any stream, delivered to its end by a caller who answers each status (more input or the end
after "needs input", some space after "needs output"), the run ends, and in exactly one of three ways:
- *done,* with the specification's output handed over, if and only if the stream is valid;
- *rejected,* if and only if it is invalid;
- *the memory limit,* only if the stream needs more memory than the limit (4).

**2. The output.** At every return, the bytes handed out so far are a prefix of what the specification's reading of
the bytes received has produced. This holds whether or not the stream later turns out valid: a caller may act on a byte
when it gets it, knowing it is what the format says those bits mean.

**3. Streaming.**
- *The statuses mean what they say:*

  | status | what is true when it is returned |
  |---|---|
  | needs input | the chunk is all used; the end has not been signalled; the reading of the bytes received wants more; and everything it has produced is handed out |
  | needs output | the space offered is full, and the reading of the bytes used has produced more than is handed out |
  | done | the end is signalled, every byte is used, the reading is complete and its output all handed out |
  | rejected | the reading of the bytes used is invalid, or the end is signalled and it still wants more |
  | memory limit | the bytes used demand more than the limit (4) |

  The first row is *promptness*: a decoder that asks for input is holding nothing back, so a stream flushed by its
  encoder is decoded as far as the flush.
- *Rejection is timely:* once the reading of the first `n` bytes of a stream is invalid, the decoder rejects before it
  has used more than `n` and a fixed number of bytes.
- *Blind to layout:* what a call returns depends only on the chunk's bytes, the space and the end flag: not on where
  the chunk lies in its array, what lies around it, or what the output buffer held.
- *A call keeps its bounds:* it uses no more than its chunk, keeps what the buffer held, and adds no more than the
  space.

**4. Memory.**
- *Bytes written* stay within what the stream has needed so far and a constant: the smaller of the declared window and
  the output its meta-blocks have declared, the room its headers ask for their tables, and a fixed cost.
- *Address space reserved* stays within the declared window and a constant.
- *The limit* is never exceeded; it is reported only when the stream's demand exceeds it, and before that demand is
  met; and it changes nothing else: two runs with different limits agree until one reports it.

**5. Progress.** Every call returns. Every call that answers the last status uses at least one byte of input, hands
out at least one byte, or stops; so a caller needs at most the stream's length, the output's length and a constant in
calls.

**Tabled** (owner, 2026-11-10): a property on work. It would say that no call stalls: a call's work, counted in a model
of the decoder's steps, is bounded by its chunk and its output space and a constant. It is the weakest claim for the
most proof (it is about a model, not what a caller observes; its constants say nothing of ordinary cost; and the caller
already bounds the output), so the decoder is not built to it. It may be taken up later, in that per-call form, with
the model chosen once the design is final. Its substance stays in the design as principle 5.

**Not promised:** that an invalid stream is rejected at the earliest possible bit (only within the bound above); that
the machine has memory to give.

### 2.5 The rules

- **Plain Lean:** the toolchain's own libraries, no external packages.
- **Trust:** proofs rest only on the kernel's standard axioms. No `sorry`, `axiom`, `native_decide`, `implemented_by`,
  `partial` or `unsafe` in the finished decoder. `@[csimp]` is allowed, since the kernel checks it.
- **One exception:** a small set of primitives in one module of the decoder's own, each an ordinary Lean definition
  (its body the model the proofs use) with a C implementation: a load, store, copy or fill of bytes within an array,
  every range inside the array by the primitive's signature, the array ensured to be held once where it is written.
- **Self-contained code:** the decoder's modules import only each other and Lean's own libraries. Its constants (the
  dictionary, the transforms, what symbols stand for) and its primitives are its own, in the form the fast code wants.
  Only the proofs import the specification, from modules of their own.
- **New primitives** may be added to that module when three things hold, and the owner is told afterwards: Lean's own
  runtime already does the same thing; it is proved safe (the model as its body, its ranges by its signature); and it is
  kept simple (a line or a short loop of C, with none of the decoder's logic in it).
- **Speed is never traded for proof effort.** Where the two conflict, the fast code stands and the proof takes the work.

## 3. Principles

1. **One machine.** There is one decoder, not a fast one and a slow one with hand-offs between them. Whatever is rare
   (a chunk's end, a full window, a block switch, an invalid stream) is handled as an event inside the same machine.
2. **State shaped by the hot path.** What the hot path carries is chosen first and kept few; everything else is arranged
   around it. No contract with another part of the decoder decides what the hot path carries.
3. **Write values where they are needed.** Nothing is built in one place and copied to another: a literal, a copy, a
   dictionary word and a table entry are each written once, at their destination.
4. **No allocation while decoding.** Memory is taken once for a stream. No record is built per step, per command or per
   event; a call allocates its reply and nothing else.
5. **No path pathologically slow.** The hot paths are identified from the format: reading a literal, reading a command,
   a copy. Every other path may be slower than these but none by an order that a stream could exploit or that an
   ordinary stream would feel. Every bounded but unusual cost is recorded where it arises.
6. **Decide once what can be decided once.** What a header fixes for its meta-block is decided when the header is read,
   not tested on every symbol.
7. **Few limits in the hot path.** The hot path tests as few bounds as the format allows, each covering every reason of
   its kind to stop; which reason it was is worked out when the bound is reached.
8. **Checks by proof, not at run time.** A test that an invariant already guarantees is not made. The tests that remain
   are those that decide between valid and invalid streams, and those that find events.
9. **Small, contiguous, predictable memory.** One buffer, with tables laid out for the order the hot path reads them.
10. **Every assumption written down.** Each fact the fast code relies on is stated where it is used, as a hypothesis or
    a proved bound, and collected in the invariant ledger (section 6).
11. **The cost follows the stream.** Work and memory are in proportion to what a stream uses, never to the size of an
    alphabet or of a window it does not fill.

## 4. What the compiler gives us

How Lean compiles the kind of code this decoder needs, as rules for writing it. Each rule was read in generated code,
by a probe or in existing code; the generated code of the real decoder, not this list, is the authority.

**Loops**
- A function whose recursion is in tail position compiles to a loop; its arguments are the loop's carried values.
  There is no other loop: a variable-length inner loop has to be rounds of the same function, or a function of its own,
  and a function that returns more than one value returns a record, which is allocated.
- Two paths that meet inside a function (a local function used at two places) compile to a join point, with no closure
  and nothing allocated. Each join point has its own homes for the live state.

**Calls are the constraint on registers**
- The target has 15 usable general registers, of which a call preserves 8. A value alive across a call must be in one
  of the 8 or on the stack.
- Every store into an array is followed by the path for an array that is not held once, which calls a function that
  copies it. The path is never taken in this decoder, but it is a call. So what matters for a loop is how many values it
  carries, how many store sites it has, and how much is alive across each; not the count of registers alone.
- Marking that path unlikely moves it out of line and changes nothing about what is kept on the stack.
- A loop at the limit is fragile: a change to a cold part of its function can move its hot path.

**Records and allocation**
- A structure with fields built at run time is allocated, unless the compiler can reuse a dead one of the same shape. A
  function that is not inlined and returns a structure allocates it on every call. A value returned with a proof, as a
  subtype, is a structure for this purpose. A pair holding a machine-word value boxes it.
- A function from one array to the same array returns no record: this is how the parts of this decoder talk (5.1).

**Arrays**
- An array is updated in place only while it is held exactly once. Reading a field of a structure and writing the array
  it holds, while the structure is still live, shares the array, and the write copies it.
- Every store tests that its array is held once: a compare and a well-predicted branch, two instructions, with the call
  above behind it.
- An unchecked read or write needs a proof of its bound at the point of use and then costs only the access.
- Byte reads combined by shifts and ors compile to one wide load only when every bit of the value is used; otherwise
  the C compiler loads the bytes it needs in pieces. The load primitive (below) is one load always.
- A loop of single-byte stores is not vectorised. Copies and fills go through the primitives.
- A value read from an array at a constant offset and compared compiles to a comparison straight from memory; a value
  updated there, to a load and a store behind the two-instruction test.

**The primitives** (2.5)
- Copies within an array: a `memmove` of any length; a 16-byte copy of two ranges that are apart.
- Stores of the low 2, 4 or 8 bytes of a value; a strided fill of a 2-byte value.
- A load of 8 bytes, `loadLE64 t i (h : i.toNat + 8 ≤ t.size) : UInt64`, decided for this decoder: its body the bytes
  combined, its C one `memcpy` of 8 bytes into a local, the array borrowed. By the rule for new primitives: the runtime
  already reads an array's bytes so; the range is inside the array by the signature, and a read changes nothing, so no
  held-once test is needed; and it is one line. Probed: every refill becomes one load, 8 instructions fewer each.

**One definition, several compiled loops**
- A loop that takes a `Bool` flag is compiled once, with the flag carried and tested every round; `@[specialize]` does
  not change that.
- A loop marked `@[specialize]` that takes the varying part as a *function* is compiled once for each function it is
  called with. Called with a function that always answers the same, the compiled loop has no test and carries nothing
  for the choice, and a value only the test used is dropped from the loop as well. Called with a real test, the test is
  compiled in line. The same holds for a method of a type class at two types, and for a macro that writes the definition
  twice. Probed at the size of a real loop, with four such functions.
- So a mode or an alternative is passed as a function, never as a flag, and costs the loop that does not need it
  nothing.

**Arithmetic, constants, choices**
- Fixed-width arithmetic compiles to machine operations. Natural-number arithmetic may call the big-number library and
  is kept out of code that runs.
- A numeral next to a fixed-width value may be read as a natural number and fail to elaborate; each is given its type.
- A constant that needs computing is initialised on first use and tested on every use; a literal is free; a constant
  array kept by the program is read by one load of its address.
- A chain of equality tests on a small index compiles to a jump table; a choice computed from bits, to conditional
  moves.
- A mask built from a width that is a variable costs four instructions; a mask that is a constant, none.

## 5. The design

### 5.1 Architecture — proposed

**Everything the decoder knows is in one buffer.** `buf` (5.2) holds the window, a meta-block's tables, a staging area
for input, and at its front the *slow state*: everything not carried by a running loop, including where the stream
stands (the phase), what each loop saved when it last left, and why it left. So the decoder's state between calls is
the buffer and nothing else, and no part of the decoder returns a record to another: each returns `buf`.

**Three kinds of function**

1. *Phase loops.* One for each stretch of the stream that reads elements (5.4): the stretches of a header (5.7) and the
   commands (5.6). Each takes `buf`, loads its few scalars from the slow state, runs until something it does not handle
   itself, saves its scalars and the reason, and returns `buf`. Each is written once and compiled for the two modes of
   5.4. None makes a call, but for the one noted in 5.6.
2. *Event handlers.* Small functions, also from `buf` to `buf`, for what a loop leaves for: a block switch, a command
   that does not fit whole, a copy that needs care, building a code's table, a meta-block's end. These may make calls;
   they run once an event. They use the same reading functions the loops use.
3. *The driver.* One loop, the only function that holds the caller's two arrays as well as `buf`. Each time round it
   reads the phase and the reason and does one thing: calls a phase loop; calls a handler; or does itself what touches
   the caller's arrays or ends the call: staging input (5.4), handing out output (5.5), copying uncompressed data and
   passing over metadata (5.8), and returning a status.

**A call** writes its parameters into the slow state, runs the driver, and builds the reply the interface asks for.
That reply is the only thing a call allocates.

**What an event costs.** Leaving a loop is a handful of stores into the slow state and a return; entering again is a
call and a handful of loads: some tens of instructions, with nothing allocated. So what is made an event must be rare
against the work it stands for. What happens every few commands may not be one, and the loops are shaped so that it
is not (5.6).

**One machine** (principle 1). The phase loops in their two modes are the only readers of the stream; the handlers
finish what a loop began, with the same state and the same reading functions; and the driver reads no input and writes
no output of its own except to move bytes between the caller and `buf`.

**The phases**

| phase | what is read there | who does it |
|---|---|---|
| the window size | 1, 4 or 7 bits | a single element |
| a meta-block's start | at most 31 bits | a single element |
| metadata | bytes to pass over | the driver |
| uncompressed data | bytes to copy | the driver |
| a header | in its stretches (5.7) | phase loops and handlers |
| the commands | 5.6 | the command loop and handlers |
| the end | zero bits to the byte boundary, then nothing | the driver |
| done, rejected, the memory limit | nothing: every call returns the same | the driver |

### 5.2 The buffer — proposed

**The layout,** front to back:

1. *The slow state:* a few hundred bytes at fixed offsets.
2. *The distance symbols' table* (5.7): at most 520 entries of 8 bytes.
3. *The staging area for input* (5.4): a few kilobytes, small because the whole front is written when a stream starts
   and the smallest streams should not pay for more.
4. *The table builder's lists* (5.7): about 1.5 KB. They are in the front, not with the tables, so that their positions
   are constants: the builder's reads and writes of them need no base, and a bound on one is a fact about a constant.
5. *Two guard bytes* (5.5).
6. *The ring:* the window's `2 ^ WBITS` bytes, written as far as the stream has needed so far, and a few tens of bytes
   of slack after the written part.
7. *The current meta-block's tables* (5.7), just past the ring's written part and its slack.

**Why the tables can sit after the ring.** An array grows only at its end, a byte is part of it only once written, and
whatever lies before a region fixes where the region starts; the ring and the tables both vary in size. But a
meta-block states its length before any of its tables are read. So when a meta-block starts, the ring's end for the
whole of that meta-block is known: the smaller of the ring and the bytes produced so far plus the length. The tables are
built just past that end, and nothing the meta-block writes can reach them. At the next meta-block they are dead: the
ring's written part moves forward over them, and the new tables are built past the new end. Once the ring is full its
end no longer moves.

**What this gives**
- The ring never moves, and neither region needs a reserved maximum inside the array.
- The array's size is the front, the ring as far as the stream has needed it, and the largest tables so far (contract
  4).
- Extending the ring's part over dead tables writes nothing; only what lies beyond the array's present end is filled,
  once, when a meta-block starts. So no loop writes beyond what the array holds, and none tests for it.

**Capacity — measured.** The array is given its room once, at the first meta-block's start, and is extended only
within that room: it is never copied to grow and never held twice.
- *Where the first meta-block is also the last,* its length is the stream's whole output, and the room is exactly the
  front, that length, the slack and the largest tables.
- *Otherwise* the room is for the declared window.
- *What the larger room costs:* allocating, writing a little and freeing a buffer with room for megabytes took 0.2 to
  0.3 microseconds, against 0.02 for one of up to 128 KiB; with 64 KiB written, 1.2 against 1.0. (One buffer taken and
  released over and over: the allocator's best case.) A few parts in a hundred of the very smallest decodes.
- *The alternative weighed:* grow at a meta-block's start by a new allocation and a copy. It makes the smallest
  allocations always, but holds two buffers while it copies, which contract 4 does not allow, and it copies.

**The largest tables** the format allows, for the room: with the table format of 5.7 and its root capped at 8 bits,
about 1.5 MB.

**That figure is out of date — to revisit once the whole decoder has landed** (owner, 2026-11-10). It was worked out
before step 3. Three choices made there (8.1) make tables larger: a context table of 8 KB for every literal block
type that has contexts, and a stream may declare 256 (about 2 MB); entries of 8 bytes, not 2, for insert-and-copy and
distance codes; and a root of at least 256 entries for every literal table. The largest tables a stream can ask for
are now several megabytes (the harness gives them 6 MB), and the new figure has not been worked out. It sets the room
the buffer reserves and the constant in the memory part of the contract (2.4), so it is settled, with those three
choices, when the whole decoder is measured.

**What the proofs pay.** With one array, every store must be shown to leave the other regions as they were, where
separate arrays would give that for nothing. It is mechanical, but it is at every step.

### 5.3 State — decided in shape (probed)

**Six values are carried by the command loop:** `buf`; `bitpos`, the position in `buf` of the next unread bit;
`opos`, the position in `buf` where the next output byte goes; the *counters* (5.6); the *literals* the command in hand
still owes, with the two bytes before them; and the *command in hand* (its copy length and distance flag, or what a
copy has left).

**What is not carried**
- *No word of bits and no count of them.* Every step starts with a refill, computed from `bitpos` alone (5.4), so the
  word lives inside a step.
- *No end of input, no end of output:* the counters and one comparison stand for them (5.6).
- *No mask and no window size:* positions are plain (5.5).
- *Nothing a meta-block fixes,* and nothing that changes only at events: these are in the slow state, read at constant
  offsets when used.

**Compute, then store.** A step finishes its arithmetic before its store, so that only the next round's values are
alive across the store's call path (section 4).

**Probed** on a toy loop of the real one's shape (contexts, named tables, the distance formula, block copies, the packed
counters; one buffer; about 420 instructions): three values are kept on the stack (the counters, the command in hand,
and the output position on one path) and five places reload one; everything else stays in registers. An earlier form
with three arrays and eight carried values kept 21 on the stack with 22 reloads.

### 5.4 Input and pausing — decided in shape

**What the contract forces.** A chunk may end anywhere, "needs input" means the whole chunk was used, and a decoder
that asks for input has handed out everything the bytes received produce (contract 3). So the last bytes of every chunk
must be decoded exactly, down to the first read the bytes received cannot complete.

**The bit reader.** `bitpos` is the position of the next unread bit. A *refill* loads the 8 bytes at `bitpos / 8` (the
load primitive) and shifts down by `bitpos % 8`: at least 57 bits, by two instructions and a load, with no test.
Consuming bits adds to `bitpos`. Nothing ever asks how many bits are held. *(To measure, section 8: against a buffer
shifted in place with a count, which carries two more values but keeps the load off the chain every later read waits
on.)*

**Elements.** The input is read in *elements*, each at most 56 bits, so that one refill covers one element: a literal
(at most 15 bits); a command's head (see below); a distance's symbol with its extra bits (39); a block switch's type,
length and the length's extra bits (54); a context map's symbol with its extra bits (31); a code length with its extra
bits (8); a meta-block's start (31); and the header's other fields. A command's head is its symbol and both lengths'
extra bits, at most 63 bits: it is read from one refill, with a second where the extra bits exceed what is left, a
branch that needs a length in the millions. An element is read whole or not at all; an element of no bits (a symbol of
a one-symbol code) is always wholly present. The state between elements is complete, and a pause falls only between
elements.

**The staging area.** The loops read input only from `buf`. The driver copies the caller's chunk into the staging area
a piece at a time: it moves the unread tail to the area's front, lowers `bitpos` by what it dropped, and copies the next
piece after it; when the chunk is used up it writes zeros after the last real byte. So the caller's array is never read
by a loop (which gives blindness to layout), and a refill always has 8 bytes to load.

**Two modes, one definition.** Every loop that reads input is written once and compiled twice (section 4):
- *Running,* while a margin of real input lies ahead in the staging area. Reads are unconditional and nothing about
  the input is tested.
- *Exact,* in the last bytes of a chunk, with zeros after them. Reads are still unconditional. After each element is
  read, and before it has any effect, `bitpos` is compared with the last real bit: if the element used only real bits it
  takes effect; if not, the loop leaves with its state as it was before the element. Nothing needs undoing, because a
  step computes before it stores (5.3) and the old values are still at hand.
The mode is passed to a loop as that test, a function, so the running loop is compiled with no test and nothing carried
for the choice. Running mode is exact mode with a test the margin makes always true, which is its proof. The window
size and a meta-block's start, read once each, are compiled in exact mode only.

**No input test in the running loop: a budget.** Every element has a largest size, so a round of a loop has a largest
input cost (for the command loop, 43 bytes: 5.6). From the real input ahead, the number of rounds certain to stay inside
it is computed, and the loop runs that many with no test of the input. The count is one field of the counters (5.6);
when it runs out it is computed again inside the loop from the slow state, and only when the input ahead is really
short does the loop leave, for the driver to stage more or to change the mode.

**A call's shape**
1. The staging area holds what the last call left: the bytes of at most one unfinished element, under 9.
2. The driver stages the first piece of the chunk after them.
3. The loops run, in running mode while the margin lasts, the driver staging further pieces.
4. When the chunk is used up, the loops run in exact mode until an element needs bits that are not there.
5. That element's bytes stay in the staging area; the waiting output is handed over; the status is "needs input".

**The end of the stream.** When the end is signalled, step 4's stop is final: an element that needs bits that are not
there means the input ended early, and the stream is rejected.

**The bytes a call reports used:** for "needs input" and "done", the whole chunk; for "needs output", what it has
staged so far; for "rejected" and "memory limit", the bytes of this call's chunk up to the bit position where it was
decided, worked out from `bitpos` and the count of bytes that were already in the staging area when the call began. An
element is judged only once it is read whole, which takes at least one bit of the present chunk, so that count is never
negative.

**Alternatives weighed**
- *A test at every read for the chunk's end,* each field able to stop half read: every reader resumable in the middle.
- *A second, careful decoder for the ends of chunks:* two machines (principle 1).
- *A margin alone, the tail left for the next call:* fails promptness.
- *The one compiled loop run a round at a time near the end:* a copy cannot be undone, so every command would need a
  test between its distance's read and its copy.
- *The input read in place, only the ends of chunks staged* (what Google's decoder does): not weighed when this was
  written; since probed and tabled (9.4).

### 5.5 Output and the window — proposed

**The ring.** The window's region of `buf` is a ring of `2 ^ WBITS` bytes. The format's window is 16 less than the
ring: a distance never reaches the 16 bytes ahead of the write position, which is where a block write may run over. The
format was made for this, and the design takes it as given.

**Positions**
- `opos`, where the next byte goes: a plain position in `buf`, never masked.
- *handed:* the position up to which bytes have been given to the caller. The bytes waiting are those from *handed* to
  `opos`, always a single run.
- *The bytes produced so far,* which with the window gives the largest distance a copy may use.

**The output's bound,** the one position a command's lengths are compared with (5.6), is the least of:
- *the meta-block's end;*
- *the ring's end;*
- *one byte more than the caller can take:* handed, plus the output space left in this call, plus one. So a call
  decodes until one byte more is waiting than the caller has room for, and no further: it does no work for output it
  cannot deliver, and "needs output" means there is certainly more.
It is set by the driver before a loop is entered and does not change while the loop runs.

**Handing out** is the driver's: one copy from the ring into the caller's buffer, of the bytes waiting or as many as
the space allows. It happens when the bound stops a loop for the caller's space; before "needs input"; before the wrap;
and before done. Every check on the reading behind a byte has passed before the byte is handed out, because a loop
leaves before the driver hands anything out (contract 2).

**The wrap.** When `opos` reaches the ring's end, every waiting byte is handed over first (pausing for output if the
caller has no room), the ring's last two bytes are copied to the guard, and `opos` and *handed* go back to the ring's
start. So waiting bytes never straddle the ring's end and are never overwritten.

**The guard.** A literal's context is the two bytes before the write position. The two bytes of `buf` just before the
ring hold what precedes the ring's first byte: zeros at the stream's start, and after a wrap the ring's last two bytes.
So the context is always read at `opos - 1` and `opos - 2`, with no case for the ring's start.

**A copy's source.** By the specification, the largest distance is the smaller of the window and the bytes produced.
- *Before the first wrap* the bytes produced are `opos` less the ring's start: a distance no more than that is a plain
  copy from `opos - distance`, and anything larger is a dictionary reference (or invalid). One comparison.
- *After it,* a distance within the window whose source falls before the ring's start is taken one ring-length further
  on, still a plain run of memory; a distance beyond the window is a dictionary reference.
- *A copy whose source or target run crosses the ring's end* is an event, done in two parts.
So a stream that produces no more than its window never meets the wrap, and one that produces more is not slowed by
it: only crossing the end is an event.

### 5.6 The command loop — decided in structure (probed); six choices to measure

**What streams are made of.** Counted on five streams of different kinds and encoder settings, to check what may be
an event and what must stay in the loop. They are not targets to tune to.

| | range over the five streams |
|---|---|
| commands with no literals | 49% to 80% |
| literals a command | 0.5 to 1.5 |
| runs of more than 8 literals | under 2.5% of commands |
| copies of at most 16 bytes | 44% to 88% |
| copies of more than 32 bytes | 1% to 50% |
| copies at a distance of 16 or less | 1% to 6% |
| copies that overlap themselves | under 0.2% |
| dictionary words | 0.9% to 14% of commands |
| block switches | 0.2 to 3.4 in a thousand commands |
| literals whose context is trivial | none, or all of them |
| distances that reuse one of the last four | 4% to 22% of explicit distances |

So: long copies are not rare and stay in the loop; overlapping copies are rare and need not be fast; dictionary words
are too common to be events; and runs of literals are short, so the first literals of a run must be cheap.

**The round, rotated.** A run of literals is the one part of a command that must be rounds of a loop. If the round
were a command from its head to its copy, whatever follows the literals would be compiled twice or reached by a second
pass through the loop's entry. So the round's boundary is put where the loop has to be:

> a round is the distance and copy of the command in hand, and then the head of the next command.

After the head, the next command's literals are rounds of their own, and then the loop comes back for that command's
distance and copy. Every part is written once; a command with no literals is exactly one round. The first round of a
run has no command in hand and starts at the head. The two kinds of distance meet at the copy, and the two ways to the
head meet at the head, as join points.

| the loop (probed) | instructions | values put on the stack | reloads | refill sites |
|---|---|---|---|---|
| a round for the head, a round for the distance | 462 | 10 | 6 | 4 |
| the head running on into the distance, compiled twice | 608 | 15 | 13 | 4 |
| rotated | 419 | 6 | 5 | 3 |

**The distance.** If the head said the distance is the last one, it is read from the slow state. Otherwise the
distance block's count is tested (a field of the counters) and lowered, the element is read, and the distance formed.
- *What a distance symbol stands for* is one 8-byte entry (5.7): which of the last distances to start from, or a slot
  that holds zero; a base (for the last distances, an offset of -3 to 3); a count of extra bits; and the shift. So
  every kind of distance is one formula with no branch on the kind, in 64-bit arithmetic so that a result of zero or
  less is not mistaken for a large distance.
- *The last four distances* are a ring of four in the slow state with an index (a field of the counters), so a push is
  one store.

**The copy,** by the distance:
- *16 or more* (nearly all): 16-byte block copies, the two ranges apart by construction. A copy longer than a round
  handles is continued by the next rounds of the loop, the length left kept in the command in hand; no library copy is
  called for any length. Probed: about 20 instructions a round of 32 bytes.
- *8 to 15:* the same by 8-byte blocks.
- *Under 8,* a source or target crossing the ring's end, or a distance that is zero, negative or beyond the window with
  no valid word: an event.
- *The fast path's test* (the distance at least 16 and no more than the position in the ring) cannot pass for a distance
  of zero or one that came out negative, so those reach the rare path with no instruction added to the common one.

**A dictionary word** is written by one call from inside the loop's function: its length worked out first from the
transform, the word then written straight into the ring by 8-byte blocks (the prefix, the base word, the suffix, each
from the exact end of the one before), with a byte-by-byte writer where the blocks would pass the ring's end. *(To
measure: against an event.)*

**The head.** The budget is tested and lowered (a field of the counters). The insert-and-copy symbol is looked up in
the current table (its name in the slow state), then what it stands for (5.7), then the two lengths' extra bits. Then:
- *the one output test:* the output position plus both lengths against the bound (5.5);
- *the literals' tests:* the insert length against the literal block's count (a field of the counters) and against the
  longest run the round's input cost covers (16).
If all pass, the literal block's count is lowered by the insert length, and the loop goes on: to the distance and copy
if there are no literals, to the literal rounds if there are. If one fails, the loop leaves *before the head*: the
handler reads the head again and deals with the command in pieces (below).

**The literals**
- *One a round* for the first literals of a run, each stored at once; *three a round with one block store* for a
  longer run, in running mode. Exact mode reads one a round.
- *The two bytes before* ride in the spare bits of the count of literals owed, read from the ring (and the guard) once,
  when a run starts.
- *The context:* a constant table for all four context modes gives a part for each of the two bytes; the two combined
  index the block type's row of table names (5.7); the name gives the table. *(To measure: against a table built for
  each block type that gives the name from the last byte directly.)*

**The counters, in one carried word:** the rounds left in the budget, the literal block's count, the distance block's
count, and the index of the last distances. A round lowers and tests its fields by arithmetic on the one word, with no
load or store of `buf` and no store site. (Probed: the compiler keeps the word on the stack and works on it there once
a command.) The insert-and-copy block's count is folded into the budget, as the smaller of the two.

**What a round tests:** the budget; the output's bound; the literals against their block and against the round's cost;
the distance block (explicit distances only); the copy's source. Five or six tests a command, none per literal, none
of the input.

**A round's largest input:** the head 63 bits, at most 16 literals 240, the distance 39: 342 bits, 43 bytes. The margin
of 5.4 is that and the 8 a refill may load beyond the last bit used: 64 bytes.

**Events, and a command in pieces.** The loop only ever runs pieces it has admitted whole. What it leaves for:
- *A block switch,* when a category's count is zero: the handler reads the type and the new length, checks the rules
  (5.10), and updates the slow state: the current table's name or row, and the counters.
- *A command that does not fit:* its head is read again by the handler, with the same reading function. Its literals
  are given to the loop as an allowance (what the literal block, the output's bound and the input ahead allow now),
  with a mark in the command in hand that more are owed; when the allowance is spent the loop leaves on that mark,
  which shares its test with the mark for a copy being continued, so the common path pays nothing for it. Its copy, if
  the bound cuts it, is cut by the handler, which copies what fits and keeps the rest in the slow state.
- *The meta-block's end,* a copy needing care, and a rejection.
When the loop leaves in the middle of a command, what the command still owes is in the slow state, and the loop is
entered again where it left.

**Exact mode's order,** element by element: the distance is read, then tested, then its push is stored and its copy
made; the head is read, then tested, and it stores nothing in `buf`; a literal is read, then tested, then stored. So
every store of a round comes after the test of the element that caused it.

**Four compiled copies** of the loop, and no more: the two modes, by whether the meta-block's literal contexts are all
trivial (then the loop has no context at all). Every other choice is a test inside them.

### 5.7 Headers and tables — proposed

**A prefix code's table**
- *Entries of 16 bits:* the code's length in the low 4 bits, and the symbol above. The stride between a code's entries
  is a power of two, so a symbol's entries are written by one strided fill.
- *A root of `R` bits,* where `R` is the code's longest length up to a cap. *(To measure: sized to the code like this,
  against a fixed width; and the cap. A sized root makes a table, its building and its cache follow the code, which
  matters most for a short stream; a fixed root saves four instructions on every lookup.)* A code of one symbol has one
  entry and `R = 0`, and reads no bits, with no special case.
- *Longer codes* go through a second level: a root entry marked as a pointer gives a sub-table's position and width.
  The mark needs no bit of its own: a root entry's length is at most `R`, so low 4 bits above `R` mean a pointer, the
  excess being the sub-table's width and the 12 bits above its place, in entries from the table's start. A sub-table's
  entries hold the code's whole length, so a lookup ends, at either level, at an entry whose low 4 bits are the bits to
  consume.
- *A table is named by one 32-bit value,* its position in `buf` times 16 and its `R`, so that whatever selects a table
  delivers both in one load.

**What symbols stand for**
- *A literal* is its symbol: one load gives the output byte.
- *An insert-and-copy symbol:* one constant table of 704 entries of 8 bytes (both lengths' bases and extra-bit counts,
  whether the distance is the last one, the distance's context), the same for every stream, kept with the program's
  constants. Nothing is built or copied for it. Two loads, one after the other.
- *A distance symbol:* a table of at most 520 entries of 8 bytes in the buffer's front (5.2), rebuilt only when a
  header's NPOSTFIX or NDIRECT differ from the last header's. Two loads.
- *(To measure: what a symbol stands for put in the prefix table's own entries, 8 bytes each, so that one load gives
  everything; it takes a load off the chain once a command, for tables four times the size built for every code, and
  needs a strided fill of 8-byte values, which the rule for new primitives allows.)*

**The header's stretches,** each a phase loop or a handler, with everything learnt so far in the slow state:
1. the block types of each category, and for more than one type its two small prefix codes and first length;
2. the parameters and the context modes;
3. the two context maps;
4. the prefix codes: literal, insert-and-copy, distance;
5. finishing: what the command loop reads is put in its final form, and the phase becomes the commands.
Every read is an element in the two modes; the long loops (a code's lengths, a map's values) run on a budget, a round
being at most 8 bits here. A header may be left and entered again between any two elements, over any number of calls.

**Reading one prefix code**
- *Simple:* the symbols are read and given lengths by their number (one: 0; two: 1, 1; three: 1, 2, 2; four: 2, 2, 2,
  2 or 1, 2, 3, 3). They may come in any order, and codes are assigned in symbol order, so the up to four symbols are
  put in order first and the table is built by the builder below.
- *By code lengths.* First the code-length code's own lengths, at most 18 of at most 4 bits each: two elements. Its
  32-entry decoding table is assembled in registers and written by four 8-byte stores. Then the symbols' lengths, one a
  round, at most 7 rounds a refill:
  - the code-length symbol is looked up;
  - a length from 1 to 15 adds the symbol to the end of *that length's list*: one store to link it after the list's
    last symbol, one to make it the last. The 15 lists are threaded through one array indexed by symbol. Symbols arrive
    in increasing order, so each list is in symbol order. Each length has one word: the place where its next symbol is
    to be linked (at first the list's head, so an empty list is no special case) and the count of its symbols, which
    the builder needs for the widths of sub-tables; one load and the two stores keep both;
  - the repeat codes read their extra bits and add a run of symbols to a list, or skip ahead for a run of zeros: a
    symbol that does not occur costs no store and no round;
  - the running sum that says when the code is complete is kept in a register and ends the loop.

**Building one table:** one walk through the lists, shortest length first, with no sorting and no second pass.
- The walk visits the symbols in exactly the order of their codes. So no code is looked up: it is a counter stepped
  once a symbol. The bits arrive low bit first, so the first slot to write is the code reversed: the counter is kept in
  8 bits with the code's first bit highest (its step halves from one length to the next), and a constant table of 256
  reversed bytes turns it into the slot. One add and one load a symbol, with no loop and no branch. This is why the
  root's cap is 8: a wider root needs a wider reversal.
- *A symbol whose length is within the root* is written to every root slot whose low bits are its code, by one strided
  fill.
- *Symbols with longer codes* come last in the walk, already in order. A code with a root of 8 bits usually has some,
  so this is an ordinary case. When the walk reaches a root slot not yet given a sub-table, the sub-table's width is
  worked out from the symbols remaining at this length and after, so that it is exactly as wide as its codes need; the
  root slot is pointed at it and its symbols written into it as into a root.

**The context maps.** A map's values are read like a code's lengths, into the working area; the inverse move-to-front
is done in place on a 256-byte list. The maps are not what the command loop reads. When the codes are built, each
literal block type gets a row of 64 table names (the map composed with the tables' names) and is marked trivial if its
64 names are one; each distance block type gets a row of 4.

**What a header leaves** in the slow state: for each category, the count of block types, the current type and the two
switching codes' names; the current insert-and-copy table's name; the current literal row, and whether every row is
trivial; the current distance row; the output's bound; the counters; and three empty sets of block types seen.

**The working area.** The lists (the links, each length's word and head) are in the buffer's front (5.2), reused by
every code of the header. Where the rest goes (the code-length table, a map's values, the move-to-front list) is
settled with the header (section 9, step 4).

**Costs, in outline.** Reading a code: a lookup and two stores a used symbol. Building it: a load, a step of the code
and one strided fill a used symbol, each slot written once. Nothing in a header is in proportion to an alphabet's size
except the constant table that is never built (principle 11).

### 5.8 The stream layer — proposed

**The window size and a meta-block's start are each one element,** read straight through from one refill with no loop.

**What a meta-block's start does**
- *An empty last block:* the phase becomes the end.
- *Metadata:* its rules are checked (5.10) and the phase becomes metadata with a count of bytes to pass.
- *Uncompressed:* the bits to the byte boundary are checked to be zero, the ring's part is extended for the length
  (5.2), and the phase becomes uncompressed data with a count of bytes to copy.
- *Compressed:* the ring's part is extended for the length, the output's bound is set, and the phase becomes the header.
The demand the stream now makes on memory is known here, before it is met, and is compared with the limit (5.9).

**Metadata** costs nothing in proportion to its length: the driver lowers the count by the bytes of it in the staging
area and then by bytes of the caller's chunk, counted as used and never copied.

**Uncompressed data** is copied by the driver: first what is in the staging area, by a copy within `buf`; then
straight from the caller's chunk into the ring, one copy for as much as the input has, the output's bound allows and
the ring has before its end.

**The end.** After the last meta-block the bits to the byte boundary must be zero, and no byte may follow: a byte
arriving in this phase rejects the stream at once; the end signalled with nothing more, and every output byte handed
over, is done; a call that brings nothing and does not signal the end returns "needs input".

### 5.9 Memory and the limit — proposed

- *What is allocated:* `buf`, once (5.2); and each call's reply.
- *The demand* at any point is the front, the ring's part as far as the meta-blocks so far have declared (5.2), the room
  the current header's tables take, and nothing else. It rises only at a meta-block's start and while a header declares
  its codes.
- *The limit* is compared with the demand before the demand is met: at a meta-block's start, before the ring's part is
  extended, and in a header, before a table's room is taken. When the demand exceeds it the phase becomes the memory
  limit and every later call returns that.
- *At the start:* a limit below the front's size is reported by the start itself.
- *The limit changes nothing else:* it is read only in those comparisons.

### 5.10 Rejection — proposed

Every way the specification rejects a stream, read off its definitions, with where the decoder finds it. A stream that
ends before a reader is finished is rejected at the signalled end (5.4).

**The stream's frame** (the stream layer)
- The window-size field's one unused pattern.
- After the last meta-block: a non-zero bit before the next byte boundary, or any byte after it.

**A meta-block's start** (the stream layer)
- A length of more than 4 nibbles whose top nibble is zero.
- Metadata: the reserved bit set; a skip length of more than one byte whose top byte is zero; a non-zero bit before the
  byte boundary.
- Uncompressed data: a non-zero bit before the byte boundary.

**A prefix code** (the header)
- Simple form: a symbol outside the alphabet; a symbol given twice.
- The code-length code: its lengths over-subscribe it; or all 18 are read and it is neither complete nor a single
  symbol.
- The symbols' lengths: a run that passes the alphabet's end; the lengths over-subscribe the code; the alphabet is used
  up before the code is complete.

**A context map** (the header)
- A run of zeros that passes the map's end.
- A code that the map never names.

**The commands** (the command loop's tests and its handlers)
- A block switch that names the block type already current.
- A block count that runs out in a category with one block type. (No meta-block can reach it; the decoder holds the
  count as the specification does.)
- Literals that pass the meta-block's end.
- A copy or a dictionary word that passes the meta-block's end.
- One of the last distances with its offset coming to zero or less.
- A dictionary reference with a copy length under 4 or over 24, or whose word number names no transform.

**A meta-block's end** (its handler)
- A block type that was declared and never used, in any category.

**What this asks of the design**
- *The output's bound has two meanings.* Where the one comparison fails, the handler tells the caller's space and the
  ring's end, which pause, from the meta-block's end, which ends the meta-block or rejects.
- *Which block types occurred* is three sets of up to 256 members in the slow state, added to at block switches.
- *Which codes a map names* is found when the map's rows are built.
- *Finality:* a rejection sets the phase, and every later call returns it at once.
- *Timeliness* (contract 3): a check may be put off to the next test a loop makes anyway, never past the loop's leaving;
  the fixed number of bytes is then a round's largest input.

## 6. The invariant ledger

The facts the fast code assumes. Each is to be stated in the code where it is used, and is what the main proof must
establish of every state a caller can reach.

| the fact | where it is used |
|---|---|
| `buf` is held once at every call | every store is in place (4) |
| the slow state names a phase and a reason at every return to the driver; what a loop saved is what it, or the handler for its reason, loads | 5.1 |
| the regions of `buf` lie in the order of 5.2 and do not overlap; every store of a loop falls in the ring's part or the slow state | 5.2 |
| during a meta-block the tables start at or beyond the ring's end for that meta-block plus the slack | 5.2 |
| the array is extended only within its room | 5.2 |
| every refill has 8 readable bytes at `bitpos / 8`; an element consumes at most 56 bits (a head, 63, with its second refill) | 5.4 |
| in running mode, at every renewal of the budget, the real input ahead covers the budget's rounds at a round's largest cost | 5.4, 5.6 |
| zeros follow the last real byte in the staging area for at least the margin | 5.4 |
| in exact mode no element takes effect unless every bit it consumed was real | 5.4 |
| `handed ≤ opos ≤` the bound `≤` the ring's end | 5.5 |
| the bytes from the ring's start to `opos`, and after a wrap those from `opos + 16` to the ring's end, are the stream's last output in order | 5.5 |
| the guard holds the two bytes before the ring's first: zeros, or after a wrap the ring's last two | 5.5 |
| a block write runs at most 15 bytes past its end, in the slack | 5.5, 5.6 |
| a distance that passes the fast path's test is a valid distance of at least 16 within the bytes produced | 5.6 |
| a command admitted by the head fits the bound, its literal block and the round's input cost | 5.6 |
| the counters' fields hold the budget, the two block counts and the index, each within its width | 5.6 |
| a name's position and width describe a table that has been built; every slot of a table is written exactly once | 5.7 |
| the working area and every table lie in the tables' region | 5.7 |
| at the start of metadata, of uncompressed data and of the end, `bitpos` is at a byte boundary | 5.8 |
| the demand has been compared with the limit before any byte it calls for is written | 5.9 |

## 7. Proof plan

A sketch, to be filled in as the design settles.

- **Proved as the code is written:** bounds for unchecked access, arithmetic side conditions, sizes preserved by
  stores, termination of small loops. A bound that follows from what is visible at the point of use is proved there. A
  bound that follows from something established elsewhere is taken as a hypothesis by the function that needs it, so
  that the code states what it relies on.
- **Owed while it is a prototype:** a loop cannot take such a hypothesis, since it would have to supply it again for
  its next round, and that is the invariant's preservation proof. So a fact that rests on the whole invariant (section
  6) is written `owed` at the point of use: one theorem, `owed {P : Prop} : P`, the decoder's only `sorry`, in a module
  of its own. The signature of what uses it states exactly what is owed. Proofs are erased when the code is compiled,
  so paying one changes nothing that runs: what is measured is what is later proved. The uses are counted, and the
  decoder is proved when none is left.
- **Deferred until a part is settled:** what a self-contained primitive leaves in memory (a table builder, a word
  writer, a copy).
- **Deferred until the design is settled:** the specification's reading of a prefix (2.2); the relation between a
  running decoder's state and that reading; the induction over every state a caller can reach; and from them the
  contract.
- **Method:** one relation between the decoder's state and the reading of the bytes received, kept by every step; a
  measure for progress; a size invariant for memory.
- **Where the proofs will be hardest:** pausing (5.4), since the contract speaks of every way of delivering the input;
  the one buffer, since every store must be shown to leave the other regions alone (5.2); and wherever the fast code's
  effect differs from the simple one's in bytes that do not matter (the slack).

## 8. To be measured

Choices that change time through how often a path runs or through the chain between symbols, which a count of
instructions does not show. For these the design does not guess: the code is written once over the part in question,
passed in as the modes are (section 4), so that each alternative is a compiled loop from the one definition, and they
are raced on real streams.

**The command loop**
1. The bit reader: a word recomputed from the position at each refill (fewer carried values, fewer instructions),
   against a buffer shifted in place with a count (a shorter chain between symbols).
2. A dictionary word as a call inside the loop, against an event.
3. What an insert-and-copy or distance symbol stands for: a second table (two loads), against the prefix table's own
   entries (one load, larger tables).
4. The literal's context: looked up and combined on the chain, against a table for each block type.
5. A table's root: sized to the code, against a fixed width; and its cap.
6. Where the constant tables live: with the program's constants, against copied into the buffer's front.

**The header**
7. The instructions a used symbol in reading and in building.
8. Two code-length symbols to a lookup.
9. The inverse move-to-front on maps of realistic size.

**The whole**
10. What the stack traffic that remains costs in time.
11. Filling the ring's new part when a meta-block starts; copying input into the staging area; the allocator with other
    allocations between a stream's.
12. The fixed cost of a call that does almost nothing.
13. How often each kind of event falls.

### 8.1 What has been measured (2026-11-10, step 3)

Measured on the web corpus with the loop alone (`fdrun`: headers by the specification's reader, the rest by simple
means), by exact instructions (SDE) and by cycles and mispredicts (VTune). For scale, a pass of the corpus costs
Google's decoder 54.6 M cycles and 111 M instructions in its command phase, and the earlier decoder 64.5 M and 148 M.

**The loop is bound by its dependency chains, not by its instruction count.** The first cut ran 118 M instructions a
pass, near Google's, with fewer mispredicts (3.9 a thousand instructions against 8.2), and still took 57.9 M cycles.
Cutting its instructions by 16% (jquery at quality 11) moved its time by 4%. Shortening the chains with the
instruction count unchanged moved it by 15 to 19%. So each alternative below is judged first by the chain it leaves
between one element and the next.

| item | result | status |
|---|---|---|
| 1. the bit reader | Recomputed from the position, the word's load is on the chain between every two elements (about 14 cycles an element). A word shifted in place would cost two more carried values. Taken instead: the position is carried as a byte and an offset in it, and the word is loaded from the byte where the *previous* element began, so its address never waits for that element's length. An element's symbol always fits (the offset stays under 49); its extra bits are taken from a fresh word on a branch that is almost never taken. One more carried value (seven). | decided |
| 3. what a symbol stands for | In the table's own entry (8 bytes for insert-and-copy and distance codes): one load gives the code's length, the bits the whole element consumes, and the lengths' or the distance's bases and extra-bit counts. The second table's load was on the chain (about 25 cycles from a head or a distance to the next element, now about 10). The builder makes an entry by one add: what the symbol stands for, read from a table by symbol, plus the code's length in its two low bytes. | decided |
| 4. the literal's context | A table for each literal block type, of 2048 table positions indexed by the last byte and the class of the byte before it. The last byte is the literal just read, so the next literal's table is one load from it (the chain from one literal to the next: about 22 cycles before, about 14 now). The class of a byte is ready a literal ahead. Its cost: 8 KB a literal block type, filled when the header is read. | decided; the cost for streams with many block types to be looked at with the header |
| 5. a table's root | Literal tables have a root of 8 bits whatever the code, so the index does not wait for the table's name. Other tables keep a root sized to the code: their names are ready long before they are used, and a name carries the root's mask, not its width. | decided |
| 6. where the constant tables live | Copied into the buffer's front: read at a constant place in `buf`, with no pointer of their own to load. | decided |
| 2. a dictionary word as a call | Built as a call from inside the loop; not yet raced against an event. It costs 1 M cycles a pass (2% of the loop), at 1.4 instructions a cycle: the dictionary is cold. | to measure |

**Two more, from the same day**

- *More than one literal a round:* two literals from one word, stored together, where two or more remain. It saved
  instructions and no time (9.81 ms a pass against 9.77): a literal is bound by the chain to the next literal, which a
  pair does not shorten. Not taken. Three a round (5.6) has not been tried and is not expected to differ.
- *What is carried from one literal to the next:* it was packed in one word with the count of literals left, and
  packed and unpacked on the chain. Now the count is a field of the command word, and the word that was carried is
  the offset of the next literal's table position itself: one shift and one or from the literal just read. On the
  streams with literal contexts this took 6 to 10% off the loop (jquery at quality 11: 189 µs to 170 µs).

**Where the loop stands, measured** (VTune, 400 mixed passes: every page decoded once a pass, among the others, as
the benchmarks time the decoders): 51.5 M cycles and 123 M instructions a pass in the loop, 584,000 mispredicts; with
the word writer (1.3 M cycles) and the loop's exits (0.5 M), 53.2 M cycles. Google's command phase, which includes
its dictionary words, its copies and its handing out of output, is 54.6 M; the earlier decoder's is 64.5 M. So the
loop is level with Google's command phase (2 to 3% under, which is inside what this harness leaves out) and 17% under
the earlier decoder's. What the harness leaves out of the figure: handing output to the caller, staging input, and
the few dozen to few hundred commands a stream that it does itself. It is not a number to quote.

- *A correction.* The figures first recorded here (49.1 M cycles, 482,000 mispredicts, "10% under Google") were taken
  with each page decoded 400 times in a row and counted the loop's own function alone. Repeating a page keeps the
  caches warm and lets the branch predictor learn the stream: mixed passes cost the loop 5% more cycles and 21% more
  mispredicts, and small pages most (a 74 KB page: 82 µs repeated, 98 µs mixed). `fdrun` now runs mixed passes and
  reports medians; `--repeat` gives the old behaviour as a diagnostic. The comparisons between alternatives made
  earlier on this page were each made within one setup, so their direction stands; their sizes are for a repeated
  page.

- *By quality:* at quality 11, where literals have contexts, the loop alone takes 0.66 to 0.88 of the time of Google's
  whole decode of the same page; at quality 5, where they have none, 0.93 to 1.02. Google's weak point is its literal
  context chain; without it the two loops are close.
- *What binds it now:* mispredicts, about a quarter of its cycles (stalled cycles are 23% of all), though it has about
  two thirds as many as Google's; and the rest at about 3 instructions a cycle. Cache misses are not it: cycles stalled on a
  first-level miss are under 2%.

**Where the mispredicts are** (the same collection's samples, by the block they land in; they smear forward some
instructions, so the shares are approximate; the loop compiled for literal contexts):
- *the test for literals left,* about half: 36% where another literal was expected and there was none, 18% the other
  way. It follows the data, and Google's loop has the same test. Decoding one literal always and discarding it would
  put a literal's lookup on the chain of every command that has none: not tried;
- *the insert-and-copy lookup's second level,* about 12%. That alphabet has 704 symbols, and something like 40% of
  heads go on to a sub-table;
- *the rest,* spread thin: the copy's length (16 or fewer, 32 or fewer), whether a distance is a plain copy, the
  distance lookup's second level (about 4% of distances, well predicted).

**A wider root for insert-and-copy tables: measured, not taken.** With a root of 10 bits nearly every head would end
in one load with no branch. The loop got slower: 9.69 ms a pass with 8 bits, 9.91 with 10, 10.14 with 11. The tables
are 8 bytes an entry, so 8 KB and 16 KB against 2 KB, and what they cost in the first-level cache is more than the
branch and the second load cost. The cap stays 8 for every table.

**The loop's design is provisionally final** (owner, 2026-11-10): what section 5.6 and the items above say, as built
in step 3. It is reopened only by what the whole decoder's measurement shows.

**The loop's stores, looked at again** (2026-11-10, after the header showed what the call behind a store can cost,
9.2). In the loop's generated code (485 instructions, compiled with contexts) a literal's round is about 37
instructions and a command's head about 75, with no value saved to the stack in either; a distance saves one value,
once a command; a copy none. The seven carried values fit in the registers a call keeps, so the test before a store
costs the loop a compare and a predicted branch and nothing else: about six instructions of two hundred a command,
none on a chain. There is nothing to take there.

- *Tried and not kept:* joining the literal's byte to the context row's position by one add, with the row and the
  class combined first, so that the table position's address needs no further addition after the literal. It took
  two additions off the chain through the literal and put a subtraction on the chain through the class: the loop was
  1.5% slower (10.44 ms a pass against 10.28).

**A cost these choices move to the header, not yet measured.** Three of them make a meta-block's header dearer, and
the loop's time does not show it:
- *the context tables* (item 4): 2048 entries a literal block type that has contexts. Filled one entry at a time
  that is about 8,000 instructions a block type; filled by rows (in the UTF-8 mode the four entries of a last byte are
  four neighbours of the map's row), about 1,000. Against the loop it is under 1% of a pass. Against a small page it
  is not nothing: one block type filled the slow way is a few percent of Google's whole decode of a 5 KB page;
- *the wide entries* (item 3): the same number of stores as narrow ones, four times the bytes written and kept in the
  first-level cache;
- *the fixed root of literal tables* (item 5): up to 256 stores for a code that needs fewer.
What is measured so far: building every table of the corpus (the builder alone, with the wide entries and the fixed
roots, without reading the codes or filling the context tables) costs 1.3 M cycles and 4.7 M instructions a pass,
under 3% of the loop. These three choices stay provisional until the header is built (step 4) and the small pages are
measured whole; if a small page pays more than it gains, the choice is made per meta-block (a meta-block decides
once, when its header is read, which loop it runs).

**A lesson for the code:** a loop is specialised on a function passed as an argument, not on a structure that holds
functions (section 4). Passing the three functions that find a literal's table as one structure compiled a single
loop that called them through closures and ran at half the speed.

## 9. Build order

Each step usable by the next, with something to measure as early as possible.

1. The primitives, the buffer's layout and the slow state's map.
2. The bit reader and the prefix-code table with its builder.
3. The command loop on a header built by simple means, in running mode: the first thing to race (section 8, 1 to 6).
   While the loop is being raced, anything may be owed (section 7), so that an alternative costs no proof. Before step
   4 starts, with the loop's design final, every owed fact that is small and local is proved in place: a loop's
   termination, a counter within its range, a size a store keeps. Only what rests on the whole invariant stays owed
   (owner, 2026-11-10).
4. The header, read and built as designed.
5. The driver, the staging area and exact mode: pausing for input and for output.
6. The stream layer: framing, uncompressed data, metadata, the end.
7. The handlers for every event, and rejection.
8. The memory limit.
Then the whole decoder is measured, and only then proved.

### 9.1 Step 4, the header: how it is to be built — built (9.2)

The header of 5.7 as a machine that can stop between any two elements, in running mode first (exact mode comes with
the driver, step 5). Written before the code, to be corrected by it.

**One element a call, two loops.** The header's place is a number in the slow state (`hphase`). `headerStep` reads
that number and does one thing: reads one element (a field of a few bits, a symbol with its extra bits), stores what
it learnt in the slow state, sets the next place, and returns `buf`. The two long stretches, a code's symbol lengths
and a context map's values, are loops of their own inside it that run on a budget of rounds (a round at most 8 bits
there) and leave when it is spent, their few values saved. The caller (the harness now, the driver later) makes sure
the margin of real input is ahead before each call. An element costs some tens of instructions of dispatch; a header
has some tens to a few hundred elements outside the two loops.

**Reading a prefix code is a sub-machine** used from six places (each category's two switching codes, the context
maps' codes, and the three kinds of code). It is entered with the alphabet's size, the kind of table to build
(narrow or wide, its source of what symbols stand for, its least root) and where to put the table's name, and with
the place to go back to. Its own places: the first two bits; for a simple code, the count of symbols, each symbol,
the shape bit for four; for a code by lengths, the code-length code's lengths (one element each, at most 5 bits),
then the lengths' loop. It ends by building the table (5.7) or, for one symbol, the one-entry table.

**The order of places** is the format's (checked against the specification's reader): for each of the three
categories, the count of block types and, above one, its two codes and first count; the two distance parameters; a
context mode for each literal block type; the literal map (the count of codes, and above one the run-length limit, the
map's code, the values, the move-to-front flag); the distance map likewise; the literal codes; the insert-and-copy
codes; the distance codes; then finishing.

**Where a header's things go,** in the tables' region (5.2), in this order: the header's working arrays (the two maps
as bytes, one a context; the list of each code's table name as it is built), then the tables, then the rows the
command loop reads (a context table for each literal block type that has contexts; a row of four names for each
distance block type). The slow state holds each category's count of types, current and previous type, its two
codes' names and its count; the distance parameters; the context modes go with the maps.

**Finishing** composes the maps with the names: each literal block type is marked trivial if its 64 map values are
one, and the meta-block trivial if all are; where it is not, each type's context table is filled (by rows of the
map, 8.1); each distance block type's row of four names is written; the distance symbols' table is rebuilt if the
two parameters changed (it is needed before the distance codes' tables are built, so this part comes there); the
command loop's slots are set (the current tables, the counters, the bound) and the phase becomes the commands.

**Rejections found here** are those of 5.10 for a prefix code and a context map; each sets the phase to rejected.

**How it is checked:** `fdrun` reads each header both ways, by the specification's reader as now and by this
machine, and compares what they leave: every table by decoding with it, the maps, the counts and the parameters; and
then decodes the stream with the tables this machine built.

### 9.2 Step 4 as built, and what it costs (2026-11-10)

Built as 9.1 says (`Header.lean`), in running mode, and checked as it says: on every stream of the web corpus and on
Brotli's own test streams that fit their window, each header as this machine reads it agrees with the
specification's reading (the counts, the parameters, the modes, both maps, every code's table by decoding every 15
bits of input, and the bit the header ends at), and the stream decodes to its original with the tables the machine
built. The rejections are written and have not been exercised: the harness has no invalid streams yet.

**Where it differs from 9.1**
- *Everything is taken from one moving position* (`Slot.tabNext`) as its size becomes known: working arrays and
  tables interleaved, not the arrays first. The move-to-front list and the set of codes a map names are scratch past
  that position (512 bytes the room must cover).
- *The code-length code's 18 lengths are a third loop,* which in running mode runs to its end in one call (72 bits
  at most, inside the margin). Its table was at first built by the general builder; it is now made directly (below).
- *A context table is filled only for the classes its mode can give:* 1 for the two modes that use the last
  byte alone, 4 for UTF-8, 8 for signed.
- *The slow state is 1,024 bytes,* for the header's slots, the three categories and the code-length code.

**The builder, rewritten for it.** The walk through the lists carried 14 values and cost about 65 instructions a
symbol, most of them stack traffic. It is now a tight loop for a run of symbols of one length within one table
(`tabRun`, compiled once for narrow entries and once for wide), with a new length and a new sub-table handled outside
it. The builder's instructions fell by a fifth on one page (jquery at quality 11); the tables are the same (checked against the
reference).

**What a header costs, measured** (VTune, 400 mixed passes of the corpus, cycles a pass). Google's headers cost
2.70 M and the earlier decoder's 8.57 M.

| | first cut | now |
|---|---|---|
| the whole header | 4.19 M | 3.16 M |
| the symbols' lengths | 1.36 M | 1.12 M |
| building tables | 1.49 M | 1.03 M |
| the code-length codes | 0.39 M and a share of the building | 0.29 M |
| finishing (the context tables, the rows, the slots) | 0.40 M | 0.17 M |
| the two maps | 0.34 M | 0.29 M |
| the rest | 0.2 M | 0.26 M |

So the header stands at 1.17 times Google's, 0.46 M cycles over it, which is under 1% of a whole decode; and the
standing of 8.1 (level with Google on the commands) does not yet hold for commands and headers together. About a
quarter of the header's cycles are mispredicts (48,000 a pass). In instructions it is 7.8 M a pass, from 10.0 M.

**What was changed after the first cut, each from this document's own guidance that the first cut had not followed**
- *The lengths' loop keeps its word in a register* (5.7: at most 7 rounds a refill). Loading the word again every
  round put a load on the chain from one symbol to the next: about 14 cycles a round at 2 instructions a cycle. It
  also reads the code-length symbol from a table of 32 one-byte entries at a constant place, and makes one or two
  tests a round: its budget is never more than the symbols the alphabet has left.
- *The context tables are filled by rows* (8.1). The table is laid out by the last byte first, 32 bytes a last byte
  (the loop's offset is `byte << 5 | class << 2`, the same shift and or as before), so a last byte's contexts are
  copied from the block type's row of 64 as one block of 16 or 32 bytes. The loop was measured again with this
  layout: the loop compiled with contexts took 25.37 M cycles a pass against 25.64 M before, and the loop without
  contexts, which the change does not touch, 25.22 M against 25.55 M; the ratio of the two moved by a quarter of a
  percent, inside the run's noise. The layout stays. If a later measurement shows the wider UTF-8 table (8 KB in
  place of 4) costing the loop, UTF-8 goes back to 16 bytes a last byte, with the shift read for the block type.
- *The code-length code's table is assembled in four words and written by four stores* (5.7), from the counts of
  each length, with nothing that branches on the data: a symbol's entries are a fixed pattern of the 32 shifted to
  its code and spread to bytes. A first version filled the table by short loops whose counts follow the data; they
  mispredicted 10,000 times a pass and it cost more than the general builder had.
- *A context map is read like the lengths* (5.7), its word in a register; the check that it names every code is a
  set of bits in a register for a map of at most 64 codes; and the move-to-front list and the marks are set up only
  as far as the map's codes go (principle 11).
- *A zero length is added to the list of length 0,* which nothing walks, so the lengths' loop has no branch between
  a zero length and another. No measurable gain; kept as the simpler loop.

- *Sub-tables are filled a length at a time, not a run at a time* (after the table above was taken). The code
  counter beyond the root is kept in 16 bits, its high byte the root slot and its low byte the code within the
  sub-table; the low byte is zero exactly when a new root slot begins, so one loop takes all of a length's symbols
  and starts each sub-table in passing (`subRun`). Before, each run of the two or three symbols a sub-table holds of
  one length was a call of its own. By the harness's clock the headers went from 0.87 ms a pass to 0.86.
- *Tried and not kept:* one plain store in place of the strided fill where a symbol has a single slot (no change).

- *The code-length code's table, made a length at a time* (this replaces the two forms above). Its 18 lengths are
  gathered in a register while they are read, 3 bits each, and nothing is stored. Codes go by length and then by
  symbol, so one counter runs through them; the symbols of a length are found by one comparison of the whole word and
  walked as a mask, so a symbol with no length costs nothing; and before a length's symbols are stored the table's
  first half is copied onto its second by one load and one store, which makes every shorter symbol's copies with
  nothing emptied, tested or spread. The five lengths are five small loops, so what a length fixes is a constant in
  its loop. Set beside Google's on one page (jquery at quality 11): 268 instructions a table against Google's 238,
  from 1,230 for the form assembled in four words. It has up to five loop exits a table that follow the data, so it
  was measured against the form with none: 154,000 cycles a pass and 2,800 mispredicts, against 290,000 and 1,000.
  The walk stays.
- *The reversed bytes and the mask-to-symbol table are read from the buffer's front* (8.1, item 6), not through a
  pointer loaded for each symbol: for the code-length table and for both of the builder's loops.
- *Tried and not kept:* the lengths' loop with its end read from the slow state and its refill marked by a bit in
  the word itself (two fewer values carried than the form kept). No faster, and the word went to the stack, on the
  chain. The form kept carries its values in registers as it is (below).

**Beside Google's, part by part** (one page, jquery at quality 11, exact instructions; Google's from its own
functions): reading codes 57,000 against 47,100; code-length tables 4,800 against 4,300; building the other tables
52,000 against 48,800; context maps 7,500 against 6,100; context tables and finishing 12,200 against none; the
distance symbols' table 2,300 against none; in all 137,000 against 107,000 (272,000 at the first cut).

**The call behind every store: looked at twice, and shaped around** (owner, 2026-11-10). An early form of the
lengths' loop, with nine values changing from round to round, spent about 14 of 52 instructions a symbol saving
values to the stack and reloading them around its two stores: the test that the array is held once has a call
behind it (section 4), and a call does not keep half the registers. Two ways of taking the call's cost away were
looked at, and neither is taken; a third search found no other.

- *The copy behind a function declared `preserve_most`,* which saves the registers itself. Probed in C: no stack
  traffic. Decided against: it needs a C file in the library, which is a build step of its own, and the library
  takes on no build step beyond Lean's; and the compiler's documentation calls the feature experimental.
- *The copy reached through a small routine written in assembly inside the primitive's own text,* emitted once for
  each object file, which saves every register itself (found by an investigation asked to get the same effect with
  no C file and nothing experimental). It was built into the real modules in a copy and checked by a test that
  forces the copy. It is not taken: it would put some 35 lines of assembly, for one operating system and with no
  unwind information, into the trusted primitives; and on the code as it now stands it gains almost nothing, for
  the reason that follows.
- *Anything else at all, with assembly ruled out as well* (owner): a second, wider search, on the real generated
  code. Nothing was found, and the reason is of one piece. Taking the call away takes every such save away (the
  command loop's function goes from 38 stack operands to 19, the builder's main loop from 20 to 11), so the call is
  the cause. But the call cannot go: a store with the test left out, tried on an array held twice, wrote into the
  shared original. And nothing short of removing it helps. Telling the compiler the array is held once is ignored,
  and if heeded would delete the copy; true attributes on the runtime's copy function (cold, leaf) change where its
  code is put and not who saves the registers, and the output is the same byte for byte; attributes that would change
  that are false of the runtime; a slow path that leaves the loop needs a Lean function saying whether an array is
  held once, and there is no such function, since two equal arrays can differ in it; and nothing in this Lean (its
  linear mark, its borrow annotations, its own store functions) skips the test.
  What other languages do is hoist the test out of the loop in the compiler (Swift does). For Lean that exists as a
  proposal and a thesis, in no release; and it would work on Lean's own array operations, where it can see the test,
  not on a primitive whose test is inside its C. So the primitives that make this decoder fast are also what would
  put it out of such an optimisation's reach, unless Lean one day lets a primitive declare that it needs its array
  held once.

**Shaping is enough.** With the loops as they now are, the hot paths have no stack traffic from the call at all:
the lengths' loop is 41 instructions for a plain length, the command loop's literal round 39 (8.1), each with none
saved to the stack. What does it is what section 4 says: few values that change from round to round, so that they
fit in the registers a call keeps (a budget kept as an end for the index, not counted down; state packed in one
word; what only a rare path needs read from the slow state there); and few store sites. The compiler also drops the
second test of two stores in a row where it can see the first cannot have reached the array's own header (an index
it knows to be small). The loop of a context map's values was the one still shaped the old way, at 38 instructions
a value with 6 of them stack traffic; reshaped in the same manner (a position in the buffer in place of an index
and the map's place, an end in place of a budget, the run-length limit read where it is used) it is about 30 with 2.

So an earlier sentence of this section was wrong and is withdrawn: what separated this header's reading of codes
from Google's (57,000 instructions against 47,100 on the page above) was not registers saved around stores.

**What it was: the repeat codes.** Found by setting the two functions side by side, block by block with their
execution counts (the page has 663 plain lengths, 83 zero lengths, 83 repeats of the last length adding about 440
symbols, 51 runs of zeros). The loop for plain and zero lengths was already level with Google's: 41 instructions a
plain length against 37, about 29,500 against 29,300 in all. The repeats were not: about 15,000 against 11,600.
Each repeat of the last length called a function of its own to add its run of symbols to the list, a symbol at a
time, and the runs are short (five symbols on average), so the call cost more than the work. Now a run of up to five
is added in line: the first symbol linked after the list's last, the next four links written by one store (their
values are consecutive), and the list's word written once with its count up by the run. Longer runs, and one within
three symbols of the largest alphabet's end, go to a loop that writes four links a store. Reading codes is now
51,500 instructions on the page against Google's 47,100, and the header 133,000 against 107,000.

- *Tried and not kept:* 64 bytes of slack after the links, so that the one store needs no test near the alphabet's
  end. It moved every later part of the front by 64 bytes, and the command loop read 0.7% slower with nothing else
  changed (the loop's tables and the ring keep their place within a cache line, so this is some coarser alignment).
  The front's positions are a thing the loop is sensitive to: a change to them is measured on the loop.


**A caution on the comparison.** Google's 2.70 M was taken with the benchmark driver (input in network-sized
pieces, its decoder pausing inside headers); ours with `fdrun` (the whole input at hand, a fresh buffer a decode);
and the two decoders do not draw the line around "headers" alike. The figures show which parts are slow. How far the
header is from Google's is known only when both run under the same driver (step 5 on).

**What is left, and what it is**
- *The symbols' lengths* (1.12 M): a chain of about 8 cycles a symbol (the next symbol's place waits for this one's
  length through a load), and 18,000 mispredicts a pass, mostly on the repeat codes. Two symbols to a lookup
  (section 8, item 8) would shorten the chain, but needs a table of 256 pairs built for each of about 1,300
  code-length codes a pass; by estimate, not measurement, that costs more than it saves. Not taken.
- *Building* (1.03 M): spread thin, with no hot spot: about 14 cycles a symbol in the wide tables, in the walk
  through a linked list (a load a symbol, as in Google's builder, which keeps the same lists) and stores into table
  memory that is not in the cache. Wide entries are twice the bytes of Google's.
- The three choices of 8.1 that the header pays for stay: the context tables now cost 0.16 M a pass, and what they
  took off the loop is many times that.

### 9.3 Step 5, the driver, staging and exact mode: how it is to be built — built (9.4)

What 2.3, 2.4, 5.1, 5.4, 5.5 and 5.6 say of it, gathered, with what they leave open settled here. Written before the
code, to be corrected by it.

**What is built already disagrees with the design in four places,** and step 5 puts each right:
- the loop's budget is renewed outside the loop, by whoever called it; 5.4 says inside it, from the slow state, the
  loop leaving only when the input ahead is really short;
- the insert-and-copy block's count is kept by the harness; 5.6 folds it into the budget, as the smaller of the two;
- nothing has an exact mode;
- the code-length code's lengths are read to their end in one call; in exact mode that loop stops between elements.

**The mode is a function** (section 4): from the buffer and the bit position after an element to whether every bit
the element used was real (at or before `Slot.inEnd`). The running one answers yes without looking, so the running
copy of a loop carries nothing for it. A loop asks it after reading an element and before the element has any
effect, in the order of 5.6: a distance read, asked, then pushed and copied; a head read, asked (it stores nothing);
a literal read, asked, then stored. If the answer is no the loop leaves with its values as they were before the
element, for the reason "input".
- *The command loop* is compiled four times: the two modes, by whether literal contexts are trivial.
- *The header's three loops* (the code-length code's lengths, the symbols' lengths, a map's values) are compiled
  twice.
- *The header's single elements* have the test always, as 5.4 has it for the window size and a meta-block's start:
  each is read once, and one comparison each is not worth a second copy of every step.

**The budget, renewed inside the loop.** When the budget's field is zero at a command's head the loop calls a small
function that works out a new one from the slow state: the rounds the real input ahead covers at a round's largest
cost, and no more than the insert-and-copy block has commands left, which it lowers by what it grants. It leaves the
new counters in the slow state, and the loop goes on with them. Only when it can grant nothing does the loop leave:
for "input" if the input ahead is short, for the block switch if the block's count is spent. In exact mode the
budget counts the block's commands alone, since every element is tested.

**The driver** is the one function that holds the caller's two arrays. Each time round it reads the phase and the
reason and does one thing:
- *the header:* a step of it;
- *the commands:* the loop, in running mode while the margin of real input lies ahead, in exact mode when the chunk
  is used up and it does not;
- *a loop left for "input":* stage the next piece of the chunk if there is one; if there is none, go to exact mode;
  if it was already in exact mode, hand out what waits and return "needs input", or reject if the end was signalled;
- *a loop left because the bound stopped it:* if the bound was the caller's space, hand out what waits and return
  "needs output"; the meta-block's end and the ring's end are steps 6 and 7's;
- *done, rejected:* return it.

**Staging** (5.4): the unread tail is moved to the area's front, `bitpos` lowered by what was dropped, the next
piece of the chunk copied after it, and `Slot.inEnd` set to the last real bit. When the chunk is used up, zeros are
written after the last real byte for the margin. The count of bytes that were already in the area when the call
began is kept (`Slot.carried`), for the bytes a rejection reports used.

**Handing out** (5.5): one copy from the ring, from `handed` on, onto the end of the caller's buffer, of the bytes
waiting or as many as the space left allows; `handed` moves on. The bound is set before a loop is entered: the least
of the meta-block's end, the ring's end, and `handed` plus the space left plus one.

**A call** writes its parameters into the slow state (where its chunk stands, the space, the end flag), runs the
driver, and builds the reply: the state, the bytes used (5.4's rules), the caller's buffer, the status. The reply is
the only thing it allocates.

**What is not here yet, and how the driver stands in for it.** The stream's frame and the other kinds of meta-block
are step 6; the handlers (a block switch, a command that does not fit, a copy that needs care, a meta-block's end)
and the wrap are step 7 (the wrap needs the ring's size, which the stream layer sets). Until then the driver returns
to its caller at exactly those points, with a status that is not part of the interface and says which point it is;
the harness does that piece by simple means, as it does now, and calls again. Each such return is replaced by the
real thing in its step, and the status goes when the last is replaced.

**How it is checked:** `fdrun` decodes every stream through the driver, with the input delivered in pieces (16 KiB
pieces, the network mix, and pieces of a few bytes so that every element is met at a chunk's end) and with output
room given a little at a time, and compares the output with the original. Then the two things section 8 lists for
this step are measured: what copying the input into the staging area costs, and the fixed cost of a call.

### 9.4 Step 5 as built (2026-11-10)

Built as 9.3 says: the mode as a function through the command loop (four compiled copies) and the header's three
loops (two each); the budget renewed inside the loop from the slow state, with the insert-and-copy block's count
folded in; staging, handing out and the driver (`Driver.lean`), whose reply is a call's only allocation. Checked as
9.3 says: every stream of the web corpus, and Brotli's own test streams that fit their window, decoded through the
driver with the input in pieces of 16 KiB, 100, 7, 3 and 1 bytes and output room of 64 KiB, 100, 5, 3 and 1 bytes a
call, each compared with its original, and what was handed out compared as it came. Three deliveries are steps of
`check`.

**Where it differs from 9.3, and what building it showed**
- *The header's single elements are guarded where they are dispatched,* not each in its own step: while 64 real bits
  lie ahead a step is taken as it is (no single element of a header is longer than 39 bits); in a chunk's last bits
  the element's own length is worked out first and the step taken only if all of it is real.
- *The header's loops choose their own mode* by what lies ahead when they are entered: the running copy while the
  input covers its rounds, the exact copy for the last bits. The driver chooses only the command loop's.
- *Running mode is chosen at every entry, by what is ahead then.* A first form went to exact mode only after the loop
  had left for want of input, and entered it in running mode at the start of each call. A loop taken up in the
  middle of a command (literals owed, a distance to read) reads on without a test, so with small pieces it read bits
  that were not there. Now the driver looks before it enters: if less than the margin and a refill's 8 bytes lie
  ahead it stages more when the chunk has more, and runs the loop in exact mode when it has none. This is 5.4's
  "running, while a margin of real input lies ahead", which the first form did not keep.
- *At the bound there may be no head to read.* At a meta-block's end the loop looks for the next command's head,
  and in exact mode at the stream's end there are no bits for one: that is the bound's event, not a want of input,
  and the loop says so (in exact mode only; in running mode the bound's own test catches it, as before).
- *The bytes a rejection reports used* (5.4, `Slot.carried`) are not worked out yet: the driver reports the bytes
  staged. To be done with rejection, step 7.

**What it costs** (the harness's clock, mixed passes; headers, commands, staging and handing out together):
10.98 ms a pass with the whole input given at once and room for all the output; 11.48 ms in 16 KiB pieces with
64 KiB of room a call. Before the driver, the headers and the loop came to 11.05 ms by the same clock, so the driver
and the budget's renewal cost nothing that shows (the loop now returns to its caller a quarter as often); and
delivering the input in pieces and handing the output out, 9 MB of it a pass, costs about 0.5 ms, 4.5%. Section 8's
two measurements for this step (staging, and a call that does almost nothing) are to be taken by function once the
stream layer lets a whole stream go through the driver without the harness.

**Each departure from the design measured both ways** (owner, 2026-11-10: a departure may be an improvement or
not, and only measuring says which). By the harness's clock, mixed passes, the least of three to five runs; pieces
of 16 KiB, of 1,460 bytes (a network segment), of 64 bytes and of 1 byte, the last two to show what happens at a
chunk's end and what a call costs. Runs of the same build differ by up to about 0.5% at the two larger sizes.

| the choice | as built | the other way | result |
|---|---|---|---|
| a call's parameters: carried as the driver's arguments, or written into the slow state (5.1) | arguments | the slow state: the same at 16 KiB, 5.7% slower at 1 byte a call | arguments stay; 5.1's wording is departed from, for a call's fixed cost |
| zeros after the staged bytes: at every staging, or only when the chunk is used up (5.4) | every staging | only at the chunk's end: the same at 16 KiB, about 6% slower at 64 bytes and at 1 byte (repeated; not explained) | every staging stays |
| a header's single elements: guarded where they are dispatched, with the element's length worked out apart in a chunk's last bits, or tested inside each step after it is read (5.4) | the guard | inside each step: 0.5% slower at 16 KiB and at 1,460 bytes, 3 to 4% slower at 64 bytes and 1 byte | the guard stays. Its cost is the proof's: two pieces of code must agree on each element's length |
| the budget's renewal: a call from inside the loop, the same in line, or the loop leaving for the driver to renew it (5.1, 5.4) | a call | in line: the loop grows from 487 instructions to 552, and 0.2 to 0.3% slower. The driver: 0.8% slower at 16 KiB, 2.9% at 1,460 bytes | the call stays, a second call in a loop that 5.1 allows one |

**Two more, looked at with them**
- *The header's input is made up first,* as the command loop's is: where less than the margin lies ahead and the
  chunk has more, the driver stages before it takes a step. Before, the header read the last bits of each staged
  piece an element at a time and staged only when one would not fit. 0.2 to 0.3% faster at the two realistic sizes,
  which is inside the noise; kept as the design's shape.
- *The staging piece's size,* within the area as it is: pieces of at most 1,024 bytes cost 2.7% more than the
  4,032 the area gives, and of 2,048 bytes 0.6% more. A larger area was not tried: it moves the front, which the
  command loop is sensitive to (9.2), so it is a question for the whole decoder's measurement.
- *A call that does almost nothing:* with the input a byte a call and room for a byte, 9.8 million calls a pass,
  the decode takes 155.7 ms against 11.2: about 15 ns a call, the harness's own loop and the reply's allocation
  included.

**Due diligence before the step was signed off** (2026-11-10): what had gone untested, tested.
- *What a call promises, checked at every return* (2.4): it adds no more than the room it was given; "needs output"
  comes with the room full; "needs input" comes with the chunk all used and nothing produced left waiting. These
  hold on every stream under every delivery, the network mix of piece sizes now among them.
- *Streams cut short.* Each stream of the corpus cut at 40 places and given to the decoder twice: with the end
  signalled it must be rejected; without, it must ask for input, having handed out exactly what the proved decoder
  (`Brotli/Decoder/`) hands out for the same bytes, which is what promptness means (the weaker check, that nothing
  produced is left waiting, would pass a decoder that stopped an element early). Of 4,160 cases 1,985 were rejected
  as they should be, 1,985 asked for input with the proved decoder's output to the byte, and 190 fell where the
  harness still does the reading itself and are not judged; none was wrong. The same with small pieces and small
  room, and with the network mix. Until this, nothing but whole valid streams had been through the new decoder.
- *Not yet tested, and why:* streams that are corrupt and not merely cut short (the header's rejections have still
  never run), which wait for the handlers and rejection of step 7 so that the whole verdict can be compared; and the
  one test stream whose output passes its window, which waits for the wrap.

**What is known to be slack or unmeasured, carried forward**
- *Every byte of input is copied once,* into the staging area; Google's decoder reads its input where the caller
  left it. A first estimate, by making the copy twice and timing the difference, is 1 to 2% of a decode; the clock
  varied by more than that between sittings, so it is to be measured by function with the whole decoder (section 8,
  item 11).
- *What the harness does for the decoder is outside its time:* on one page (jquery at quality 11) the loop goes
  back to the harness 121 times, for 75 copies that need care, 40 commands that do not fit and 6 block switches.
  These are step 7's handlers, and their cost will be the decoder's.
- *The header* stood at 3.16 M cycles a pass against Google's 2.70 M when last measured by cycles (9.2), before the
  repeat codes were put in line.

**Reading the input in place: measured, and tabled** (owner, 2026-11-10). 5.4 stages every byte of input, and
weighs four alternatives, none of them the one Google's decoder uses: read the caller's array where it lies while
plenty of the chunk remains, and copy only the last bytes of each chunk. It was probed: the command loop's input
taken either from the staging area or from the caller's array (the source passed as a function, so one definition
gives both loops), the two timed in one binary, alternated.

| delivery | staged | in place | gain |
|---|---|---|---|
| the whole input in one call | 11.07 ms a pass | 10.71 | 3.2% |
| 16 KiB pieces | 11.37 | 11.06 | 2.4 to 3.0% |
| a mix of network read sizes | 11.53 | 11.46 | 0.4 to 0.8% |
| 1,460-byte pieces | 11.54 | 11.48 | 0 to 0.8% |

- The loop bears the caller's array as one more carried value: one instruction longer, three more values on the
  stack, and still faster. So that reason of 5.4's for staging does not hold.
- The gain is the copy and the loop's leaving every 4 KB to have more staged; the two were not told apart.
- It shrinks with the pieces, because each chunk's end costs what it did: its last bytes staged and read in exact
  mode, then joined to the next chunk's first bytes until the reading has moved wholly into the new chunk. The probe
  did this crudely (160 bytes of the new chunk staged each time); a careful form may do better at small pieces.
- It was correct under every delivery and the truncation test.
- A first probe, valid only for the whole input in one call, gave the 3.2% alone; the measurement in pieces was
  asked for before anything was decided on it, and is why the answer is not simply yes.

Tabled, not refused: it makes the driver switch between two sources at every chunk's end, and makes blindness to
layout something to prove of every read, where now no loop reads the caller's array at all. To be looked at again
when the whole decoder is measured.

### 9.5 Step 6, the stream layer: how it is to be built — built (9.6)

What 2.1, 5.1, 5.2, 5.4, 5.5, 5.8 and 5.10 say of it, gathered, with what they leave open settled here. Written
before the code, to be corrected by it.

**The decoder's start.** `start` sets up the front of a buffer it is given: the constant tables copied in (8.1), the
last four distances at their first values, the guard zero, the output's position and `handed` at the ring's start,
the staging area empty, the phase the window size. The buffer itself is still the harness's to provide, large enough:
its room and its growth (5.2) need a bound on a header's tables before they are built, which is the question 5.2
defers and belongs with the demand and the limit (5.9), step 8.

**The window size** is one element of 1, 4 or 7 bits, read in exact mode: its one unused pattern rejects. It sets the
ring's end, `2 ^ WBITS` bytes past its start, and the window, 16 less.

**A meta-block's start** is one element of at most 31 bits, read in exact mode with the bits to the byte boundary
where the format has them checked: whether it is the last and, if so, whether it is empty; the count of nibbles; then
either the length and, for a block that is not the last, whether it is uncompressed, or for metadata the reserved
bit, the count of bytes and the skip length. Its rejections are 5.10's. Then, by its kind:
- *the empty last block:* the phase becomes the end;
- *metadata:* the bits to the byte boundary must be zero; the phase becomes metadata with its count of bytes;
- *uncompressed:* the same of its bits to the boundary; the phase becomes uncompressed data with its count;
- *compressed:* the meta-block's end is the output's position and its length; the tables go at the smaller of that
  and the ring's end, and the slack (5.2); the header is begun.
Whether the block is the last is kept, for what follows it.

**Metadata** is passed by the driver without a copy: the count is lowered by the bytes of it in the staging area,
which are dropped, and then by bytes of the caller's chunk, counted as used.

**Uncompressed data** is copied by the driver into the ring at the output's position: first what is in the staging
area, by a copy within the buffer, then straight from the caller's chunk; each time as much as the input has, the
count has left, and the bound allows (the ring's end, and one byte more than the caller can take). Output waits and
is handed out as for the commands.

**After a meta-block** (its last byte produced, its metadata passed): the next meta-block's start, or, after the
last, the end. For a compressed meta-block this is the handler of step 7, which also checks that every block type
declared was used; the move to the next phase is made here, and the check left to that step.

**The end:** the bits to the byte boundary must be zero. Then a byte in the staging area or in the chunk rejects; the
end signalled, with everything handed out, is "done"; otherwise "needs input".

**Carried from one meta-block to the next:** the last four distances and their index; the output's position;
`handed`.

**What the harness is left with:** the events of step 7 (a block switch, a command that does not fit, a copy that
needs care) and the wrap, each still a `todo`. Its own reading of the frame goes, and with it the comparison of each
header with the specification's reading, which needed the header's place in the file.

**How it is checked:** every stream of the corpus and of Brotli's own test data (which has empty streams, metadata
and uncompressed meta-blocks) decoded through the driver under the deliveries of 9.4; the truncation test, with the
frame now the decoder's; and the frame's rejections, by changing the frame's own bits and comparing the verdict with
the proved decoder's.

### 9.6 Step 6 as built (2026-11-10)

Built as 9.5 says, in `Stream.lean` (`start`, the window size, a meta-block's start, what follows a meta-block) and
in the driver (metadata, uncompressed data, the end). What the code settled or corrected:

- **A meta-block of commands is over** when the loop stops before a head with the meta-block's last byte produced:
  for the reason "command", or for "insert-and-copy switch" when the block's count ran out on the meta-block's last
  command (the loop asks for the count's renewal before it reads the head, so the switch that never comes is asked
  for first). The driver tests the output's position against the meta-block's end for both.
- **The frame's elements are read after a top-up:** as for the header (9.4), the driver stages the chunk's next piece
  first when less than a refill lies ahead, so an element is found short only when the chunk is used up.
- **Two slots added:** whether the meta-block is the last, and the window.
- **The tables' place is rounded up to 8 bytes** past the slack. Measured both ways by the harness (30 mixed passes,
  three runs each, the aligned build before and after the other): aligned 11.32 to 11.36 ms at 16 KiB pieces and
  11.48 to 11.53 ms on the network mix; unaligned 11.43 to 11.48 ms and 11.59 to 11.62 ms. About 1% for the
  alignment; kept.
- **The comparison of each header with the specification's reading stays**, against what 9.5 expected. The harness
  no longer knows where a header begins, but fed a byte at a time the decoder always returns once with a meta-block's
  start pending, and its place then shows. So the comparison is a decode of its own, a byte at a time, with no hook
  in the decoder. As before, only a meta-block that returns to the harness at least once is compared (52 headers on
  the web corpus, 16 on Brotli's test data).

**Checked** (all steps of `check`): the web corpus under the deliveries of 9.4, 52 of 52; Brotli's test data, 44 of
45, the other needing the wrap (step 7); the truncation test on the web corpus, 503 rejected, 503 asking for input
with the proved decoder's output, 34 not judged (the cut fell where the harness's slow code was reading),
none wrong; and each of the first 48 bits of every stream flipped, the verdict against
the proved decoder's: on the web corpus 183 accepted with the same output, 1,537 rejected by the decoder, 762
rejected by the harness's slow code standing in for step 7, 14 needing the wrap, none wrong; on Brotli's test data
301, 933, 208, 54, none wrong.

**Read against the design again** (2.4, 5.1, 5.2, 5.4, 5.5, 5.8, 5.10, 9.5; owner's request). Conformant: the two
elements and their rejections; metadata and uncompressed data; the end; the statuses; what is carried between
meta-blocks (the distances' index is kept in the counters by the header's last step). Where the code differs:

- *The zero bits before the end were checked where the last meta-block ends*, not by the
  driver in the end's phase as 5.1's table has it. The bits lie in the byte the reading stands in, so they are
  always there. Measured below, and changed to the design's form.
- *The uncompressed bytes in the staging area are copied by `move`* (a `memmove`): the module has no copy for ranges
  that cannot overlap. A handful of bytes a meta-block.
- *`start` does not write the whole front* (5.2 says a stream's start does): it writes the slots, tables and guard
  it knows are read before they are written. The harness now fills the buffer with a non-zero byte before `start`,
  and every stream decodes as before, so nothing visibly rests on zeros; that every slot is written before it is
  read is still a fact owed to the proof. The whole front is written when the buffer is the decoder's own (step 8).
- *The ring's part is not extended and no demand is compared* at a meta-block's start (5.8): step 8, as 9.5 says.

**Each difference built both ways and measured** (owner's rule; the harness's decoder time, now with `start` inside
it, 30 mixed passes, three runs a schedule; the as-built code measured three times, between the others: 11.35 to
11.42 ms at 16 KiB pieces, 11.48 to 11.56 ms on the network mix; every variant also decoded Brotli's test data and
passed the flipped-bit test):

| the choice | the other way | 16 KiB | network mix | result |
|---|---|---|---|---|
| the end's zero bits checked where the last meta-block ends | checked by the driver in the end's phase (5.1) | 11.32 to 11.37 | 11.47 to 11.49 | no difference to be seen: the departure earned nothing, so the design's form is now built |
| `start` writes only what is read before it is written | `start` writes the whole front first (5.2) | 11.32 to 11.36 | 11.47 to 11.61 | no difference in the total; the smallest pages (708 to 6,138 bytes) read 0 to 3% slower, inside their own spread. Not settled by this harness; left as built until the buffer is the decoder's own (step 8), where writing the front is how the array comes to be |
| a frame element read after the chunk's next piece is staged | staged only once the element is found short | 11.34 to 11.37 | 11.49 to 11.51 | no difference; kept, since it is 5.4's shape (exact reading only at the chunk's end) |

The copy of staged uncompressed bytes by `move` is not a difference: 9.5 asks for a copy within the buffer, and this
is one. It may be as much as a staged piece (4 KB), not a handful of bytes. No stream of the web corpus has an
uncompressed meta-block, so that path's time is not measured at all.

**Two things found that are not step 6's, for step 7:**

- *A distance in the ring's last 16 bytes.* Before the first wrap the loop tests a distance against the bytes
  produced alone (5.5, "one comparison"). The format's largest distance is the smaller of the window and the bytes
  produced, and the window is 16 less than the ring: once more than the window has been produced, a distance between
  the two is a dictionary reference by the format and a plain copy by the loop, and a dictionary word's number is
  counted from the wrong place. 5.5 is wrong there. Until now the harness refused every stream whose output passed
  its window; it does so again. A remedy to weigh with the wrap: before the first wrap the bound's ring term is the
  window's end, not the ring's, so the last 16 bytes are produced by the handlers, which compare with both.
- *The tables' place after a wrap.* It is put past the smaller of the meta-block's end and the ring's end, from the
  output's position. After a wrap that position is small again while the ring is full, so the place must become the
  ring's end for good (5.2: "once the ring is full its end no longer moves"), and a meta-block's end must be carried
  across the wrap. Neither is built.

**Time:** not measured against step 5 on one build; the harness's figure (about 11.3 ms a pass at 16 KiB pieces, 11.5 ms on the
network mix, 30 mixed passes) lies within what step 5 recorded. The frame is a few elements a stream.

**Proved** (small and local): the sizes every step of the stream layer keeps; that the window size's field, where it
is not the unused pattern, names a ring of `2 ^ 10` to `2 ^ 24` bytes (`wbitsOf_range`); and that a meta-block's
start with the bits to the byte boundary is at most 38 bits, for metadata and for data (`metaStart_bits`,
`dataStart_bits`), which is the ledger's "one refill covers one element" for the frame. Owed still: the positions of
the uncompressed copy and of the refills, which rest on the invariant, and the driver's termination, whose control
flow step 7 changes again.

**Not done here:** the check that every declared block type was used, the bytes a rejection reports used, the wrap
(step 7); the buffer's room and growth (step 8). A stream that rejects on a further byte after its end does so
without handing out what waits, which the non-goals allow; to be looked at with step 7's rule for rejections.

## 10. Decisions

| decided | where |
|---|---|
| The design comes first and the large proofs once; small local proofs as the code is written | 1, 7 |
| The contract of five parts, stated against a reading of prefixes in the specification; the property on work tabled | 2.2, 2.4 |
| New primitives by three tests, the owner told afterwards; a load of 8 bytes added | 2.5, 4 |
| One buffer; the parts return it and nothing else; no allocation but a call's reply | 5.1, 5.2 |
| The tables after the ring, placed by the meta-block's declared length; room taken once | 5.2 |
| Six carried values; compute, then store | 5.3 |
| Elements; two modes from one definition, the mode passed as a function; a budget in place of a test of the input; a staging area | 5.4 |
| A ring with plain positions; one bound for the output; the wrap hands everything over first; a guard for the context | 5.5 |
| The round rotated; copies by blocks continued by rounds; the counters in one word; four compiled copies | 5.6 |
| Tables named by one value; lists by length and one walk to build | 5.7 |
| The stream's phases; the window size and a meta-block's start as single elements | 5.1, 5.8 |
| The list of rejections, from the specification | 5.10 |
