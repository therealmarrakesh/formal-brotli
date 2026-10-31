import Brotli.Decoder.Interface
import Brotli.Decoder.GoalChecks
import Brotli.Decoder.Rest
import Brotli.Decoder.BitBuffer
import Brotli.Decoder.Refill
import Brotli.Decoder.Hit
import Brotli.Decoder.Slots
import Brotli.Decoder.Codes
import Brotli.Decoder.Table
import Brotli.Decoder.Lookup
import Brotli.Decoder.Window

/-!
# Decoder

The streaming decoder and its proofs against the spec.
-/
