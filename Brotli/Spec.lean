import Brotli.Spec.Stream

/-!
# Brotli specification

Executable specification of the Brotli compressed data format (RFC 7932). The entry point is
`Brotli.Spec.decode : List UInt8 → Option (List UInt8)`, in `Brotli.Spec.Stream`.
-/
