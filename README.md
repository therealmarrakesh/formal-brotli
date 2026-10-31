# formal-brotli

A formal specification of the Brotli compressed data format ([RFC 7932](https://www.rfc-editor.org/rfc/rfc7932)) in Lean 4, with no dependencies beyond the toolchain.

The spec is an executable function, `Brotli.Spec.decode : List UInt8 → Option (List UInt8)`: `some y` means a valid stream with output `y`, and `none` means an invalid one.

A decoder built for real use, proved correct against this spec, comes next.

```sh
lake build
```
