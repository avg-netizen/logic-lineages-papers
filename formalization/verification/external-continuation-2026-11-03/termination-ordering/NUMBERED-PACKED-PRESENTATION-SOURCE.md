# The actual packed typed-syntax presentation

Paper06 lines551–556 uses effective coding of typed auxiliary terms before taking
least-code primary representatives. For each finite signature, actual arity and
fixed binder context, this component uses exactly the existing `packedNumber`
encoder and `decodePackedNumber` decoder for `Packed (Fin n) arity Gamma`.
Its `Encodable` round trip is the accepted actual packed numeric round trip.
No surrogate syntax type or freely assumed primitive-codability field is used.

The frozen targets calibrate the encoding, prove that decode followed by Option
encoding is `value + 1` precisely on successful original decodes and zero otherwise,
and require this normalization function to be primitive recursive. Combined with
the actual round trip, that supplies the mathematical obligation for a genuine
`Primcodable` instance. Success effectivity must be proved by the actual typed
validator component; it is not a new hypothesis or an oracle.

The fixed-context output type retains the actual dependent term and its result
type. This does not itself prove effective finite-universe filtering, primary
class enumeration, step-certificate checking, arithmetic accessibility or a whole
source theorem. The manuscript and all accepted numeric codecs remain unchanged.

Prospective SHA-256 hashes:

- Definitions: `2b9dd41c24b02c84eecd2d802390706ad94cc6dd39bb5a9c356c21ab1065d266`.
- Targets: `254c067f0fee12e02f7892d285fba2ad6a3013db4f8b2fb1a420a9b5ba95ec68`.

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
