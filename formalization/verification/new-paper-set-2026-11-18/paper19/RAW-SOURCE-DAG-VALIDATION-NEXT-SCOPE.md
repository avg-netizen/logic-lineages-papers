# Next bounded raw-source codec proof stages

The original four-contract/six-pin frozen comparator remains unchanged.

## Next requested gate: ValidationProof only

`RawSourceDAGValidationProof.lean` imports the passed RoundtripProof and proves lookup-index soundness, successful one-node reconstruction preserves the literal node and previous table, graph decode/encode converse, packed decode/encode converse, validator iff actual typed encoding, exact rejection/reification behavior and rejection of tags >=7. These are precisely the existing Validation endpoint; no computability or full packet acceptance from this gate. Proof candidate is authored offline and not compiled. A bounded root scope review is requested before native authorization.

## Subsequent genuine raw computation stage (not requested for native yet)

`RawSourceDAGRawValidatorDefinitions.lean` supplies a concrete numeric checker with all seven tags, exact payload arity, explicit in-range index checks, encoded simple-type checks and a tail-first finite list fold. All previous vertices, including repeated/unused vertices, remain in the raw specification list. The root is checked against the empty local prefix and declared output type. No type-code value is treated as malformed because the type codec is a bijection on Nat.

Required correctness proof: actual dependent typed lookup exists iff the numeric lookup checks; nodeValid iff actual step succeeds (with the literal spec list); graph fold success iff actual decodeGraph succeeds; check = existing valid. This is an operational inductive comparison against the existing executable dependent decoder, not a uniqueness-only reconstruction oracle. Computability of the concrete numeric checker follows from finite product/list primitives and fold, and transfers by that proved equality. Existing reifyCode equals the raw conditional reifier only by the proved successful decode/encode converse. This establishes Computable for the existing actual functions; it does not redefine their frozen semantics.

Actual raw routines are newly authored implementation helpers, not changes to the six frozen files. Full four-endpoint exact statement gate and independent final remain required. Whole compiler operations/input encoding/computability are still separate.
