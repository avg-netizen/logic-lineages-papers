# Original packed structural coding and decoding

Paper06 lines551–556 uses computable primary classes and least-code
representatives of typed numbered syntax. The original candidate-list algorithm
enumerates structural `(Ty, Code)` pairs and filters them through `decodePacked`.
These three fixed targets connect that exact interface to the previously
accepted numeric packed presentation.

The actual `packedCode` map is primitive recursive for every fixed finite
signature, arity and context. The actual numeric decoder on the original
type/code pairing equals the original structural `decodePacked` for every pair,
including ill-typed pairs. This calibration must discharge the numeric decoder's
final re-encoding filter from the existing soundness results. The original
structural decoder is then primitive recursive with its dependent typed output.

No encoding, decoder, rejection branch or context is changed. There is no
well-typedness premise on structural input. Candidate-list completeness remains
the separate accepted coverage theorem; primary equivalence decisions, canonical
representatives, arithmetic representation and accessibility remain separate.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
