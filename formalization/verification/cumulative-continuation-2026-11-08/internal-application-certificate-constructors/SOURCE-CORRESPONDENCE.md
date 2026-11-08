# Original application-certificate constructors

This supports paper 06 `lem:id1`, specifically function-side application
reduction and its certificate transformations (paper.tex lines 582–595).
It is independent of path traversal. Internal acceptance preservation for
the original typed step/quotient-edge checkers remains a separate obligation;
the whole accessibility and computable-substitution arguments remain pending.

The explicit programs compute the unchanged numeric functions
`ApplicationCertificateLift.rawApplication` and `liftStep`, and
`ApplicationCertificateLiftEdge.liftEdge`. The edge envelope is exactly
`NumberedNumericQuotientEdge.edgeCertificateNumber`: source paired with
(target paired with step). The selectors use those same original pair
coordinates. The application constructor uses the original node tag 2,
codomain and domain codes and the right-unpaired source payloads. The step
transformer prefixes `positionNumber .appFunction` through the original list
cons and preserves the complete replacement/root payload without decoding it.

Every AST is built explicitly by composition from the already proved original
Nat.pair, Nat.unpair and list-cons programs. No program is selected by a
primitive-recursive completeness theorem. Separate calibration covers all
natural inputs, including malformed codes, and names the original functions.

The internal targets are closed proof schemas in the unchanged
`InternalCalculus.Derivation`, with arbitrary positive body, free-variable
type and symbolic arithmetic terms. They recover/reconstruct exact edge
fields, equate raw application with its explicit packed-node builder,
preserve the original step prefix and replacement/root payload, and prove
bidirectional edge-constructor commutation at the same supplied fields and
transformed codes. Intermediate witnesses are discharged through original
existential elimination and existing graph totality/functionality; evaluation
calibration supplies no internal inference.

Definitions and ten exact target propositions are frozen before proofs.
No original source, checker, arithmetic definition, numbered target or
global register is modified.
