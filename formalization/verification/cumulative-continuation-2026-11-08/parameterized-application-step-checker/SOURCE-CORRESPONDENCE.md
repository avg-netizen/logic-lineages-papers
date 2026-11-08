# Parameterized original application-step checker

The four exact targets retain the original raw application-step peeling and checking construction while threading one unchanged runtime parameter. Definitions and targets were approved and frozen before proofs, on base commit `fd5936d8`; exact snapshots and original supplier hashes accompany the freeze record.

## Literal programs and representation

The endpoint is an arbitrary `Program 6` on `[domain, codomain, source, target, argument, parameter]`. Its five structural type coordinates use the original `InternalApplicationStepPeel.endpointTypeGuard`. Original source, target, step, path, constructor and payload selectors inspect the unchanged raw edgeCode state. The parameter is separate from that state and never becomes a certificate field.

`transitionP` retains the original structural guard, returns the original peeledState on acceptance, and otherwise returns the unchanged raw state. `repeatP` is the existing raw `listRec` at two parameters `[initial state, parameter]`; it performs the same binary transition once per original path cell. No numeric fuel, new path encoding, or altered suffix parser is introduced. `checkerP` passes all three original selectors of the entire normalized state and the unchanged parameter to an arbitrary `Program 4` old checker.

## Exact internal targets

The raw-list front-cons target permits the transition to act on the initial state before the remaining original path cells. The lifted-transition target says that the actual original lifted state peels precisely to the original state. The lifted-checker target proves full-output graph equivalence between original and lifted source/target/certificate triples, not only preservation of acceptance one.

Every internal target permits arbitrary arithmetic bodies, assumptions, symbolic parameters and outputs. Original arrow and raw outer-tag graphs, the actual endpoint-acceptance graph and the original application/step-lift constructors are the explicit premises. No normalization, checker equivalence, successful decoding, semantic calibration or truth-to-derivability reflection is assumed.

## Original all-input calibration

The fourth target calibrates the literal checker to the original `NumberedNumericStep.numericStepTest` on every raw triple at one arbitrary parameter slice. The endpoint retains original source/argument universe decoding and unrestricted target packed decoding. Both leaf calibrations cover their entire original numeric domains. No subtype-closure, paired-parameter, source-validity or valid-certificate hypothesis restricts the checked input.

The surrounding structural endpoint, outer source/type guards, additional target-source validity, quotient-edge checker, and uniform typed application/path transport remain separate consumers. This packet does not claim unqualified `CertifiedApplicationLift` or promote a numbered statement.

## Verification scope

Definitions and Targets passed the serialized Targets preflight unchanged, receipt `build-reports/1794178997661209954-2.json`. All four exact StatementChecks aliases then passed in final receipt `build-reports/1794179832957649719-2.json`, using only `propext`, `Classical.choice`, and `Quot.sound`. Source-matched prior helper receipts and the unchanged resource profile are recorded in `STATUS.md`. The accepted scope is this supporting packet; the numbered register remains unchanged.
