# Joint-context quotient edge and path checkers

Baseline: `fd555e8d851c81bd730804dee9cf64f77f43e4a7`.
Paper06 `paper.tex`, lines 538–556, fixes a finite type window, defines the
numbered reduction and finite primary classes, works with least-code
representatives, and identifies H and R = H^+ as arithmetic. This component
supplies stronger joint-context primitive-recursive checkers for the existing
certificate presentations of those relations. It does not prove accessibility,
well-foundedness, ID1 derivability, the whole `lem:id1`, or private II5 claims.

## Exact comparator and input contracts

`ActualJointEdgePrimitive`, `ActualJointPathPrimitive`, and
`ActualJointPositivePrimitive` name the ORIGINAL `numericEdgeTest`, `pathTest`,
and `positivePathTest` directly. Only the finite signature size and arity are
fixed. The symbol list, finite type list S, ambient context Gamma, precedence
Boolean table, endpoint numbers and certificate are joint inputs. No premise
requires the context, endpoints, certificate or table to be valid. Neither
certificate numberings nor their malformed-input behavior change.

The raw edge implementation preserves the original three-number certificate,
source-universe decoder, target packed decoder, complete numeric step check,
and both least-code representative comparisons. Its calibration is pointwise
on every input. The literal path check visits entries in their original order
and tests the terminal endpoint; the positive numeric check keeps the original
path decoder and rejects an empty certificate even when endpoints are equal.

## Nonduplication and supplier provenance

The accepted `NumberedQuotientCertificatesPrimrecTargets` quantifies Gamma
outside `Primrec`; it does not give joint-Gamma effectivity. Accepted
`ContextUniformPrimary` supplies joint-Gamma raw representatives with exact
typed calibration, while `NumberedNumericStepPrimrec` supplies the original
joint-Gamma step test. Their exact definitions and proofs are reused unchanged.

The Nov 4 `sol2-id1` R005 archive contains an earlier larger unaccepted
edge/path/direct/context-program candidate. Its partial axiom log records an
edge/positive-path check, but the corresponding source was explicitly archived
as unaccepted and the whole gate was not adopted. This component transparently
reuses the raw-edge proof structure while narrowing the new comparator to the
three ORIGINAL checkers. No archived result is treated as an accepted supplier;
all new files are checked in a fresh focused gate. The archived files stay
unchanged. Direct multiset and full encoded context-program claims are excluded.

The targets and implementation definition are hashed before proof creation;
preflight must pass before authoring the new proof modules. Acceptance requires
exact target aliases and actual axiom closures contained in propext,
Classical.choice and Quot.sound, with the unchanged serialized bounded checker.
No manuscript, global register, root import, checker, dependency or CI change.
