# Application-head positional diagnostic

Status: source inspection only. Not a kernel-verified counterexample, accepted proof, or numbered result. No compiler was run for this review. The fully installed outer Context/G tuple was not checked.

## Concrete candidate

Write `o := Ty.ground`, `A := Ty.arrow o o`. Choose `n = 0`, empty symbols, `S = [o,A]`, and `Gamma = []`. Let both heads be `f = g := HeadCode.application o o`.

```
base   = argumentsCons A (bottom A)
           (argumentsCons o (bottom o) argumentsNil)
target = argumentsCons o (bottom o)
           (argumentsCons A (bottom A) argumentsNil)
left   = ordinary f base
right  = ordinary f target
```

Both packed result annotations are `o`. This uses the same application head, not a change of domain or result.

## Premises and source evidence

Paths below are relative to `formalization/LogicLineages/OrdinalComparison/`.

- `SourceMarkedSyntaxDefinitions.lean`, `headArguments` and `headResult`: the head has ordered argument types `[A,o]` and result `o`.
- `TerminationOrdering/NumberedFiniteUniverseDefinitions.lean`, `HeadInWindow`, `RankedCovered`, `rawHeadWindow`, `headWindow`: the application head is covered by the stated finite window. There is no ranked symbol obligation.
- `TerminationOrdering/NumberedAuxiliaryEnumerationDefinitions.lean`, `sourceHeads`: the same head occurs in the mapped finite head window.
- `TerminationOrdering/RecursiveComparisonDefinitions.lean`, `headClass`, `headEquivalent`: identical application heads satisfy class equivalence.
- `TerminationOrdering/NumberedExchangeCodeDefinitions.lean`, `argumentEntries`, `argumentPermutation`, `headMove`, `codeExchange`: complete `(type,term)` entries are swapped, so the permutation condition holds. Both head guards and class equivalence hold; the ordinary branch's extra result-equality test also holds.
- `TerminationOrdering/ID1Completion/SourceComputabilityCompletion/Continuation20261114/OriginalHeadMove/Definitions.lean`, `headMove`: the original program retains precisely window, target-head membership, class, and argument-permutation conjuncts. It adds no positional typing test.
- `TerminationOrdering/ID1Completion/SourceComputabilityCompletion/Continuation20261115/OriginalCodeValidityGuard/Definitions.lean`, `table`, `check`: this is the original Code-decoder validity guard, not typed-term acceptance. The candidate consists entirely of genuine Code constructors, valid type/head codes, and canonical nil; it does not exploit malformed raw syntax.
- `TerminationOrdering/NumberedAuxiliaryDecodingDefinitions.lean`, `decodeTerm`, `decodeArguments`: source arguments decode at `[A,o]`, using each bottom's matching annotation. Target arguments fail at their first annotation, because `o` is not `A`.
- `TerminationOrdering/ID1Completion/SourceComputabilityCompletion/OriginalTypedDecoderDefinitions.lean`, `ordinaryStep`, `bottomStep`, `consStep`: the ordinary root requests its actual signature; `consStep` tests expected-domain equality before pushing children. The target fails this test immediately. More raw+1 fuel cannot repair failure.
- `TerminationOrdering/ID1Completion/SourceComputabilityCompletion/OriginalUniverseDecoderDefinitions.lean`, `guard`, `extraGuard`, `transition`, `termCheck`: for an unrestricted implication quantified over arbitrary fixed `M/W`, constant-one programs remove these unrelated membership/window gates. Genuine membership/window programs need only accept `o`, `A`, and `f`, which the chosen window contains. This review does not establish the additional fully installed outer Context/G constraints.

Thus syntax validity and headMove alone do not supply destination positional typing. The candidate meets their source-level conditions while the source typed checker succeeds and the destination's first ordered argument check fails. These evaluations remain a source-level analysis, not newly executed or kernel-certified arithmetic results.

## Boundary: existing typed theorem is not refuted

`TerminationOrdering/NumberedExchangeNeighborhoodDefinitions.lean`, `argumentsFromList`, checks every permuted packed value against the destination's ordered signature. `ordinaryNeighbors` and `numberedNeighbors` use `filterMap` to discard unsuccessful typed reconstruction. This candidate's swapped list is discarded.

`TerminationOrdering/NumberedExchangeCalibrationProof.lean`, `termSound`, already quantifies over a destination `AuxTerm`; it does not assert arbitrary raw Code preservation.

The diagnostic therefore concerns an unrestricted raw-preservation bridge lacking destination positional compatibility, not the existing typed neighborhood theorem. The missing invariant is ordered type compatibility, not multiset equality or head-class equivalence. Homogeneous ranked signatures avoid this particular mismatch. No target-success premise or altered original AST is proposed here.
