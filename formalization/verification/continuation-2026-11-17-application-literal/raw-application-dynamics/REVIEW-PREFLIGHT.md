# Independent preflight review — raw application dynamics

Decision: **accept the proposed exact supporting scope** on 2026-11-17,
following base commit `206a3ae0`.

## Reviewed source pins

Under
`LogicLineages/OrdinalComparison/TerminationOrdering/Continuation20261117/RawApplicationDynamics/`:

- `Targets.lean`: `af7c0485dab35d8978dc5360130b6634d0e0b8ecc4191545035f74eb2a2f46c5`.
- `ComparatorGate.lean`: `47c152a80797197d8a919d2e68d74132fe0c490a087f2b4de2b3449139ab118b`.

## Relation and source correspondence

The original `RawStep` rules for an auxiliary application have exactly three
possibilities: a function-side step, literal beta contraction, or same-type
bottom. The argument is unchanged by function-side reduction. The original
functional application head is still an ordinary head with its own rules.

The path target retains these original relations. Before a root beta step,
the application retains the same argument and follows a finite original
function path. At a root beta step, that function is a genuine lambda, and
the remaining path starts at `substitute body (singleSubstitution a)`.
Bottom is terminal; the reverse bottom alternative follows from the original
direct bottom rule. The three alternatives need not be disjoint and no
unique decomposition is asserted.

The accessibility target uses the descending orientation of `Acc`. Necessity
follows by lifting function steps and paths, then using the actual beta rule
to reach each indicated contractum. Sufficiency follows by induction on
function accessibility, carrying accessibility of every contractum reachable
through an original finite function path. It assumes no argument reduction,
argument accessibility, substitution compatibility, normalization agreement,
or finite-window oracle.

This is a precise native supplier for the lambda/application reasoning in
paper 6 `lem:id1`. The existing `NumberedRewriteApplicationPathProof` supplies
path composition and function lifting, while
`NumberedInverseApplicationAccessibilityTargets.ActualInverseApplicationAccessibility`
concerns a finite-window numeric quotient relation. Neither is the new raw
finite-path decomposition or exact raw accessibility criterion. No duplicate
at this exact interface was found in the inspected sources.

## Acceptance boundary

This review does not accept candidate proof artifacts or claim a native run.
The original frozen definitions, serialized limits, exact-type checks, and
standard-axiom audit remain required. No internal ID1 derivation, quotient
certificate transformer, source substitution/fundamental theorem, global
accessibility, stable-pair repair, or numbered completion follows from these
native statements. The reviewer ran no compiler or Git operation.
