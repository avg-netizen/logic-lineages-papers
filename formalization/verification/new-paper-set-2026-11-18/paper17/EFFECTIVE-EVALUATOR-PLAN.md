# Selected-control effective closed evaluation: next exact scope

This is a plan only. No successor definition/target/proof is authored here,
and the pending CollapseStatementChecks packet stays frozen.

## Genuine reusable suppliers

- `EncodedNormBallDefinitions/Proof`: `encodedNormalNormBall` exhaustively
  enumerates all normal raw codes of additive tree-weight <= b; it is primitive
  recursive. Its decode characterization and all-raw code bound are genuine
  algorithms, not a finite-set existence oracle.
- `EncodedMaximumDefinitions/Proof`: `encodedMaximumPredecessor code budget`
  filters that list using the actual encoded ordinal comparison and takes its
  largest entry. For every positive normal notation and arbitrary budget,
  `encodedMaximumPredecessorActualCorrect` identifies the decoded result with
  the independently defined actual ordinal M. The binary numeric function is
  primitive recursive on every input, including invalid raw syntax. It does
  not depend on Phi and is reusable without semantic changes.
- `RawSplit`/`RawNormCode`: compute the limit-part code and finite tail, and the
  exact additive norm, respectively. `encodedFiniteTest/Value` are also
  control-independent. Their existing correctness proofs can be reused even
  if their import closure also contains fixed-Phi proofs: no such fixed-Phi
  conclusion may substitute for a new selected-control conclusion.
- `actualLimitPart` and `actualTailPart` use ordinary ordinal quotient and
  remainder by omega. These definitions and the split proof are independent
  of the control. Existing actual descent/terminal steps are not independent.

All reused source/compiled artifact dependencies must be reconciled under the
normal bounded native checker and recursive evidence before acceptance.

## New parameterized semantics

Define an actual nonfinite step using
M(actualLimitPart alpha, f(actualOrdinalNorm alpha)); make finite states
absorbing where an iterated total step is needed. Establish its strict ordinal
descent, epsilon-zero closure, exact next norm f(N(alpha)), and collapse
recurrence from the currently pending selected-control single-predecessor
packet. Do not evaluate M(alpha,...) when alpha contains a finite tail.

Define a parameterized actual well-founded endpoint/count pair with finite
base (n,0) and nonfinite branch (endpoint(next),count(next)+1). Prove first
finite occurrence, no earlier finite state, endpoint=f^[count](initial norm),
collapseWith f alpha=endpoint+count, and 0<count<endpoint at nonfinite starts.
These semantic results alone do not prove computability.

## New numerical program and independent exact target

Define `encodedStepWith f n` to return n when encodedFiniteTest n, otherwise
encodedMaximumPredecessor(limit-part code, f(rawNormCode n)). Iterate this
numeric function k times. Use Nat.rfind over the Boolean finite test to find
the first finite state, and return its decoded finite value plus k. Invalid
raw-normal codes return zero immediately. A total-value wrapper may use a
fallback only alongside an independently proved totality theorem; fallback
must never be cited as termination.

For a generic computable strictly increasing f>=G, require Partrec of the
concrete search program, totality on all natural inputs, actual Computable
of its total output, and equality on every normal code to the independent
collapseWith f denotation. For fStar and each fb discharge the computability
premise using the proved primitive-recursive certificates; concrete endpoints
must have no supplied termination/correctness/computability premise.

For the selected PR controls, the numeric step and bounded iteration can be
proved primitive recursive; the unbounded closed evaluator is required only
computable. Do not claim it is primitive recursive from bounded-step PR.

Prove code-trajectory NF preservation and actual denotation by induction,
then use well-founded actual terminal data to witness rfind termination and
leastness. Prove all-input totality by splitting rawNormalCode. Finally
combine Partrec + totality to obtain Computable, as in existing
EncodedCollapseProof, but with a new genuine parameterized program.

## Source acceptance boundary

The full printed cor:closed-evaluation requires the algorithm, computability,
actual collapse agreement, exact norm orbit and positive-count bound. It must
not be promoted after only semantic recursion or only a supplied search
witness. Exhaustive encoded maximum suffices for effectiveness, but does not
prove the separate optimized simultaneous M/L recursion in
thm:maximum-predecessor. That theorem remains distinct even if the exhaustive
evaluator is complete. Complete residue/count/entry theorems remain separate.
