# Computability and knowledge formalization

## External continuation — 29 October 2026, 16:58 UTC

The historical local author/Claude loop remains paused. The separately
user-authorized external Codex continuation has advanced the checked source
components below; it did not restart a paused local worker or claim a new
Claude authorship process. Root owns shared integration and the sole bounded
compiler queue; an independent auditor reviews/freezes targets and accepts
exact gate/axiom results. The original paused narrative and raw-candidate
provenance are retained below, **as historical state rather than current status**.

All results below passed independent gates against their entire frozen targets.
Their actual axiom closures are within `propext`, `Classical.choice`, `Quot.sound`.
No private import, added axiom, `sorry`, `admit`, or `native_decide` is used.
The fresh 94-gate checkpoint has been independently accepted. Later individual
gate passes remain separate from that fixed checkpoint; neither is a whole-paper proof.

### Accepted paper-02 reduction pipeline

The literal syntax remains `1`, positive variables, addition, and
`E(a,b)=2^a*b`. Source depth is unchanged: addition takes the maximum, while
E adds one to the maximum of **both** operands. All simultaneous equations and
comparisons share one valuation.

| Source component | Checked scope | Proof/gate receipt(s), `formalization/build-reports/` |
| --- | --- | --- |
| Seven-equation multiplication lemma | All eight positive witnesses, numeric iff, literal seven source pairs and depth ≤ 1; raw saved candidate passed unchanged | `1793266596541430476-7.json` |
| Circuit → equations, lines 198–210 | WF finite positive circuits; fresh/shared wires and 8 auxiliaries per multiplication; both extension directions; bound `n+9*length`; literal depth ≤ 1 equations | `1793267889765066639-6.json`; effectivity `1793269243914017424-6.json` |
| Circuit → strict/weak comparisons, lines 212–231 | Finite shared valuations; U/V equality iff circuit solvability; non-solvability iff universal `V<U` and `V+1≤U`; depth ≤ 2 and finite bounds | `1793271047692392626-6.json`; effectivity `1793271288704598576-6.json` |
| Polynomial → circuit, lines 191–198 | Actual `MvPolynomial Nat Int` interpretation of finite signed monomial-list codes, coverage of every finite-variable polynomial, exact positive/negative totals with seed ones; zero/negative/repeated terms and arity 0 | `1793274700919171962-7.json`; effectivity `1793274847307605786-7.json` |
| Positive polynomial → comparisons | Composed fixed-input extension/global root and counterexample equivalences, depth and arity, both actual computable coded maps | `1793276960837928845-7.json`; effectivity `1793277075122657267-7.json` |
| Nonnegative → positive variables, lines 185–190 | Literal Xi−1 expansion, actual polynomial substitution identity, ν↔ν+1 including arity 0, same WF/arity | `1793279801455200816-7.json`; effectivity `1793279214684539787-7.json` |
| End-to-end nonnegative polynomial-code reduction | Fixed-assignment positive extensions plus global root↔strict/weak finite counterexample and nonroot↔universal comparison; faithful codes and both actual computable compositions | `1793283333334508689-7.json`; effectivity `1793283167146427759-7.json` |

The output pair orientation is exactly strict `(V,U)` and weak `(V+1,U)`.
Effectivity is actual Mathlib `Computable` on explicit codecs, not merely
`Encodable`, definability, or a classical `Decidable` instance. Coverage of
abstract polynomials is existential; it does not assert a computable operation
extracting our code from an arbitrary quotient/extensional representation.

### Exact co-c.e. certificate, lines 232–236

`FiniteComparisonEnumeration` retains the existing expression/pair framing.
Its decoder rejects malformed and out-of-bound terms. The numerical token-stack
evaluator is proved equal to the literal source evaluation, at arbitrary finite
expression depths. Enumeration of positive `Fin d` valuations is surjective,
including `d=0`. The source predicates are defined by actual bounded terms and
finite positive counterexample valuations, **not** by search success.

The semantic gate proves those source predicates equivalent to existence of a
successful enumerated check. The effectivity gate proves actual `Computable`
evaluation and strict/weak checks and actual Mathlib `REPred` for both
source-defined counterexample predicates. Thus the strict/weak relations on the
well-formed finite-fragment domain have the asserted co-c.e. upper bound;
no MRDP premise is used. Semantic receipt `1793285203476493867-6.json`;
effectivity receipt `1793285411747227432-6.json`.

### Existential Diophantine supplier bridge

`DiophantinePolynomialBridge` proves genuine Mathlib `IsPoly` ↔ actual
`MvPolynomial` evaluation correspondence. Mathlib `Dioph` allows an arbitrary
auxiliary type β: the proof **derives** finite witness sufficiency from the
polynomial's finite variable support rather than assuming β finite. It then
proves finite WF-code representation with faithful first-n/last-m input/witness
framing. Finally the actual pinned `Dioph.pow_dioph` yields a code representing
the natural power graph `x^y=z`, including zero inputs. Exact six-clause gate:
`1793286540914150999-6.json`.

These are existential mathematical witnesses, **not computable witness extraction
from `Poly`/`Dioph` proofs**. Mathlib's missing full RE→Dioph/DPRM/MRDP theorem
has not been supplied or assumed. This supplier component does not complete
Hilbert's tenth problem or paper-02 hardness.

### Bounded-vector numeric preparation and pending queue

The semantic `FiniteDepthEnvelope` gate is accepted, receipt
`1793287420723574218-6.json`. For a literal term R, L is its actual node count,
s0 is `1+sum` of its distinct variables, b is `(L+1)s0`, and g is `5b`, all
represented by genuine addition-only source expressions. The gate proves
positivity, affine depth 0, unchanged finite variable bounds, and
`depth R≤2 → eval R≤2^(2^eval g)` at each shared positive valuation.

The full envelope effectivity gate has now passed, receipt
`1793292193390200071-6.json`, candidate
`03704c06de3c87cb4f6455a7734a8372665efbefce2ed31cd12b6710501d963a`.
It proves actual `Computable` encoded construction, exact existing-code
correspondence, malformed-input rejection and valid same-arity output decoding.

`FiniteDepthControl` has also passed its full fixed gate, receipt
`1793292777168166471-6.json`, proof
`848b4b53c39c5c548dca697af8d9c2b6b4370999672618590d3699ca2ad3c3b3`.
It composes the exact affine envelope with the already checked literal
`OrdinalComparison.Control.two_tower_le_fastControl` supplier, proving
`eval R ≤ fastControl 2 (eval g)` with shared valuation and unchanged arity.
The final 101-gate root aggregate passed, receipt
`1793292997840831261-18.json`, audit 458, including this final composition.
There are no pending compiler checks in this continuation lane at the deadline.
The first Control attempt stopped in an uncompiled optional `ControlCore`
dependency; the accepted proof uses established `Control` instead, without
editing another lane's source or importing the failed dependency.

Neither component establishes ψ admissibility, membership in the original
Wilken–Weiermann C classes, the norm bridge, or bounded source-vector comparison.

### Other papers and remaining whole-paper gaps

The saved full `GorbowFormulaSubstitution` candidate and gate passed unchanged,
receipt `1793266628221335736-6.json`. This is substitution semantics, not the
Gorbow DCB/CK fixed-point, internal derivability/Löb, KT/FS, revision or consistency
metatheory. Gorbow and Alexander knowing-machine theories remain distinct.
Paper 14 still lacks the ordinary-program/runtime and complexity-hierarchy
suppliers and reductions described in the historical handoff.

Paper 02 still lacks full DPRM/MRDP, recursive normal-form/separation and
one-variable decision suppliers, and the original admissible-substitution/
C-vector/ordinal-norm bridge. The checked code reductions and co-c.e. upper
bound do not by themselves establish the claimed complete classifications.

## Historical paused checkpoint (preserved)

Ownership: papers 02, 12 and 14. The Codex lane also leads the new, separately
guarded read-only Claude author loop for these papers. Root owns the shared
package, target register, compiler runner and integration.

Current state: **PAUSED by explicit user request for external-agent takeover**.
No author, compiler or new proof work runs in this stream. The returned R003
source remains unchanged and unelaborated after the memory deferral. The
self-contained public handoff is
`LogicLineages/ComputabilityKnowledge/PAUSED-HANDOFF.md`; its local provenance
copies let the external agent continue without private Claude logs.

Saved checkpoint: **two exact local targets are accepted**. The finite-system
collision proof passed on its first proof compile. The paper's bounded
multiplication lemma passed after one explicit rewrite instantiation. Both
independent gates match their frozen types; actual axioms stay within the
standard three. All full paper conclusions remain pending. The exact prediction-game, Gorbow-signature and term-substitution foundations
also now pass their independent semantic checks; full prediction-complexity
and knowledge-theory targets remain pending.

## Initial comparator

`LogicLineages/ComputabilityKnowledge/PositiveExpression.lean` defines the literal
paper-02 grammar with positive valuations and its natural-number evaluation.
It includes structural renaming lemmas. `Comparators/ExponentialGap.lean`
independently defines the source U/V constructors for arbitrary finite systems
and the exact nonnegative-gap/zero-set target, including empty systems.

The initial comparator passed before authoring. Root then diagnosed Lean's
modern module/import requirement and authorized **header-only** migration;
all original mathematical bodies and hashes were preserved in the round's
provenance record. The accepted modern comparator has SHA-256
`f50d88fcd80d9a494e24572ea16b29f5f80d2dd01d728f23bca1b3a5b1b6179e`.
Its core-only syntax dependency has SHA-256
`4ad6156af313275071fae9fa1d4b0a3166fccf99c2cb38a6a46921113a6fc1ed`.
The unchanged-body comparator passed again before candidate compilation.

`ExponentialGapProof.finiteSystemCollision` is accepted at the exact `Target`
by `ExponentialGapGate.lean`. It proves the source U/V nonnegative-gap and
equation-system equivalence for all finite systems and shared positive
valuations. The candidate and exact gate passed in 2.99 and 1.22 seconds,
with peak RSS 500,904 and 494,808 KiB; the gate's complete axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. No proof-body correction or
duplicated hand proof audit was needed. This is a reduction lemma, not the
full paper's classification.

R002's independently fixed `Comparators/RestrictedProduct.lean` has now
compiled and is frozen at SHA-256
`3b6aec50b063e33c05f7d4ecddfd8af123cab045a4eb7a40ce73e129e4831214`.
Its exact positive-domain bounded multiplication identity is paper02
`lem:restricted-product`; comparator receipt1793246364158248187-2.json passed.
The same authorized read-only Claude author returned a complete141-line
candidate at04:07:23UTC, peak session RSS326,468KiB. Its immutable source and
initial public candidate are byte-identical (SHA-256
`2e3f19f232b5ddd663b544bab7d0c0d106abf652d17db0a952fd495e8f839c33`).
`RestrictedProductProof.boundedMultiplication` and the independent
`StatementChecks.restricted_product` gate now pass at the exact frozen Target.
This completes paper02 `lem:restricted-product`: all positive variables,
exact strict bounds, iff, and both simultaneous positive witnesses.
The final proof differs from the raw proposal only by explicitly fixing D,k
in a geometric-sum rewrite. Receipt1793247970233247267-2.json records proof
2.947seconds/298,908KiB and gate1.064seconds/368,032KiB. The gate's actual
transitive axioms are only `propext` and `Quot.sound`. Comparator/gate/source
hashes are unchanged. The accepted proof SHA-256 is
`fc1638d3ba1408e74819e02e0ec0495daf88ebb153511795bc67db4df9774c80`.
No additional premise or whole-paper computability claim was introduced.

R003's full seven-equation comparator passed before authoring, receipt
1793248471358273988-2.json, and is frozen at SHA-256
`a43bd3e54d1bdb9cb421ed2acde22e3390a4955bf114d4304cdaed87d0207d5e`.
The authorized read-only author returned a complete200-line proposal after
transport recovery. Exact existing session/model/high and actual source reads
were verified. The raw candidate is saved unchanged at SHA-256
`79c9f0059d64dc1b4049635a708875d7fc1d019492fe56b0efd83b52a02545e9`.
Its first attempted core-profile compilation deferred **before Lean launched**:
671MiB available versus the unchanged768MiB guard, receipt
1793254222090917897-2.json. No proof-body read/repair preceded that attempt,
and the seven-equation theorem remains unaccepted pending actual elaboration.
R004 has not started; main/other native checks get their agreed windows.

The frozen R003 specification `Comparators/MultiplicationGadget.lean` matches all seven numerical source
equations and all eight positive witnesses of `lem:seven-equations`. Its
full local Target also demands correspondence with the literal seven source
expression pairs and the stated depth-one bound; those are not silently
omitted from the prospective lemma.
`PositiveExpressionProperties.lean`, `PredictionGame.lean`, `GorbowSyntax.lean`
and `GorbowSubstitution.lean` now pass `FoundationChecks.lean`, receipt
1793248486091914766-2.json. The five explicit gates cover positive evaluation,
the depth-two collision compiler, the actual-history semantic anti-predictor,
literal arithmetic falsehood, and full source-term substitution semantics.
Every axiom closure stays within the standard three. These are exact
foundations, not computability, arithmetization or consistency conclusions.

The target is not a redefinition of its desired conclusion: the source terms
are built solely from 1, variables, addition and E(a,b)=2^a b, and their
evaluation is fixed structurally. A candidate must prove the displayed
universal inequality and equation-system equivalence. This local reduction
lemma does not establish MRDP hardness, identity decidability, a one-variable
comparison algorithm, or the Wilken–Weiermann source-vector bridge.

## Full dependency obligations

- Paper 02: source grammar/evaluation, bounded multiplication and seven-equation
  gadgets, exact finite-system detector, effective circuit compiler, the actual
  MRDP undecidability supplier, recursive normal forms and separation,
  constructive one-variable bounds, and original admissible-domain/vector
  correspondence. A classical Decidable instance would not prove an algorithm.
- Paper 12: actual full-language arithmetic syntax and coding, recursively
  self-indexed DCB presentation, internal provability derivability conditions
  and Löb's theorem, exact CK fixed-point substitution, KT/FS proof rules,
  selector equivalences, standard-model revision semantics and consistency.
  These cannot be replaced by a generic assumed provability oracle or by the
  different knowing-machine theory from the 3.1.3 development.
- Paper 14: actual finite-history play, ordinary program numbering and bounded
  simulation with the stated input-tape runtime convention, finite error
  certificates, recursive-matrix hierarchy/jump characterizations, adaptive
  baseline, uniform total-predictor reductions, canonical total-function list,
  diagonal finiteness and exact measure/comparator reductions. A semantic
  anti-predictor alone would not prove that its evader is computable or has
  the required runtime-class membership.

## Reuse inspection

The existing 3.1.3 project has concrete partial-recursive coding and explicit
first-order/Hilbert proof syntax. Those are candidate reusable foundations,
not a proved Gorbow DCB or arithmetical-hierarchy supplier. No private project
module has been imported or copied at this checkpoint.

## Author and acceptance policy

For each round, Codex first compiles and freezes the independent comparator
and its complete local import-source hashes. Claude reads it and returns
separate proof source. Compile the candidate first. Repair compiler failures;
after a pass, check exact target matching and the complete axiom report.
The final gate must type-check the accepted declaration at the frozen type
without additional premises. Only then record acceptance and send feedback.
All compile commands use root's bounded serialized runner. No sorry, project
axiom, native_decide proof or hidden theorem supplier is permitted.
