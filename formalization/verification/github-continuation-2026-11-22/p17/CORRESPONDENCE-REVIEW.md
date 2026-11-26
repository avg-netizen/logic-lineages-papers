# Paper 17 comparator scope review — 22 November 2026

Baseline: `dd4eddff9f8eab0a4532e8df4880f71b8d5dffb9`, branch
`formalization/new-paper-set-2026-11-18`.

This is a focused comparison of the printed statements, their definitions,
and the frozen Lean propositions. It introduces no proof-validity claim,
native gate result, register promotion, manuscript change, or replacement of
an accepted source. The existing receipts for #1418, #1428, and #1429 remain
the evidence for those exact propositions.

## Decision

| Printed statement | Existing comparator | Scope finding |
| --- | --- | --- |
| `thm:arithmetic` | `ClosedBlockDecision.ClosedBlockDecision` | No material mismatch found in the stated circuit language and original-domain semantics. |
| `thm:ground` | `GroundComparison.GroundComparison` | No material mismatch found for the fixed effective policy and fixed control of this theorem. Zero padding is explicit in its printed proof. |
| `thm:main` | `GroundComparisonMain.MainComparison` | **The supplied-policy uniformity clause is absent from the proposition. Keep the printed theorem pending.** |

The earlier `P17-THM-MAIN-CORRESPONDENCE.md` says that uniformity in the policy
means merely that the theorem holds for every policy. That interpretation
does not retain the printed effectiveness claim. The finding concerns the
strength of the comparator, not the validity of its checked proof and not a
counterexample to the mathematical theorem.

## 1. The missing uniformity clause

Paper 17 `paper.tex`, lines 83–100, states the comparison classification
"uniformly in a supplied computable admissible literal parsing policy".
The supplied object is an algorithm for the policy selector, not merely an
arbitrary semantic policy accompanied by a proof that some algorithm exists.
The generated-source theorem also explicitly states uniformity in the
supplied computable policy (`sections/source.tex`, `thm:generated-source`).

The frozen target in `GroundComparisonTargets.lean`, lines 47–52, has this
quantifier order:

```text
for every policy p,
  Effective p implies
    for every relation rel,
      there exists a total computable Boolean decider for p and rel.
```

`StandardControlCurrent.PolicyShape.Effective p` is the proposition

```lean
Computable (fun x : Nat × Nat => selector p x.1 x.2)
```

in `PolicyShapeDefinitions.lean`, lines 39–45. Neither it nor
`GroundDecidable` takes a selector program as a runtime input. The decider's
runtime input is only the context length and the two source-term codes.
No single evaluator taking a policy program, and no computable transformer
from policy programs to decision programs, occurs in the comparator.

The difference is the standard distinction between
`∀ p, ∃ computable decision procedure for p` and one effective construction
from a supplied program for `p`. Existential witnesses inside a `Prop`, or
classically choosing one such witness for each `p`, do not establish that
construction. This distinction persists even if the existing mathematical
construction is in fact uniform.

`GroundComparisonMain.MainComparison` is only the conjunction of
`Targets.FullControl`, `Targets.NearControlModular`,
`GroundComparison.GroundComparison`, and
`SelectedFunctionalHardnessTargets.SelectedFunctionalHardness`.
The control-law conjuncts add no policy-program clause. Therefore the
missing uniformity cannot be supplied by another conjunct of the current
main comparator.

The same per-policy shape occurs in
`SelectedGeneratedSourceTargets.Programs` and
`StandardControlCurrent.PolicySourceInterfaceTargets.Programs`. The raw
compiler definitions are useful concrete material for a repair, but those
effectivity propositions do not by themselves express uniformity in a
selector index.

The hardness route has a shorter available bridge: the separately accepted
`SelectedFiniteQueryTargets.ExactTotalReduction` and
`SelectedSingleQueryTargets.ExactTotalReduction` identify literal reduction
functions `FiniteQueryCode.reduceCode` and `SeededQueryCode.reduceCode`
independently of the policy and control. Their `LiteralProgram` /
`LiteralPrograms` clauses state the required effectivity. A strengthened
main comparator can expose these existing uniform reductions; it should
not rely only on moving existential quantifiers in the weaker
`SelectedFunctionalHardness` proposition.

For the near-control family the current positive comparator also has
`∀ b, ∃ decide`, without joint computability in `b` and the encoded query.
The standalone ground theorem says "a fixed f_b", so this is appropriate
there. A repaired main target can explicitly include `b` among its supplied
parameters, avoiding another interpretation question about the phrase
"For every supplied b". No failure of joint computability is asserted here;
it is simply not exposed by the current target.

## 2. Arithmetic circuit semantics

The relevant printed language is specified in
`sections/arithmetic.tex`, its opening paragraph, `thm:arithmetic`, and
"The finite matrix language". It permits natural inputs, natural-valued
affine gates, fixed control iterates, entry norms, interval counts, and
fixed-head collapses, with signed linear rows and arbitrary Boolean
combinations in the output test.

`OriginalPrintedCircuitSequential.Gate` combines
`OriginalMixedGateSequential.Gate` (signed affine and arbitrary-head
collapse) with `OriginalNaturalFieldGates.Gate` (iterate, entry, count).
`Topological` requires that inputs are known before each gate and its
output is fresh. Shared names are actual common coordinates in the single
valuation; no pairwise-independent replacement appears in the proposition.

`PreparedProjection.PlainPreparedFormula` says only that every row
summand is a plain variable coordinate. It does not restrict Boolean depth,
integer coefficients, repeated occurrences, constants, or positive moduli.
`NormalForm.Formula` contains negation, conjunction, and disjunction, and
its atoms contain nonnegative signed rows and divisibility by `m + 1`.
Equalities and the other inequalities are expressible by these atoms and
Boolean connectives. Nonlinear expressions are represented by the circuit
nodes whose values those variables read.

This matches the printed flattening convention. The theorem is over finite
circuits, and its proof explicitly assigns a coordinate to each node and
keeps all graph equations outside the Boolean output test. A separate
theorem about compiling some additional arbitrary term grammar is not
part of this printed statement. The ground-source use already has its
separate scalar-to-circuit interface in #1423.

`HasSuccessfulObservation` existentially quantifies one base valuation and
requires the literal circuit observation to succeed with the requested
polarity. `EverySuccessfulObservation` requires that polarity of every
successful observation. An invalid gate input is neither a successful true
nor a successful false test. This agrees with the paper's requirement that
each call carries its true domain and its final explanation that universal
blocks are absence of counterexamples on the same original domain.
Vacuity when that domain is empty is consequently appropriate.

The arbitrary-head interface uses `NONote` heads and
`ArbitraryFixedHeadCollapse.ActualGraph`, whose specified value is
`collapseWith f (a + u)`. `ActualNormalization` includes finite-head
evaluation and transport of the finite tail to the decoded limit part.
These are the head cases printed immediately after `thm:arithmetic`.
This review retains the already accepted interpretation of `collapseWith`
and ordinal notations; it does not reopen those earlier proof bodies.

`Decides` requires correctness only on admitted topological encodings with
plain matrices. Its true and false equivalences ensure that the
`Option Bool` result is not `none` on those inputs. The raw function itself
is total and computable. The printed input class is precisely a valid
finite circuit, so no new semantic restriction results from leaving
malformed numerical encodings outside the correctness statement.

"Preserves sharing" is expressed semantically by deciding that same
shared-coordinate circuit. The comparator does not separately expose an
internal memory-layout or complexity invariant. No such additional
resource property is specified by the printed theorem.

## 3. Ground comparison semantics

`sections/consequences.tex` starts by fixing one computable admissible
literal policy and states `thm:ground` for the factorial control or a fixed
near control. Its quantifiers therefore agree with `GroundDecidable` for
the standalone ground theorem; the stronger uniformity issue arises when
this result is presented as the whole main classification.

`Source.AdmissibleSum.Policy` contains a site-and-arity selector for an
ordered full binary shape. `Shape` has only leaf and binary join, and
`expand` inserts operands in order as unchanged subtrees. Together with
`PolicyShape.Effective`, this matches `def:literal-policy`, including the
fact that the choice does not inspect operand values or syntax.

`GroundComparison.Canonical` uses the literal
`AdmissibleAssignment.assignment p` of each typed original term.
`GroundDecidable` restricts only free-context entries to `Ty.ground`;
result types, internal binders, and source terms remain unrestricted.
`Holds` uses universal admissible substitutions and the printed three
coordinate relations. `GroundComparisonDomain.SelectedGroundDomain`
specifies the exact two directions between ground admissible substitutions
and independent positive-natural component valuations.

The zero-padding convention is **explicit**, not merely an interpretive
choice: the proof of `thm:ground` says to use zero padding beyond the
assigned level. `GroundComparison.vectorAt` does exactly this. A decision
procedure correct on encoded typed terms matches the theorem's input
class. No new source-scope mismatch was found in this comparator.

## 4. Narrow repair using an ordinary universal evaluator

An ordinary partially recursive evaluator can consume the supplied policy
program. A lasting Turing-oracle hypothesis is unnecessary. The pinned
Mathlib `Computability/PartrecCode.lean` provides
`Nat.Partrec.Code.eval_part`, `exists_code`, `primrec₂_curry`, and
`eval_curry` (the `smn` interface).

A suitable realization relation is:

```text
RealizesPolicy(e, p) :=
  for all tag and n,
    e.eval(pair(tag, n)) =
      Part.some(encode(PolicyShape.selector p tag n)).
```

The first bounded supporting target should be a **uniform macro
interpreter**, without attempting the full compiler in its first gate:

```text
macro(e, tag, n, xs) :=
  e.eval(pair(tag, n)).map
    (fun z => decodeListBool(z).bind
      (fun script => PolicyShape.expandCode script xs)).

Partrec(macro), and
RealizesPolicy(e, p) implies
  macro(e, tag, n, xs) =
    Part.some(PolicyShape.macroCode p tag n xs).
```

Here the outer `Part` represents possibly nonterminating policy programs;
the inner `Option` preserves the existing syntactic expansion rejection.
`PolicyShapeTargets.RawPrograms` already supplies primitive recursiveness
of `expandCode`. This target needs only the universal evaluator, code
decoding, that accepted raw program, and an exact calibration equation.
It introduces no extra mathematical hypothesis beyond identifying the
actually supplied program with the existing policy.

The next target should expose one `Partrec` function

```text
compilePolicy(e, contextLength, termCode) : Part (Option EncodedVector)
```

with equality to
`Part.some (PolicySourceInterface.compile p contextLength termCode)`
whenever `RealizesPolicy e p`. Its implementation lifts the concrete
`PolicyPartial`, `PolicyConstructors`, `PolicyAbstraction`, and
`PolicyAssignment` recursions, preserving their rejection cases. Those
definitions make finitely many selector calls on every finite run; the
missing work is an explicit uniform code-level implementation and its
calibration, not a new source arithmetic proof.

After that bridge, a fixed-control ground procedure can combine the two
compiled vectors, the accepted positive-coordinate test, the fixed
scalar-to-circuit compiler, and one fixed closed-block decider. One
ordinary partial-recursive evaluator then returns a Boolean on every
valid supplied policy and typed-term input. Alternatively, `smn` can
produce decision-program indices from policy indices. The stronger final
target must place the existence of this single evaluator/program
transformer **outside** the universal quantifier over policies.

The evaluator is allowed to diverge on invalid or nonterminating policy
codes. Totality on valid policy codes is a conclusion of the calibration
and existing total compiler. Requiring a universal evaluator that always
terminates on arbitrary alleged policy codes is unnecessary and would
confuse the statement with deciding whether a supplied program is total.

For joint near-control uniformity, separately expose a computable function
of `(b, encodedCircuitQuery)` calibrated to the concrete
`OriginalPrintedRawStageQuery.result (nearControl b) (b + 1)` with the
fixed rendering/high program. Existing per-`b` computability statements
must not be substituted for this joint statement. The control family and
high program are explicit, so this is an implementation-effectivity
bridge rather than a change to the arithmetic semantics.

All proposed targets above are specifications for follow-up work. No Lean
source or proof of them is supplied by this report.

## Source pins

Paths are relative to the repository root. These hashes identify the
definitions and printed scope read for this assessment.

| Path | SHA-256 |
| --- | --- |
| `17-permitted-control-canonical-comparison/paper.tex` | `12433b93cafb6e32dd497816e9e1bcfaba03b67ff0dc0a72fc6cdfd4f757415b` |
| `17-permitted-control-canonical-comparison/sections/arithmetic.tex` | `e1f9917e59dace6f57aba3014e83770bded6321ae29fc06d92e7affba31ddbab` |
| `17-permitted-control-canonical-comparison/sections/consequences.tex` | `db5ec55a8f5eb5748e6adc486d104551ab7059e32d11c0d470ad0aa80c453b23` |
| `17-permitted-control-canonical-comparison/sections/source.tex` | `cf441a8cc9544801b53c222ea136e7cc74d528d765012b2906d67d592f102c8e` |
| `formalization/LogicLineages/PermittedControl/ClosedBlockDecisionTargets.lean` | `56edf93074550b19ad73ed0c4002dd845aa95a8043340d2570e65989c82c1fb0` |
| `formalization/LogicLineages/PermittedControl/GroundComparisonTargets.lean` | `1c4d40201de55c3f03f145914bb44ccd75de641fc2b59038c09de9931b6e2d91` |
| `formalization/LogicLineages/PermittedControl/GroundComparisonMainTargets.lean` | `c3552aad4b8e882f9b507473da60d39081ca38256f321291670fb1e84329ac4f` |
| `formalization/LogicLineages/StandardControlCurrent/PolicyShapeDefinitions.lean` | `c1627852d10acb64fa0f8bae8ee07eb744b5c21d898c36818a5cba2d2bc9bee3` |
| `formalization/LogicLineages/OrdinalComparison/WWAdmissibleSumDefinitions.lean` | `39ce61dbe6a57b3443ded40ca5fb6218dcfc92ef609709185fcd297276b95073` |

## Subsequent checked continuation

After this source review, supporting records #1433 and #1434 implemented and
checked the proposed macro interpreter and the exact equivalence between
`PolicyShape.Effective` and existence of selector-realizing code. Their six
theorem aliases passed native receipt `1795394451020498412-12`, using only
`propext`, `Classical.choice`, and `Quot.sound`. The frozen scope maps and
append-only `LEDGER.md` preserve the sequence from proposal to checked result;
the source-review findings above are unchanged.

Uniform source compilation, the complete comparison evaluator, and joint
near-control effectivity remain follow-up specifications. No numbered statement
is promoted by this continuation. See `../HANDOFF.md` and
`../root/ACCEPTANCE.json` for the final checkpoint and evidence index.
