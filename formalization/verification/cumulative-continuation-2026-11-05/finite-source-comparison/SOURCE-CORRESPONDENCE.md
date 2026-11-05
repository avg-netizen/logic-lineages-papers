# Native acceptance notice

The source-match review below was completed before the native verification. Its original pending-native wording is retained as historical review context. See [component acceptance](ACCEPTANCE.json) and the [passed native verification](NATIVE-VERIFICATION.json) for the subsequent result.

---

# Paper 08 finite-coefficient source comparison: source-match review

## Review status

This is an independent source-contract review of the proposed
`FiniteSourceComparisonStatementChecks.full_finite_source_comparison` gate.
It is not native acceptance. The new literal-condition bridge, admissible-domain
bridge and final gate still require the coordinator's native statement checks,
source-bound receipts and actual axiom audits. No numbered source promotion or
cumulative-build result is asserted by this document.

Source: `08-multivariate-collapse-comparison/paper.tex`, theorem
`thm:finite-source`, lines 202–234; finite-head identity at lines 193–200.
The reviewed source SHA-256 is
`a4a8481437b8c7683ee8d82ec9e13e0a29af44110edcace0e9b0ef31b8fdaf0d`.

All declaration prefixes below are relative to
`LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion`
unless a different namespace is given.

## Clause-by-clause correspondence

| Printed source clause | Exact formal interface |
| --- | --- |
| Two original well-typed T terms of the same type, with ground free variables (lines 203–204) | `FiniteSourceComparisonTargets.OriginalComparisonDecision` quantifies `a b : OriginalTerm Γ τ` and `∀ σ ∈ Γ, σ = Ty.ground`. The actual source type, context and term codes are retained. |
| Compute their canonical assignments (line 204) | The conclusion supplies `av` and `bv` with equations for `AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a` and the corresponding assignment of `b`. Assignment success is proved, not a premise. |
| Every literal zeroth-coordinate collapse has a closed finite-valued coefficient (lines 205–206) | `LiteralFiniteSource.finiteSource` requires an actual assignment and `finiteCollapseCoefficients (v 0)`. The specification contains no scalar-compiler-success premise. |
| Universal weak, WW-strict and equality comparisons are decidable (lines 206–207) | `OriginalComparisonDecision` relates the actual universal WW admissible-substitution relation to the output of the total Boolean `FiniteSourceComparison.decide`. `TotalNumericDecision` states its `Computable` property. |
| Every recursor-free such term passes, without an internal-type bound (lines 207–208, 227–230) | `LiteralFiniteSourceTargets.RecursorFreePasses` proves both the literal source condition and acceptance by the actual source-code test from `SourceClasses.recursorFree e = true`. There is no bound on internal types, binder types or result-type level. |
| Closed coefficient evaluation and finite traversal terminate (line 233) | `LiteralFiniteSourceTargets.ExactSourceTest` gives the exact admission test on genuine typed original terms; `Computable LiteralFiniteSource.Code.acceptsSource` supplies its effective implementation. The finite coefficient evaluator and literal source pipeline are the existing calibrated suppliers. |

The final frozen `FullFiniteSourceComparison` is the conjunction of the exact
source test, recursor-free inclusion, computability of admission, total numeric
comparison and the original comparison-decision theorem. The final gate aliases
that whole proposition; it is not only a conditional theorem with an unproved
decision supplier.

## Literal coefficient condition

`collapseHeads` traverses the unchanged `OrdinalExpression` syntax. At every
`.collapse a b`, it records `a` and visits both children. It also visits both
children of `.add` and `.emul`. It performs no normalization, cancellation,
erasure of zero occurrences, or replacement by a semantically equal expression.

`finiteCollapseCoefficients` requires each recorded original head to have the
empty original variable list and to denote an ordinal below `Ordinal.omega0`
under every ordinal valuation. The universal valuation is harmless for a
closed expression and makes the condition independent of an arbitrary chosen
environment. The condition is applied only to coordinate zero of the computed
canonical assignment. It does not require all positive vector coordinates to
be finite.

`LiteralScalarCorrespondence` identifies this original-syntax condition with
`SemanticFiniteScalar.finiteHeads` after the existing scalar extraction.
`ClosedCoefficientExtraction` supplies the exact closedness, absence of nested
collapse nodes and denotation of every successfully extracted coefficient.
Consequently, the extra recursive traversal into a recorded coefficient does
not impose an additional restriction on an actual extracted source head:
that coefficient subtree has no collapses. Canonical source extraction is
already proved to exist for every original term with ground free context.

This preserves semantic finiteness of the original closed coefficients. It
does not replace finiteness by a syntactic prohibition on Omega or use an
arbitrary input environment to decide what a closed head means.

## Natural arithmetic and the scalar translation

At the original source interface, a collapse node denotes
`actualCollapse (ordinalNaturalSum (ordinalNaturalProduct omega0 c) g)`.
The coefficient product is the original natural product `omega0 ⊗ c`.
It must not be replaced by ordinary ordinal multiplication for a general
coefficient. The accepted scalar-translation theorem retains that natural
product and uses the proved finite-right-tail identity to replace the natural
sum by the printed ordinal `+` when the scalar tail is finite.

Closed coefficient evaluation also preserves the original operations:
`ClosedPositive.emul a b` denotes genuine ordinal `2 ^ a` followed by natural
product with `b`. It is not natural exponentiation or multiplication of
variable natural inputs.

When the complete semantic recognizer returns the actual finite value `k`,
the existing `naturalProduct_omega_finite` theorem identifies `omega0 ⊗ k`
with `omega0 * k`. `actualFiniteHeadCollapse` and the checked finite expansion
then give the literal identity

\[
\psi(\omega k+n)=\Phi^{k}(n+2k)+k.
\]

The output contains `k` literal Phi applications. The iteration count is a
closed integer computed from the original coefficient, not a variable-seed or
variable-depth operator in the target language. The exact control remains
the existing `Phi`, calibrated to `F_5(n+100)`; no control function is changed.
`SemanticFiniteScalarProof.actualScalar` retains each original scalar value
and the exact original variable list under this translation.

## Genuine WW admissible ground substitutions

The final theorem quantifies `Source.OriginalDomain.AdmissibleSubstitution Γ`.
These are actual closed graded vectors with the original bounded-norm condition,
as defined independently in `WWOriginalDomainDefinitions.lean`. The domain is
not a new structure with positivity, finiteness or the desired comparison
equivalence inserted as fields.

`GroundAdmissibleComparisonTargets.ExactGroundValuations` pays both directions
of the source argument at lines 222–225. Every ground name has one coordinate.
The existing `originalClosedScalarFinite` and `originalClosedGradePositive`
theorems extract its positive natural value. Conversely, the literal closed
Add/One numeral in `UnitObservation.substitution` realizes every positive
natural value. Its grade is proved by construction; its boundedness condition
is reflexive for the sole ground coordinate. Distinct names keep their distinct
original identities, and repeated occurrences keep the same value.

This concerns admissible closed ordinal-expression substitutions. It does not
assume that every such substitution is the canonical assignment of a closed T
term, and no such assumption is needed by the printed comparison relation.

The established support convention is also retained. The independently proved
`Source.OriginalDomain.originalSupportComparisonBridge` identifies comparison
on exact occurring-name substitutions with the total-context interface used
here: unused names extend by One, and restriction preserves the compared
expressions. Requiring total context functions introduces no coupling or
extra constraint on the occurring ground names.

`GroundAdmissibleComparison.vectorAtValue` evaluates each original
`ordinalVectorAt` expression, including its literal Zero padding.
`VectorRelationAt` and `UniversalComparison` transport the entire relation
between the original substitution domain and the positive-natural domain
used by the scalar compiler. This argument is valid for arbitrary ordinal
vectors, so it does not assume a finite coefficient or closed positive
coordinate in order to prove the domain bridge.

## All comparison modes and positive coordinates

The mode convention is the existing numeric API:

| Mode | Original relation |
| --- | --- |
| `0` | Weak inequality at coordinate zero and at every positive coordinate. |
| `1` | Strict inequality at coordinate zero, with weak inequality at every positive coordinate. |
| Every other natural code | Equality at every coordinate. |

The actual canonical positive coordinates are closed and are evaluated by
the existing compiled-vector and closed-ordinal suppliers. The existing
`positiveFlag` uses their actual values, preserves Zero padding, and requires
both weak directions for equality. WW-strict is not strict in every
coordinate, and equality is not merely equality of the scalar coordinate.
The two terms share the original variable-index map throughout.

## Effective class admission and comparison

For an actual original term in an all-ground context,
`ExactSourceTest` identifies the executable source-code test exactly with the
independent literal source condition. The test runs the canonical assignment,
existing vector extraction and complete semantic finite-coefficient compiler.
An assumed successful compilation is not part of the theorem's input.

`FiniteSourceComparison.decide` is a total Boolean function on the existing
four-field natural-code input. It obtains the result of
`SemanticFiniteVector.Code.decideSource` and supplies `false` only as the
`Option.getD` fallback. On every admitted pair of genuine original terms,
the decision theorem proves that the option is `some answer`, so the fallback
cannot determine the result there.

The exact admission equivalence is stated on genuine original typed terms.
This component is not a new specification of every malformed raw-code case.
A failed admission test, or the total Boolean fallback outside the admitted
class, is not a certified negative answer to an unrestricted source comparison.
The source statement is a decision theorem on its stated finite-coefficient
class.

## Arithmetic supplier and completion boundary

After finite expansion, the scalar comparison is a quantifier-free Boolean
BASE formula with arbitrary finite fixed Phi nesting. The explicit guard
requires each original free ground input to be positive; the formula is then
universally closed. The existing `BaseBooleanSource` exact closure-decision
theorem covers this fragment, including arbitrary Boolean polarity and shared
input names. There is no unproved BASE oracle among the final target's
premises.

The paper invokes the stronger first-order Snyatkov theorem in its proof.
For this particular source theorem, the already available universal closure
of quantifier-free Boolean BASE supplies all required arithmetic instances.
The proposed finite-source gate therefore does not assert or promote the
still-separate full first-order BASE theorem, quantifier elimination,
unrestricted bound-dependent Phi alternation, or arbitrary canonical
comparison outside the finite-coefficient class.

The source-match review finds that the proposed whole target preserves the
printed finite-source domain, all three relations, the actual computation
claim and the recursor-free clause. Native checks and axiom acceptance remain
separate pending obligations of the coordinator.
