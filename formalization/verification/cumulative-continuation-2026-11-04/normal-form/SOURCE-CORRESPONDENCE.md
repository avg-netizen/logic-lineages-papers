# Normal-form row semantics and literal compilation

## Source and frozen contract

This component continues the normal-form preparation in the proof route for
paper08 `thm:snyatkov`, the first-order arithmetic decision theorem for the
literal control `Phi(n) = F5(n + 100)`. The primary proof's normal-form and
elimination stages are identified in the preserved
[source reading](../../local-resume-2026-11-04-six-lanes/sol3-snyatkov/SOURCE-CONTRACT-AND-DEPENDENCIES.md).
The present component proves the row/domain/compiler interface specified
before the preceding pause; it does not assert that arbitrary source formulas
have already been converted to that normal form.

`FROZEN-TARGETS.json` pins the unchanged definitions and comparison types,
their complete local import closure, the manuscript, and the pinned package
configuration. The two restored files have the same hashes as the preceding
successful target-only preflight. The draft archive and its historical
unaccepted status are preserved.

## Exact mathematical content

| Frozen proposition | Content |
|---|---|
| `ExactOriginalDomainCutoffs` | Each variable, shifted `Phi`, or shifted `Phi(H(...))` occurrence is meaningful exactly above its computed cutoff. Both signed domains of a hyper occurrence are retained. |
| `ActualSignedRowDecomposition` | The integer value of a finite occurrence row equals its compiled positive natural part minus its compiled negative natural part. |
| `ExactOriginalRowDomains` | The conjunction of the original occurrence guards is equivalent to every occurrence being meaningful. Zero and cancelled coefficients do not remove guards. |
| `ActualAtomCompilation` | Nonnegativity and positive-modulus integer divisibility are equivalent to the actual expanded-matrix compilation. Divisibility uses the absolute value of the signed row. |
| `ActualBooleanCompilation` | Truth, falsity, atoms, negation, conjunction and disjunction preserve evaluation under the same valuation. |
| `ExactVariableMembership` | A variable name occurs in the output matrix exactly when it occurs in the input formula. This is membership equivalence; occurrence lists can have different multiplicities. |
| `LiteralCodeCalibration` | The concrete numeric item, cutoff, row, domain and Boolean programs return the exact codes of the corresponding syntax constructions. |
| `ActualNumericPrograms` | Item terms, item cutoffs, signed row parts, domain guards and atoms are primitive recursive; the total all-code Boolean compiler is computable. |

For the hyperfunction domain, `hyperThreshold` treats required values at most
`H(0) = 1` separately. Above that range, the proved floor-inverse inequalities
give the exact least admissible index. Neither a uniform tail assumption nor
an approximate bound is substituted for this equivalence.

Rows remain lists of signed occurrences. Repeated variable names and shifts
share one valuation, and all occurrences contribute to source-domain metadata.
The compiler does not impose a global domain guard across negations or
disjunctions: a caller inserts `domainFormula` at the required Boolean position,
and Boolean compilation preserves that position.

The numeric Boolean program has concrete leaf and recursive cases. Its
recursive child codes are strictly smaller than the input code, and its
assembly function is primitive recursive. Mathlib's `Primrec.nat_strong_rec`
supplies course-of-values recursion on the list of previously computed values.
This proves primitive recursiveness of the exact Boolean implementation, and
therefore the computability required by the frozen target. The program is total
even on malformed atom payloads; literal calibration is stated for actual
source encodings, as in the frozen target.

## Remaining source obligations

The full `EffectiveSourceExistentialNormalForm` proposition is still unproved.
Repeated-occurrence normalization and closure under every elimination branch,
the remaining domain and dominant-summand cases, the decreasing quantified-block
induction, inverse-boundary assembly, and arbitrary first-order BASE decision
remain separate obligations. The completed comparison consumers still require
that full solver.

These eight propositions are supporting results for the existing pending
paper08 source statement. They do not increase the numbered-source completion
count. Acceptance and native-check scope are recorded separately in the
checkpoint evidence; historical compiler success is not used as proof of the
new candidate files.
