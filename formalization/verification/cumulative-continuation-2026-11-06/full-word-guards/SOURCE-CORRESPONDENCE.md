# Exact source correspondence

The target is paper 08, `lem:guards`, “Ordered maximum-variable guards,” in
`08-multivariate-collapse-comparison/paper.tex`. The baseline is commit
`2066300c16197fc71dc30c87d61fb6bb11eadd9b` on
`formalization/joint-gamma-quotient-paths-2026-11-06`. This baseline contains the
integrated local guard work and the subsequent joint-Gamma proofs.

## Literal inputs and output

The input words use the existing `PolynomialGraphCompletion.Word` encoding and
its unchanged `WordAllowed`, `WordDomain`, and `wordValue`. The alphabet contains
arbitrary signed shifts, Phi, signed quadratic kernels, signed scheduled kernels,
and scheduled counters. The whole-source target quantifies over every finite
degree `D >= 3` and every pair admitted by that literal source grammar.

`compile D (A,B)` has no raw numeric arguments. It computes a common cutoff, one
word-linear row, three finite Boolean guards, a same-variable outcome, and the
finite trace of original/generated word pairs. Original variable names are zero
and one. The row's occurrences of zero have the identity word; nonempty words
can occur only at one. The three Boolean guards are finite disjunctions of the
row's negative, zero, and positive sign atoms. An empty disjunction is false.

| Printed obligation | Frozen target |
| --- | --- |
| Effective common tail and all syntax computed before its use | `CompilerCalibration`, `BoundedCompilerPrograms`, `CompilerProgram` |
| Actual original and generated-word domains on that common tail | `CompiledDomains` |
| Original maximum variable occurs only linearly; words occur only at the other original variable | `CompiledSyntax`, through `LinearInMaximum` |
| Exact strict, equality, and reverse-strict guards under `y <= x` | `CompiledThreeWay` |
| Effectively decided comparison at the same original variable | `CompiledSameVariable` |
| All clauses together | `FullWordGuards` |

## Finite selected chain

The existing canonical selector has seven forward cases and their reversed
orientations. Each accepted local theorem preserves strict child order and
resolves only child equality by a fixed comparison of its source parameters.
The dispatcher therefore uses a three-valued tie map. Reversing a local theorem
reverses that map while retaining the original left/right variable positions.

The runner follows the selector's actual child, not a separately proposed call
graph. Every admitted selected child decreases the existing lexicographic
measure: counter count, then the finite reverse-rank histogram. No expression
length bound or new analytic estimate replaces that source measure. The
accumulated cutoff pays each processed local guard and every current original
word domain. The accumulated tie composes in the same order as the literal
selected comparisons.

All bounded syntax operations are primitive recursive. The complete compiler
uses ordinary total computability: the explicit least-stopping search is proved
to terminate by the actual child measure and is implemented through
`Computable.find`. Invalid raw codes stop at zero and return the stated fixed
package. No unproved semantic decision procedure is a premise.

## Terminal and same-variable cases

If the left word is all shifts, the emitted row is
`shiftSum A + x - wordValue B y`. Original shift domains are paid before applying
the one-way normalization theorem. If the left word is nonlinear and the right
word is all shifts, the already accepted nonlinear-growth threshold makes the
left value larger under `y <= x`; the emitted row is the positive constant one.

For the same-variable clause, two shift-only words compare by their signed shift
sums. A nonlinear word eventually exceeds a shift-only word in either
orientation; the reversed growth payment is included explicitly. The final
answer applies the accumulated tie to that constant terminal outcome.

## Frozen-target revision

All eight definition/target/preflight files were frozen before candidate proofs
and passed a 123-module native preflight. The first Boolean helper proof exposed
a precedence error in its auxiliary specification: without an outer pair of
parentheses, Lean parsed the input outcome bound as part of the left side of an
equivalence. V1 is preserved in `FROZEN-V1` and `FROZEN-TARGETS-V1.json` with the
failed candidate and native receipt. V2 adds the intended parentheses and passed
native preflight before that proof resumed. The source target `FullWordGuards`,
all definitions, and every dispatcher/runner target are byte-for-byte unchanged
by this revision. No source domain, constant, premise, or conclusion was weakened.

The ranked row-cancellation lemma, closed existential decision, arbitrary
first-order BASE, and internal-level-two consumer are separate obligations.
