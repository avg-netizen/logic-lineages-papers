# Source formulas to quantified occurrence rows

## Fixed source and output syntax

The input is the existing `SnyatkovCompletion.SourceFormula`: equality and
strict order of arbitrary actual source terms, negation, conjunction and
ordinary named existential binding. Its semantics, radix-5 encoding and
free-variable membership are unchanged. This is the literal first-order
source language used by paper08 `thm:snyatkov`.

The new `SourceRows.QFormula` permits an existing normal-form Boolean matrix,
negation, conjunction and named existential binding. It is an intermediate
quantified row language. Translation retains every original negation,
conjunction and binder at its original structural position. An atom is replaced
by a finite existential graph construction at that position.

This output is not the single existential prefix required by the older
`NormalFormTargets.EffectiveSourceExistentialNormalForm` proposition. In
particular, source negations can still contain introduced witness blocks.
The decreasing complement-elimination induction needed to remove such blocks
remains a separate obligation.

## Local atom introduction

For operands `a` and `b`, the fresh start is one above the largest original
variable index in either operand, or zero if neither operand contains a
variable. It is computed by scanning the concrete postfix instructions. Names
bound by surrounding source quantifiers are included whenever they occur in
the atom; they are not omitted merely because they are globally bound.

The graph of the joined term `a + b` records both operand computations and one
additional final sum slot. The comparison uses the two child output slots.
The sum slot is a total auxiliary witness, not the compared source value.
Every graph slot is bound locally within the atom.

For output names `x` and `y`, equality is the row equation `x - y = 0`.
Strict order is the row inequality `y - x - 1 >= 0`. The constant `-1` is
retained, so the compiled relation is strict order on naturals. All graph and
comparison occurrences have shift zero and are meaningful at every natural
valuation.

The exact frame theorem for term graphs proves both directions of the atom
equivalence. Total realization supplies witnesses while preserving original
inputs. Conversely, a satisfying graph determines the two actual operand
values under that same original valuation.

## Exact frozen obligations

| Target | Mathematical content |
|---|---|
| `ExactLocalAtomIntroduction` | Every equality or strict-order source atom is equivalent to its literal local graph construction under every original valuation. |
| `ExactSourceIntroduction` | Every source formula, including arbitrary nesting and binder shadowing, is equivalent to its concrete quantified-row translation under every valuation. |
| `ExactFreeVariableMembership` | A natural-number name is free in the output exactly when it is free in the original source formula. Multiplicities in occurrence lists need not agree. |
| `LiteralSourceCompilerCalibration` | The total numeric compiler applied to the original source encoding returns exactly the encoded typed translation. |
| `ActualSourceNumericProgram` | The concrete all-code source compiler is primitive recursive. |

Free-variable preservation is exact membership equivalence. The graph's
support consists of original names and allocated names; the local binders
remove exactly the allocated names. Source binder filters are then preserved
structurally. Witness names can be reused in distinct atoms because their
scopes remain local. A surrounding binder absent from an atom's operands need
not be reserved by that atom's allocator.

## Literal numeric implementation

The implementation computes source instructions, a variable-index bound,
postfix graph rows, the comparison row, and the finite sequence of witness
binders. Typed calibration identifies all of these with the exact syntax
constructors, including the child output indices and original binder names.
The complete source recursion follows the original radix-5 tags and strictly
smaller child codes. No source evaluation or truth test is assumed by the
compiler.

These five targets, together with the
[eleven term-graph targets](../source-term-graph/SOURCE-CORRESPONDENCE.md), pay the
general source term/atom introduction step. They retain arbitrary Boolean
positions rather than moving existential witnesses through negations.
The full existential normal form, source-restricted closure of every
elimination branch, decreasing quantified-block induction, inverse-expanded
elimination and first-order BASE decision remain pending. The whole numbered
source register therefore receives no promotion from this package.
