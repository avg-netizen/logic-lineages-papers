# Actual source-term graphs in the occurrence-row language

## Source boundary

This package supplies term introduction for paper08 `thm:snyatkov`, whose
literal source language is `Th(Nat;0,1,+,<,Phi)` with `Phi(n) = F5(n + 100)`.
It uses the existing `CommonLayerSyntax.BaseTerm`, its original variable names,
its actual arithmetic evaluation and its radix-4 encoding. The normal-form
rows and their semantics are the unchanged definitions accepted at the
[preceding checkpoint](../normal-form/SOURCE-CORRESPONDENCE.md).

The broader proof route and primary-source reading are recorded in the
[source contract](../../local-resume-2026-11-04-six-lanes/sol3-snyatkov/SOURCE-CONTRACT-AND-DEPENDENCIES.md).
This is a dependency of general source introduction. It does not eliminate
an arbitrary quantified block or establish the whole decision theorem.

## Concrete construction

Each occurrence in the source syntax receives one fresh natural-number name.
Names are allocated consecutively in postorder, including distinct slots for
repeated occurrences of the same original variable. Original variable indices
are copied without renaming. For a start name `s` and source term `t`, the
allocation is exactly the interval `[s, s + nodeCount t)`, and the last name
is the output slot.

The graph has one equation per occurrence:

| Source occurrence | Integer row equation |
|---|---|
| Numeral `n` | `z - n = 0` |
| Original variable `i` | `z - x_i = 0` |
| Addition | `z - x - y = 0` |
| Actual `Phi` | `z - Phi(x) = 0` |

Each equation is represented by nonnegativity of the row and its coefficientwise
negative. The nonlinear occurrence uses shift zero, so every graph occurrence
is meaningful at every natural valuation, including zero. This package adds no
tail restriction and does not discard domain metadata.

## Exact frozen obligations

| Target | Mathematical content |
|---|---|
| `ExactAllocation` | Positive node count, no duplicate allocated names, exact interval membership, and disjointness from original variables under the explicit freshness condition. |
| `ExactGraphSupport` | A name occurs in the graph exactly when it is an original source name or an allocated node name. |
| `OriginalGraphDomains` | Every original row and its negation are meaningful under every valuation. |
| `GraphSoundness` | Any valuation satisfying the graph gives the actual source-term value at its output slot. No freshness hypothesis is required. |
| `TotalGraphRealization` | Fresh allocation extends every original valuation to a satisfying graph valuation, preserves all names outside the allocation, and returns the original source value. |
| `AllocatedNodeUniqueness` | Graph valuations agreeing on source names agree on every allocated node. No freshness hypothesis is required. |
| `ExactExistentialGraph` | For fresh allocation, `t.value ν = y` is equivalent to the literal existential prefix over every allocated slot applied to the graph with output equation `z = y`. |
| `InstructionCodeCalibration` | The concrete radix-4 numeric instruction generator returns the actual typed postfix sequence, whose length is the node count. |
| `RowMachineCalibration` | The postfix machine produces exactly the typed graph rows and output stack, from every initial stack and list of prior rows. |
| `LiteralGraphCompiler` | The numeric package returns the exact encoded output name and graph formula. |
| `ActualNumericProgram` | Instruction generation, the complete row machine and the numeric graph package are primitive recursive. |

Freshness is the necessary explicit premise for realizing a graph without
changing original inputs: every original name must be below the chosen start.
The later formula introduction computes such a start from each atom's actual
source occurrences. Soundness and uniqueness do not assume this premise.

The generic existential-prefix/frame equivalence also permits repeated binder
names. It uses ordinary `Function.update` shadowing and proves that an
existential prefix is equivalent to choosing a valuation that agrees outside
its listed names. The graph allocation itself is duplicate free.

## Effectivity and remaining obligations

The numeric program is an actual stack machine over encoded occurrence rows.
Addition consumes the two child results in the correct left/right order;
the final row list retains postorder. Recursive decoding follows strictly
smaller radix-4 child codes. The primitive-recursion proof uses Mathlib's
course-of-values recursion and finite-list folds; it does not assume an
arithmetic oracle or semantic supplier.

The eleven targets are supporting results for the pending source theorem.
Source-formula introduction, full existential normal form, closure under all
elimination branches, decreasing quantified-block induction, inverse-boundary
assembly and first-order decision are distinct stages. The accompanying
[source-row package](../source-rows/SOURCE-CORRESPONDENCE.md) addresses the first
of those stages while retaining the original Boolean and binder structure.
