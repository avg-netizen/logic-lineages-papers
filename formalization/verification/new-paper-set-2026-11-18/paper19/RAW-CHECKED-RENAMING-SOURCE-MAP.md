# Checked source-DAG renaming for paper19

The printed compiler retains the valuation of shared inputs and source leaves
when assembling the comparison. Its typed implementation uses
`ScopedDAG.renameInput` to move source inputs to the compiler's shared context.
This supporting comparator covers the checked raw entry point for that exact
operation with the existing literal `Operations.renameCode` table format.

The source and target contexts are lists of type codes. The renaming table has
one entry per source context position, in context order. Each index must be
in range in the target and carry precisely the corresponding source type.
`tableGuard` consumes one table entry per source type and requires the
remainder to be empty. Thus incorrect unused entries also fail. Empty source
and empty table are compatible for every target. Repeated target indices are
permitted; equality of source and target types is checked at each index.

The input graph must pass the actual shared-DAG validator. Every compatible
typed input and renaming has literal output-code equality, and every arbitrary
raw success reconstructs the exact typed input, renaming table and context,
output and dependent decode. Success preserves the graph's table length and
the exact root and result type, including for higher-type inputs. Computation
is the finite scan followed by the existing raw transformation. The proof of
typed reconstruction supplies evidence about that computation.

Whole-compiler valuation preservation, primitive gate construction and
numbered-statement promotion are separate obligations.
