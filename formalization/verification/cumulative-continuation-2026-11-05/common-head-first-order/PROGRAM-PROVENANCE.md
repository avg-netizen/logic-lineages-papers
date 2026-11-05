# First-order code compiler provenance

The new typed AST is only a source presentation: each atom records its original
finite head list and original CommonSyntax operands. Its raw radix-five encoding
stores the exact accepted comparison input tuple, followed by standard Boolean
and binder constructors. Atoms may have different head lists and depths.

The numeric compiler is total on every Nat code. At atomic tags it decodes the
comparison payload with the stated default, invokes the actual checked exact-support
common-head output program, and invokes the literal existing BASE-to-SourceFormula
code compiler. It never evaluates an input valuation or decides source truth.

At other tags it recursively compiles exactly the original child codes and writes
the existing SourceFormula constructor codes. Positive existence writes an ordinary
Nat binder around the conjunction 0<x and the translated body. The added variable
occurrence is bound immediately. Nat existence has no positivity condition. Each
recursive child code is strictly smaller than its parent; a checked finite graph
with this measure supplies actual Computable compilation, not a termination oracle.

Exact source semantics require only the original genuine-head certification at each
atom. Exact syntax support and literal calibration do not assume a semantic solver.
The compiler may vastly expand formula size; no complexity bound is asserted.
