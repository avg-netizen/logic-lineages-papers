# Raw source-DAG lowering for all four primitive arithmetic gates

The paper19 compiler uses equality, addition, sorting and arithmetic one
when flattening arithmetic and compiling Boolean nodes. This supporting
packet covers the actual `PrimitiveLowering.forest` in the shared-DAG
implementation. It introduces a distinct code with one tag and four port
slots. Sort carries all four slots. Zero denotes the zero port and successor
of a variable index denotes the corresponding ground port. Every referenced
index is checked against the original encoded context. Unused slots must be
zero and unknown tags fail.

All four outputs prepend the actual nine ground coordinates. Outgoing
equation order and fresh indices follow `PrimitiveLowering.lower`, including
the equations for unused coordinates. The successor, eraser and identity-zero
tables preserve the exact vertex orders of `PrimitiveLowering.Expr.graph`.
Each successful call produces the ten actual ground equations as raw codes
with the same encoded enlarged context. Typed calibration and arbitrary raw
success reconstruction refer to the same literal forest and its actual decoder.

This packet pays concrete joint computability of local gate lowering.
Plan recursion, interleaved-input normalization and the whole source
compiler are separate.
