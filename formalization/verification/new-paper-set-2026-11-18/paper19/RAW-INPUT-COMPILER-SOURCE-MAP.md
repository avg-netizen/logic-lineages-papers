# Checked shared interleaved input compiler for paper19

The actual typed input is `InputNormalization.Input Γ 0`, with a literal
current source context and backward Boolean references. The raw code has
all six Boolean node tags, addition, a binary literal, ground observation
and a closed unary source call. A separate root index terminates the program.
The actual raw source-DAG codec carries observation/unary payloads, retaining
the full graph and backward references. The guards check indices, tag
arity and padding, actual source validity, exact free context and result
type, and closure of a supplied unary function.

Normalization stores a newest-first Boolean row table with two natural
port slots per node, in oldest-first slot order. New Boolean rows refer
to the two newest natural slots when testing natural terms. A later
natural declaration shifts every stored ground port once in the shared
context. Each arithmetic declaration contributes one entry to the
reverse lowering list, so construction of the arithmetic spine uses the
actual continuation-based binary compiler and the literal source equation
stages. This uses no expansion of the Boolean DAG or supplied source DAGs.

Typed exactness identifies the whole raw Plan with
`BooleanCompiler.lower (InputNormalization.normalize .nil q)`.
Every raw success reconstructs a complete valid typed input and its exact
Plan code. The executable validator and construction are jointly
Computable over all raw inputs. This supporting packet leaves the final
comparison pair composition and numbered theorem to the full source gate.
