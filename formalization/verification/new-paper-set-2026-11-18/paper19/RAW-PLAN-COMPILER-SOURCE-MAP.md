# Raw Plan compilation for paper19

This supporting comparator mirrors `ExistentialPlan.compile` over the literal
source DAGs and all four primitive gate forests. The spine uses a disjoint
sum of an equation's two raw source DAGs, a four-port raw gate instruction,
or a ground binder. The list terminator denotes `Plan.done`. The current
free context includes arbitrary type codes. The printed all-ground domain
will enter through normalization and lowering of the original input syntax.

A forward binder-only scan computes the last context. A right fold then
starts with the identity embedding and empty forest in that context.
A source equation validates both original contexts and result types and
uses checked raw renaming. A gate validates its ports in the current source
context, renames ports by the same embedding, and calls the checked actual
primitive gate forest in the tail compiler's context. Its nine fresh entries
shift the retained tail forest and original embedding as in the typed
compiler. A ground binder removes its source-context and embedding entry.
These folds are structural operations on finite syntax. Their raw successful
outputs must reconstruct the whole typed Plan, rather than selected sample
gates or expanded terms.

Exact source-Plan encoding, successful output reconstruction and joint
computability are paid separately. The entire arithmetic/Boolean input
normalizer and the final comparison pair assembly remain open.
