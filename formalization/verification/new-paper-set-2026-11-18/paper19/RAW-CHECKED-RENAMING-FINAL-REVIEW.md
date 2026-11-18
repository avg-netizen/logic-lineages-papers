# Independent final review: checked source-DAG renaming (root, local continuation)

Accepted as a supporting five-contract endpoint. Reviewer: root of the local
three-party continuation (not the lane B author). No reviewer native run.

Comparator scope (read in full, since this target was frozen locally by the
lane): `rename` is the existing literal `Operations.renameCode` behind an
explicit guard (actual shared-DAG validator plus `tableGuard`). `tableGuard`
consumes exactly one table entry per source context position and requires an
empty remainder; TableExactness is a genuine iff against existence of a typed
`Renaming Γ Θ` with that code, so over-long tables and ill-typed or
out-of-range indices are rejected and repeated target indices are admitted.
TypedExactness is literal output-code equality for every typed input and
renaming. SuccessReconstruction starts from an arbitrary raw success and
returns the typed input, contexts, renaming, output code and its decode; no
caller-supplied witness or successful-decode premise appears. Rejection is an
iff with guard falsity; counts give validity, target context, table length and
root/type preservation. Effective claims Computable for the total Option
routine, not primitive recursion. The comparator is not satisfied by a
definition engineered to make it true: the operation, validator and codec are
the previously frozen ones.

All eight frozen pins recomputed and match. Compiler-free recursive evidence
reproduced independently and JSON-identical to the author's file: 147
source-matched modules, zero errors, five exact aliases on propext,
Classical.choice and Quot.sound only. Dedicated gate 1795032365894084226-60;
proof receipt 1795032287190816372-124. No unsafe, opaque, implemented_by,
extern or partial in the packet's Lean files.

Whole-compiler valuation preservation, primitive gate construction and any
numbered statement remain separate. No full-root or CI claim.
