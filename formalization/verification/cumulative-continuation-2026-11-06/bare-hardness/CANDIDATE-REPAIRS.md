# Preserved preflight and proof repairs

All raw receipts are retained. No source definition, target quantifier,
admissibility condition, depth bound, comparison relation, or compiler resource
limit was weakened.

| Receipt | Finding | Exact repair |
| --- | --- | --- |
| `1793929772899097808-2` | The official cached object for `Mathlib.Algebra.MvPolynomial.Eval` was absent. | Acquired the pinned upstream import closure from the official cache; no source or compiler change. |
| `1793929833801694323-2` | New target definitions referenced `REPred` without its defining import. | Added `Mathlib.Computability.RE`, preserved the initial target snapshot and freeze, and renewed the freeze before any candidate proof. |
| `1793929930030885176-2` | Complete target preflight passed. | Candidate proof authoring began only after this success. |
| `1793930255707492144-2` | Typed expression-code injectivity retained a lambda application in a rewrite hypothesis. | Exposed the exact encoded-expression equality with `change` before rewriting. The MRDP and program gates already passed in this receipt. |
| `1793930290232965772-2` | An option-valued evaluation left a definitional computation; backward inference for a computability composition exhausted the existing heartbeat allowance. | Closed the option computation with `rfl` and gave the computability projections explicit types. |
| `1793930383347728605-2` | The expected-type-directed computability composition still unfolded the evaluator during inference. | Specified both functions of `Computable.comp` and inferred its result before applying it. The unchanged upper-bound proof then passed in `1793930476360195825-2`. |
| `1793930361406662808-2` | Vector reduction rewriting encountered the unreduced application of its chosen function. | Added an explicit beta-normalized `change`; made the corresponding normalization explicit in the scalar assembly. |
| `1793930441248980282-2` | Rewriting an entire raw-code goal generalized the arity on which its typed expression witnesses depend. | Transported only the scalar comparison proposition through `congrArg` and `iff_of_eq`, retaining the original typed witnesses. |
| `1793930511644755998-2` | Whole scalar, vector and final coordinator gates passed. | Both source endpoints and all final aliases use only the standard three axioms. |

`candidate-snapshots/initial` retains every initial candidate proof. The
intermediate upper-bound and vector candidates are retained in their named
subdirectories. `preflight-repairs` retains the original missing-import target
and freeze. Additional historical failed receipts selected by the evidence
collector concern shared dependencies from the prior uniform checkpoint and
remain historical evidence; this continuation did not modify those sources.
