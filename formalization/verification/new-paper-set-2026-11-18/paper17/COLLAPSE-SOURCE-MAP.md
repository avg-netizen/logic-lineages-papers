# Actual selected-control collapse correspondence

Paper17 foundations `def:collapse` takes a finite maximum including zero over
strict predecessors whose additive hereditary norm is at most f(N(alpha)).
Existing `ParametricActualCollapse.collapseWith f` uses ordinal well-founded
recursion with exactly that predicate. The finite supremum on Nat includes
zero as bottom. Its outside-epsilon-zero totalization is never part of the
new theorem domains. `ParametricActualCollapse.Proof.equation` gives both
maximum inequalities and `uniqueBelowEpsilonZero` proves uniqueness. These
must enter the checked native recursive closure; they are not assumptions.

`actualOrdinalNorm` is the pre-existing actual hereditary-CNF additive norm,
with notation correspondence established independently. `actualBoundedPredecessors`
filters its finite norm ball by strict ordinal order. `actualMaximumPredecessor`
is the finite supremum of that actual set, not a new selected-control oracle.
The existing correctness, saturation and strict-in-budget results are independent
of f and can be reused after the transitive native evidence is reconciled.

The old `ActualSinglePredecessor` proof is mathematical guidance only: its
conclusion uses the unchanged Phi collapse. New targets use `collapseWith f`
throughout, require StrictMono f and G-majorization, and have separate explicit
concrete clauses for fStar and every nearControl b. StrictMono for these
controls follows from the proved exact double-exponential step, not merely
from majorizing G. No equality with the Phi assignment is claimed.

The full printed finite-tail bound is psi_f(alpha)+k <= psi_f(alpha+k).
The older ActualCollapseFiniteTailBound only says k<=psi(alpha+k), so it
cannot discharge this clause. A fresh induction will use the bounded-predecessor
maximum equation and the exact additive norm of finite tails.

The full single-predecessor statement uses M(lambda,f(N(lambda)+n)) with
lambda the nonzero limit part. Its induction must handle predecessors below
lambda and those in the finite interval separately, with strict growth of f
and actual limit saturation handling the latter. No global monotonicity of
collapse on arbitrary ordinal arguments is assumed.

These targets are semantic equations/estimates on actual ordinals. Reusing a
noncomputable ordinal recursion does not prove a computable closed evaluator.
The algorithmic closed-evaluation corollary, norm orbit, counts and entry
residues remain separate obligations.
