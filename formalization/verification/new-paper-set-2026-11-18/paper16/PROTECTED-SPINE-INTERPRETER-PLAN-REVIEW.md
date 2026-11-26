# Protected original-spine interpreter conceptual review

Read the plan, literal SpineSyntax Expr/Args/substitute/applyAux/apply, decision.tex structural interpretation statement/proof, and current MarkedFamilyCoherence predicates. Approve the call-local protection and structural-recursion direction for concrete design, subject to the exact obligations below before a full source comparator is accepted.

## Protection and residual reset

The empty-tuple reset is correct and necessary: actual applyAux with no arguments returns ordinary simultaneous substitution, while a later apply begins with an empty consumed-values list. Protection therefore belongs to the current original call, not permanently to an abstract residual value. A newly consumed binder blocks with remaining arguments even when its assigned image looks functional. A pre-existing ambient substitution or free image uses its whole remaining-tuple table. Never identify a full original call with staged calls, or transport undefinedness from the unsubstituted free variable. The final concrete correspondence must state the original scan, concrete simultaneous substitution, argument typing and reset precisely.

The nonempty helper avoids the obvious same-source interpret/helper empty case cycle. Freeze a genuine mutual size measure and every cross-call: interpreter lambda table starts at the original body, helper lambda descends original body, head/base/extras recurse only into original children. Table reads must be finite already-constructed value lookups, not recursive calls inspecting replacement syntax. Arg-list source-size descent and residual type consumption must remain explicit.

## Fresh opening is a substantive unresolved obligation

Current retained families enforce monotonicity and extension coherence, not an explicit permutation-equivariance field. Finite renaming of observations/environments/M coordinates is not automatically independence under the SAME arbitrary M. Do not assume that arbitrary retained M is invariant under a fresh-port permutation merely from (C), and do not add that as an unapproved final premise. The next exact design must explain whether coherence through a common extension plus fixing all relevant inputs proves the required equality, or provide actual equivariant transport of the family and a justified way back. If that cannot be proved for the existing carrier, report the obstruction before freezing a falsely unconditional freshness/naturality theorem; a silent restriction of M changes the operator domain.

Target-observation budget must supply an actual spare typed port. Finite support includes both endpoints, source environments, observation and family coordinates used; source lambda depth alone is insufficient. Extension can occupy the old canonical port, so naturality must compare different choices. Off-schema defaults cannot discard any legal observation. Variable values themselves need full Valid proof, with literal matching weak bits, strict false, whole-bottom nonempty tables.

## Full source obligations

Ordinary Fun is positional and typed, not an unordered-base test. Marked coordinates retain original head/result/context, all bases and tagged downclosed extras. Every optional lookup/encoding failure is excluded on source inputs; source inventory discharges local interfaces. Monotonicity, weakening and capture-avoiding substitution must be simultaneous real syntax/helper proofs, not a supplied generic semantic function. Concrete substitution correspondence distinguishes consumed original binders from pre-existing images and proves both successful and undefined applications.

Proceed with executable definitions/equations and a precise opening-coherence design before exact target review. This conceptual approval does not pay freshness, interpreted-value validity, the four positive constructor operator tests, endomap, fixedpoint or adequacy.
