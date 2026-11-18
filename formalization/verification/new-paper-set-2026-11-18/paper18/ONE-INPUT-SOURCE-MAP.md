# Complete current18 one-input quantified comparison

Proposal: u:cor:boolean, unary-decision.tex182 onward. Frozen expanded target
OneInputTargets.OneInputQuantifiedComparison. Candidate historical
OrdinalComparison.OneInputBoolean.full, not a conditional finite oracle.
No proof/native run/register promotion yet.

The source permits every finite Boolean combination of equality, weak order
and strict order between P1 expressions, with one shared positive input.
OneInputBooleanExpr has literal truth/atom/neg/conj/disj; relation codes are
equal/weak/strict. Each atom retains actual original FixedLimitPositiveExpr
with arbitrary fixed nonzero-limit heads below epsilon0, unrestricted nesting
and addition. Validity is only source grammar/head validity. No oracle-supplied
sign, common threshold, evaluation or eventual constancy is assumed.

oneInputBooleanCompile is explicit structural postfix compilation. Atoms
carry the two original positive-expression codes, and logical instructions
retain the exact Boolean structure. No new raw variable is introduced or atom
input made independent. encodedOneInputBooleanValue executes these original
source codes at each input. Its total computability and every-input equality
to actualOneInputBooleanValue are explicit target conjuncts.

The actual common tail takes the maximum of sign-decision moduli for all
atoms, at least1. The target proves constancy from that computed threshold,
not merely existence of some unspecified eventual sign. The closure program
evaluates positive points1,...,N inclusive, so N supplies the entire tail;
it does not omit the threshold point or include zero. Existential uses any,
universal uses all. Final biconditionals range over all positive inputs and
arbitrary formula negations/disjunctions, not only a single comparison atom.

Read OneInputBoolean.full and closures_correct: both outcomes are proved by
literal prefix membership and source-tail constancy; source_value calibrates
the postfix evaluator. The earlier complete eventual-sign and closed source
evaluation suppliers are real dependencies, not hypotheses. In particular
small inputs use original expressions, never auxiliary kernels outside their
raised genuine domains.

The expanded target unfolds the three old helper properties so the full
source statement and effectivity conditions are visible before reuse. This
is not multivariate polynomial Boolean comparison, free-parameter quantifier
elimination, or graph-domain composition. Independent pre-scope review,
native exact aliases, recursive evidence and final review are still required.
