# Original08 single-core consumer: actual formalization plan

This is an implementation plan, not an accepted theorem or numbered promotion.
Paper07's entire actual sign procedure is checked; use it rather than inventing
an arithmetic decision oracle for the interior core. Source08 §10 explicitly
allows arbitrary nested positive cores, not only affine cores. Read the original
source before changing the target.

The desired complete source target remains thm:single-core. A row has actual
integer coefficients K,r,q_i, fixed nonzero limit notes lambda_i, natural
positive a_i and nonnegative c_i. Its actual value is
K+r*E(rho)+sum_i q_i*h_lambda_i(a_i*E(rho)+c_i).
The interior core is the actual MultivariatePositiveExpr grammar. Fixed
nonnegative multiples expand by literal repeated addition, with zero yielding
the constant0 tree. All original variable indices and repeated occurrences stay
shared. No exposed f constructor or subtraction is added inside E.

First supplier SingleCoreSupport*: literal input-leaf list (duplicates retained),
uniform numeric Primrec support compiler, actual support bounds, value
independence off support and dominance rho(i)<=E(rho) for each supported i.
Head dominance is actualFixedLimitProfileHeads, not a supplied growth field.
This is useful for the actual finite box and is NOT yet full thm:single-core.

Complete row algorithm:

1. Form actual one-input positive expressions P,Q for the positive/negative
   parts of K+r*t+sum q_i*h_lambda_i(a_i*t+c_i). Use explicit repeated addition
   (zero multiplicity is constant0), not integer-valued positive syntax.
   Compute the genuine raw expression codes uniformly from the numeric row.
   Prove actual row = (eval P t : Int)-(eval Q t : Int).
2. Run the accepted actual sign decision on (.positive P,.positive Q). Its
   computed sign sigma and N>=1 describe every formal t>=N. This does NOT
   assume that the actual core ranges freely or surjectively over naturals.
3. Extract actual support V of E, allowing duplicates. For any original positive
   valuation with some rho(i)>=N, support dominance gives E(rho)>=N, hence the
   actual row has sigma. All remaining supported values lie in [1,N-1].
4. Enumerate the FINITE list of all length-|V| words in [1,N-1]. For each word,
   form the conjunction of original-variable equations rho(V_j)=word_j.
   Inconsistent duplicated occurrences simply produce false clauses; for any
   satisfiable clause, first-occurrence lookup agrees with the original
   valuation at every supported variable.
5. Evaluate E and the row EXACTLY for that lookup valuation (default1 off V),
   retaining clauses with the requested sign. Add the tail disjunct
   ((exists i in V, rho(i)>=N) AND [sigma=desired]). This is a literal finite
   Presburger DNF using only the ORIGINAL variable indices and constants.
   Empty support needs no special assumption: the box has one empty word,
   tail disjunction is false, and the exact closed row decides the sole clause.
6. The full target must include a genuinely total Computable numeric compiler
   producing the actual finite Presburger syntax, code/semantics agreement and
   exact sign equivalence for EVERY positive original valuation. No supplied
   support, evaluation, sign, enumeration, compiler-success or independence
   premise. Only then promote the whole numbered source theorem.

Numeric core evaluation can reuse actual instantiateScalarCode xs n followed
by the checked total encodedPositiveFoldValue. Prove its structural correctness
for ALL actual MultivariatePositiveExpr trees (do not rely on Scalar.head's
restricted source-origin grammar). A tuple length code(E)+1 suffices once the
support code bound is paid. Store raw entries lookup(i)-1 so the existing
successor-positive tuple convention produces the desired values. The finite box
uses only positive values and default1; all exact evaluations are total.

Whole original07 is locally closed in PROMOTIONS.json (identity/sign/Boolean/
sourceeq/final typed-source corollary). Root alone reconciles global register and
accepted imports. Do not alter its TerminationOrdering namespace, source papers,
old accepted hashes, shared compiler, TARGETS or Git. Continue bounded checks
through scripts/check.py with the explicitly measured profile and shared locks.

## Completed source consumer

ENTIRE original08 thm:single-core passed1793503217184609784-2, all4exact frozen aliases/std3. Numeric compiler/quote/original-support/all-positive-valuation/universal-mask semantics all checked. Previous implementation TODOs above are historical. Full authoritative proof is SingleCorePresburgerStatementChecks.fixed_full; freeze hashes exact target compiled1793502040124333653-2 before consumer proofs. CompilerDiagnostic is unaccepted/outside root import closure. No assumption about core range or arithmetic theory was introduced.
