# Proposed genuine polynomial Boolean decision bridge

Status: plan before new definitions/targets/proofs. Independent plan review
required. This is NOT a wrapper that assumes a graph-to-decision oracle.

## Audited concrete suppliers

1. PolynomialGraphCompletion.ExpressionSemanticStatementChecks supplies real
source Expr graph soundness, fresh realization, allocated-node uniqueness,
and all-natural-input domain/finite-degree correctness. The actual source
compiler rows/start/output and ExpressionCode.run/package are explicit and
primitive recursive. Expr has numeral, named variable, addition, fixed natural
scale and fixed polynomial collapse. Repeated original names remain shared.
2. ClosedWordDecisionCompletion.Machine.solve is a concrete total numeric
solver. MachinePrograms.solve_computable proves joint degree/code computability;
MachineProof.actualClosedDecision proves exact satisfiability for Formula.allowed
D, with Formula.meaningful p ν AND Formula.eval ν p. No free-parameter QE.
3. Both formula and graph Row are literally PolynomialGraphCompletion.Row;
no semantic row adapter or independently quantified word-value parameter is
needed. WordLinearDecisionCompletion.Formula encodes Boolean atoms
nonnegative/divisible and explicit global word domains.

## Full current cor:polynomial-booleans endpoint

Introduce literal finite Boolean source syntax over equality, weak and strict
comparison of polynomial Expr. Include truth,neg,conj,disj. A declared d bounds
original variable names i<d, and every head is a genuine nonzero polynomial
limit. Quantify over positive original valuations i<d; fresh graph wires are
natural, including zero. Retain arbitrary fixed nesting/addition and repeated
names. Source semantics uses actual Expr.value/collapse, not compiler output.

Compile all atom expression occurrences into ONE global allocation, starting
at d. Each occurrence gets a disjoint consecutive block, using existing
rows/start/output and nodeCount. Sequential allocation keeps every earlier
block and all original names fixed during later realizations. Collect ALL
graph equations positively, regardless of Boolean negation/disjunction.
Translate only the source output atoms to linear rows on their node outputs:
<= by nonnegative(right-left), < by nonnegative(right-left-1), equality by both
opposite nonnegative rows. Preserve Boolean syntax around these output tests.
Add positive guards for original names0,...,d-1. Fresh nodes get no positive
restriction. Track common degree>=3 sufficient for every actual head/row.

Prove the allocated ranges are disjoint and above originals; emitted graph
conjunction has a realization for EVERY original valuation and uniquely
fixes each output to the corresponding source expression. Prove all row word
domains for EVERY natural global valuation from existing graph-domain theorem,
and every output/positivity row has empty words. Hence the complete emitted
formula is meaningful automatically; no domain premise leaks to the endpoint.

Existential matrix = original positivity AND positive graph conjunction AND
translated Boolean output test. Universal counterexample matrix has the SAME
positive graph conjunction and positivity, and negates ONLY the output test.
Do not negate graphs or turn nodes into independent parameters. Prove exact
existential equivalence for both matrices using global realization and
soundness. Set flags=(solve D existentialCode, NOT solve D counterexampleCode).
Prove both biconditionals for the original source existential/universal closures.

Effectivity is an explicit final obligation: numeric encoding of source formula,
actual structural/postfix compiler calibration, joint Computable compiler and
flags (or primitive recursive compiler plus computable solve). Invalid numeric
codes may default deterministically, but every valid source encoding must map
to its literal finite graph/Boolean matrices. A mere finite semantic formula
existence theorem or a presumed computable AST function is insufficient.

## Why this route needs no finite-exception split

The checked graph compiler proves all-natural word domains and exact rows;
graphCutoff=0, graphExceptions=[]. This is stronger than the printed finite-tail
construction. The above bridge can therefore establish the FULL source Boolean
corollary without a generic exception normalizer. This fact must be a theorem
used in the proof, not an assertion that all totalized partial words are meaningful.

## Separate generic graph-domains lemma: not silently credited

Current m:lem:graph-domains permits finite graph presentations with nonempty
small-input tables. A full exact formalization of that broader presentation
still needs: enumerate a finite list of branch matrices by distributing only
positive graph disjunctions; substitute each fixed input/output integer into
all correlated rows and guards; discard violated tail guards; evaluate/remove
all word occurrences in fixed names only after checking their domains; retain
remaining name correlations and tail guards; compute per-name domain bounds;
prove finite-case satisfiability equivalence; OR the concrete solver outputs.

This is not achieved by building one disjunctive Formula and ignoring inactive
word domains: Formula.meaningful demands every literal occurrence, even under
negation and unselected disjuncts. A tail word may be undefined in a small-point
case, so that naive reduction is unsound. Finite branch specialization or the
proved all-natural generated-graph specialization is necessary. The proposed
first endpoint deliberately promotes only cor:polynomial-booleans, NOT the
full generic finite-exception lemma. A later generic lemma must freeze all the
case/specialization/effectivity obligations above, with no finite oracle premise.

## Review/sequence

First independently review this plan, including scope distinction and source
faithfulness. Then freeze concrete literal definitions and source-complete
comparator, review again, author proofs, obtain exclusive bounded native turn,
recursive evidence and final independent review. Do not change old graph or
solver definitions, compiler caps, source manuscripts or historical statuses.
