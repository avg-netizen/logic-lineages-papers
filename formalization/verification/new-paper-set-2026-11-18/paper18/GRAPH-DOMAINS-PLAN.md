# Generic finite-exception graph-domain decision plan

Plan only; independent review before concrete definitions/targets/proofs. Scope complete current18 m:lem:graph-domains, not free-parameter QE.

## Literal presentations and source semantics

Use finite concrete graph data: original natural input wire, output wire, computed cutoff L, one actual word-linear tail equality row, and a finite list of exact small-input (k,value) point pairs. Its source graph predicate is (L<=input AND tail row=0) OR one of those point equalities. Both fields reference the same valuation of named wires; repeated/shared names remain unchanged. The presentation's domain invariant says every word occurrence in its tail row is defined whenever L<=input, and its degree invariant is actual RowAllowed D. Point input indices are below L. Include the source total/functional property as an explicit specialization property of graph data, but the finite decision construction can prove a stronger result not needing it. Do not assume any decision function or branch-solving oracle.

Input query also has a finite list of literal linear graph rows, a Boolean combination of linear output comparisons/congruences, and an original input scope d. Linear means every word is empty; graph wires are all natural and original i<d are positive. Source satisfaction is the common-valuation positive graph conjunction and output Boolean, not independent wire parameters. No graph is negated.

## Genuine positive branch specialization

For each graph enumerate one tail alternative (guard+tail equality) and its finitely many point alternatives (input=k AND output=value). Compute the finite Cartesian product of these choices, preserving graph occurrence multiplicity. Each branch matrix is positivity AND all chosen graph constraints AND all linear equations AND the unchanged output Boolean. Call the concrete closed-word solver separately on each complete branch and OR its returned Booleans. Empty graph lists give one branch; empty point tables leave the tail branch. Truth and empty original input scope remain covered.

Do NOT combine these matrices into one Formula disjunction passed once to the solver: its global meaningful predicate would incorrectly require words from inactive alternatives. Here each solver input contains only chosen tail words. Prove the exact source conjunction iff SOME branch is true. For each branch, prove allowed D; prove truth of its retained guards implies meaningful for every word in that branch, including any Boolean inactive output branch (all output words are empty). Thus branch satisfiability with meaningful iff plain branch truth, and the finite OR exactly decides the source query.

Explicit substitution/evaluation of fixed point values is not necessary for this implementation. Point equalities remain literal constraints on the same names; retained tail guards still enforce the exact domain bound. If a point and guard conflict the entire branch is unsatisfiable, while a consistent point/tail combination has all its tail words defined. This proves the same case-split theorem without totalizing undefined words or dropping correlations. The source proof's optional substitution normalizes cases, but is not a missing decision obligation if this guarded-domain lemma is proved.

## Effectivity and frozen endpoint

Provide explicit numeric encoding of graph data/query and an actual finite list-of-formula-code branch compiler. Prove structural/numeric calibration and joint primitive-recursive or computable compilation, then joint computable finite-OR flags using the actual Machine.solve. Invalid codes default deterministically. Final endpoint requires the complete original common-valuation existential equivalence, positive/raw scopes, graph/linear/output syntax, and actual numeric solver; no supplied formula translation or finite-oracle premise.

Domain/degree assumptions are verified properties of supplied finite graph presentations, not blanket claims that partial words are defined. Explain their derivation for presentations produced by the graph theorem. Our current actual compiler has cutoff zero/empty exceptions/all-natural domains; the new construction must genuinely handle arbitrary nonempty finite point tables too, including shared input wires and point-output/input coincidences across clauses. A structural total/functional certificate alone does not imply tail word domains, so keep these logically separate and explicit.

No arithmetic with free parameters, nonlinear word applied to a sum, or full main-comparison claim.
