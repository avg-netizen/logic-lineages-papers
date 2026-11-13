# Independent source-scope audit: weighted insertion and sort

Reviewed SortWeightedDefinitions, Targets, insertion/sort Proof and Core modules, and both induction-binding suppliers. Coordinator reports exact2 PASS, receipt 1794569876860672875-30; this source audit does not rerun the compiler.

## Findings

- The two targets quantify arbitrary external arity k and an arbitrary primitive-recursive Program (k+1), with arbitrary internal runtime parameter vector params : Fin k → OTerm alpha. F is not restricted to a particular weight, evaluator, native interpretation, or closed numeral input.
- The same F and the same params are used at every entry of the original row and the inserted/sorted row. Renaming in continuations transports that entire vector consistently. The fold step explicitly feeds F the current entry followed by the unchanged parameters, then adds the recursive accumulator.
- Insertion consumes the literal graph of OriginalNumericListSort.insert, actual F(x,params)=weight, and actual weighted(raw,params)=sum. It concludes actual weighted(inserted,params)=weight+sum. Sort consumes the literal original sort graph and the original weighted graph, concluding that same sum on its actual output.
- No sortedness, decoded-list permutation, desired output weight, comparison outcome, or semantic rank fact appears in either endpoint. The insertion proof splits the actual numeric comparison internally and reconstructs its branches with original insertion graph suppliers.
- Both proofs use internal strong induction over the raw arithmetic list code. Their rawInduction suppliers build InternalStrongInduction predicates and apply strongInduction, then eliminate the universal at the arbitrary raw term. The nonzero case queries the original head/tail programs and reconstructs the cons code; the recursive application is justified by actual consTailDescent.
- The difficult insertion-after-head case is a genuine internal sum rearrangement: the code derives sum = headWeight + tailSum by fold functionality, constructs headWeight + (insertedWeight + tailSum), and transports it to insertedWeight + sum using internal addition commutativity, associativity, and congruence.
- Sorting derives the actual insert of the current head into the recursively sorted tail using sortConsRecover, then applies the checked insertion theorem and the actual original cons-sum equation.
- The weighted program is a new proof-side sum fold. It does not replace the original numeric sort/insert AST, evaluator, selected tuple, or canonical program. Multiplicity is retained in the sum law; no deduplication interpretation is used.

## Scope verdict

The exact statements support internal preservation of arbitrary parameterized arithmetic weighted sums by the unchanged original insertion-sort, without native permutation reflection or hidden sortedness assumptions. They do not alone establish evaluator rank determinacy, any relation between the weighted fold and an evaluator component, canonical cancellation, Object equality, I/C, or accessibility. Those require additional genuine connecting theorems.
