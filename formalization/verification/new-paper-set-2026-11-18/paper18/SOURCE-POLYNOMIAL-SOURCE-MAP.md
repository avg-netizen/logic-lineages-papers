# Current18 literal source polynomial heads

Source `sections/source-applications.tex`, complete `lem:source-polynomial`:
ground-open original terms, every internal type and subtype level at most two,
all direct scalar heads polynomial limits below omega^omega.

## Exact source, not a grammar oracle
`OriginalTerm Γ τ` is the actual intrinsically typed original syntax, including
variables, zero/successor/case, all recursor instances, application and lambda.
The original signature has no extra ranked constants. Γ is entirely ground;
τ and internal types are not restricted merely by the result level. Actual
`InternalLevelBound 2 t` checks `SourceTypeSupport.typeSupport`, which includes
the full types of constants, arguments, binders and their subtypes.

`AdmissibleAssignment.assignment p t` is the literal zero-history assignment
recursion; no source normalization occurs. Its partials and abstraction must
succeed as conclusions. `Policy` supplies admissible finite sum/repetition
shapes. The polynomial invariant holds for all such policies, a stronger
structural assertion than the source's fixed computable policy. No claim of
computability of arbitrary Policy functions is made or needed by this lemma.

`compileScalar` is a refusing structural traversal: each actual collapse
extracts its actual closed positive coefficient and recurses into its tail;
additions retain both children and original components retain identity.
`scalarHeads` lists EVERY shift head in that compiled tree, including all
nested tails and repeated occurrences. It cannot silently discard a collapse.
`fixedHead c` is the actual natural ordinal product omega⊗evaluate(c), and
its denotation is actualCollapse(fixedHead(c)+tail). This is the printed
literal direct head, not an arbitrary notation supplied as a premise.

The fresh expanded target requires actual assignment and scalar compiler
success and every extracted head's IsSuccLimit and <omega^omega. There is no
hypothesis of bounded head height, generated assignment, successful compiler,
finite positive values or polynomial coefficients: all must be proved.

## Exact existing proof route
`Source.SourceClasses.actualSourceClasses.2` already has this full type.
It derives actualLevelTwoSourceHeadProfile from literal generated-coordinate
profile invariants; PositiveHeightOnePolynomialBound proves actual ordinal
closure; sourcePolynomialIndexLimit proves the actual omega-natural-product
is a nonzero limit and remains below omega^omega. All those dependencies need
fresh recursive native evidence before accepting the current-source theorem.
This is only the printed polynomial-head lemma, not a source-vector decision.

## Exclusions
No universal level-two source comparison, full forward computability/domain
interface, admissibility of arbitrary component assignments, recursor-free
comparison, or full arithmetic supplier follows from this packet alone.
