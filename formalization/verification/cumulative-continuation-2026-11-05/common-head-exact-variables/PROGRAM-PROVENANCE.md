# Source and program provenance

The compiler and its underlying common-head arithmetic are reused without changes
through the already audited `CommonHeadClosureDecisionSemanticInterface` and
`CommonHeadClosureDecisionCodeInterface`. The original common-layer support
containment proof is reused literally. Padding truth, support and literal encoding
are proved narrowly from the existing finite-conjunction laws, avoiding a broad
balanced compiler import solely for these elementary facts.

The actual raw support function is the original
`CommonLayerComparison.codedVariables depth code`. Its finite graph has state
`(depth, code)`. At depth zero the existing real BASE term variable extractor is
used. At positive depth its children are the existing decoded payload children at
depth minus one. Concatenation preserves exactly the original variable occurrences.
Strict decrease of depth proves finite evaluation even for malformed payloads;
existing `Encodable.decode.getD (0, [])` defaults are not altered. The graph's
exact-value theorem supplies actual total Computable extraction, not merely an
assumed evaluator or a class field.

Output composition applies dedup only to padding names, maps each to the literal
instruction for x=x, folds existing conjunction, and joins that code to the original
compiler output. No source-order or multiplicity claim is made for the free-variable
set. There is no new oracle, positivity premise, finite bound on variable indices,
or claim of primitive recursiveness for the complete compiler.

The first candidate stopped at the unchanged LinkedResidueProof RSS guard via
BaseFormulaProof → GuardCodeRuntimeProof → CommonHeadCodeInterfacesProof →
FiniteGraphProof. Receipt 1793894711510466549-2 and candidate bytes are preserved.
The two new owned runtime/calibration proof modules reproduce exactly the original
`ExactLiteralEncoding` and `LiteralBaseFormulaCode` propositions and their elementary
syntax inductions, omitting only the unrelated full row-computation interface.
No original supplier file or limit was changed. Their transitive axioms are included
in the final source-clause audit.
