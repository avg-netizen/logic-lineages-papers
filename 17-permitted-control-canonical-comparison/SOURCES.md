# Published sources, retained definitions, and corrections

The mathematical bibliography is in `references.tex`. The source question
and canonical assignment are credited to Gunnar Wilken and Andreas Weiermann,
*Derivation Lengths Classification of Gödel's T Extending Howard's Assignment*,
LMCS 8(1:19), 2012, DOI 10.2168/LMCS-8(1:19)2012. Section 2.1 supplies the
permitted control framework; Definitions 2.6–2.8 specify the substitution
domain and comparisons; Definitions 2.10 and 2.18 specify the assignment
operators; the zero-history case of Definition 3.1 gives the canonical source
map. The paper states these definitions directly.

The ordinal-norm background is also credited to W. Buchholz, E. A. Cichon
and A. Weiermann, *A Uniform Approach to Fundamental Sequences and Hierarchies*,
Mathematical Logic Quarterly 40(2), 273–286, 1994,
DOI 10.1002/malq.19940400212. The final linear projection uses D. C. Cooper,
*Theorem Proving in Arithmetic Without Multiplication*, in *Machine
Intelligence 7*, 91–99, 1972. The hardness reduction uses Paliath Narendran,
*Solving Linear Equations over Polynomial Semirings*, LICS 1996, 466–472.
The exact source compiler and its assignment calculations are printed here.

## Corrections integrated into the paper

- The scalar partial estimate is weak. At the tracked scalar variable, both
  sides are one; the strict assertion in the printed Lemma 2.19 fails there.
- The printed free-subtree estimate (A.5) has an equality case. The new
  first-free-positive-subtree argument supplies bounded norm with the original
  multiplier `2^n sum_i s_x(h_i)`. No replacement multiplier changes the object.
- Literal parsing is explicit. Existing expression trees are not reassociated
  before a later syntactic partial is taken. The theorem is uniform in an
  admissible computable policy, not an assertion of policy independence.
- The generated-source argument handles every internal and bound-variable
  type. The positive coordinates become closed exactly when free term inputs
  are ground, leaving a shared finite fixed-head scalar circuit.
- Entry formulas carry their genuine source and target domains. Cocycle
  bounds include the intermediate target, zero-target strict comparisons keep
  their positive unit, and equal-gap breakpoint selection retains an included
  endpoint unless the top interval is clipped by the excluded initial phase.
- Count normalization groups full leading values before cancellation.
  The finite charge, complete small-coordinate strips, graph-wire polarity,
  and decreasing-dimension projection are part of the proof.

The paper does not claim that the single canonical zero-history map is a
history-dependent assignment derivation following every reduction. It also
does not identify the numerical comparison with the structural ordering.

## Earlier public sources and verification boundary

Earlier entries 05 and 07–10 were read at public commit
`4028a9e34506f4339af2992749464cf2d4d55eb9`, together with the repaired
formalization records. Useful foundations and the actual-source compiler
are consolidated into this paper. Separate one-variable, polynomial-head,
balanced-layer and low-type algorithms are not prerequisites of the new
chosen-control theorem; their other scopes are retained in the older papers.

Preparation and cross-checks were performed by OpenAI Codex under the
repository owner's direction. The manuscript is a complete hand-proof
exposition. The existing formalization checks do not yet certify the new
controls, all-head entry calculus, complete elimination procedure and final
classification. Copyrighted source papers are cited, not redistributed.
