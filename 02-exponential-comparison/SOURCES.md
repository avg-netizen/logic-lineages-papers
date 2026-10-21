# Source and proof guide

| Source | Use in this paper |
|---|---|
| Wilken and Weiermann, *Derivation Lengths Classification of Gödel's T Extending Howard's Assignment*, [LMCS 8(1:19) (2012)](https://doi.org/10.2168/LMCS-8(1:19)2012), arXiv:1203.0115v2 | Definitions 2.4–2.9 supply the syntax, independent admissible ground substitutions, scalar/vector comparison and bounded C classes. The effectiveness conjecture follows Definition 2.8. Proposition 2.3 supplies the collapsing-function norm estimate. |
| Matiyasevich, *Hilbert's Tenth Problem*, MIT Press (1993) | MRDP: Diophantine solvability is computably enumerable complete. The paper converts the usual nonnegative-input formulation to positive inputs explicitly. |

The source's fast-growing hierarchy starts with `F_0(n) = 2^n`. Confusing this with doubling would invalidate the vector bound; the manuscript uses the exponential definition.

The multiplication gadget, positive-circuit translation and depth-two sum-of-squares encoding are proved locally. No Diophantine undecidability theorem for this exact signature is imported. Recursive normal forms and the separation-ray proof give the identity and unary algorithms. Their threshold recursion is explicit and requires no transcendence theorem.

The vector corollary imports source definitions but proves that the constructed vectors meet the boundedness side condition. It is not a claim about recognition of the actual assignment image, a general ordinal comparison algorithm, or a completed termination ordering. The algorithms establish computability without a practical running-time guarantee. No companion executable is needed for the mathematical proofs.
