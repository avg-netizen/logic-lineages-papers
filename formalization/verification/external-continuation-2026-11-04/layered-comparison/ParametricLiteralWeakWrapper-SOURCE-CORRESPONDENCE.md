# Literal identity/constant weak-comparison wrappers

Paper09 paper.tex lines 193–201 uses I=λz.z and K=λz.0, applying K directly to R and I directly to L. These definitions reuse the existing literal GroundEquivalence.identity and constant syntax, with no magnification. Existing GroundEquivalence.upper/lower and ExistentialPlan.weakPair include an extra magnify eraser and are not identified with these literal wrappers.

ExactAssignment gives the entire actual default-assignment vector for each application under the explicit successful assignment of its operand. The vectors are collapse one (three+v0) and collapse one (five+v0), with three/five spelled as exact source-independent ordinal expressions. The existing assignment-only lemmas can be reused; fixed-Phi denotation and admissible-substitution conclusions cannot.

FiniteCoefficientCalibration assumes only a successful finite Scalar observation x for the operand, for arbitrary G and ordinal-valued environment. It concludes coefficientOne G (x+3) and coefficientOne G (x+5), preserving zero cases and the original full assignment. ControlValueCalibration additionally assumes StrictMono G and n≤G n and concludes G(x+5)+1 and G(x+7)+1. These are exactly g(x+3), g(x+5) where g(n)=G(n+2)+1, not G itself.

No Gamma gap equivalence, aggregate application, weak coded language, numeric encoding, source fragment/level preservation, universal reduction or completeness is asserted here. The manuscript, original weakPair, default assignment and accepted semantics remain unchanged.
