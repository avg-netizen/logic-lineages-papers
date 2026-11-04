# Actual ordinal realization of nonnegative polynomials

Paper09 hardness.tex lines 188–193 uses each nonzero polynomial as a positive ordinal first coordinate in the matching zero pattern. This component establishes the ordinal/coefficient part, before any graded-expression or admissible-substitution lifting.

The input is an arbitrary finitely supported Nat→Nat coefficient function. signedCoefficients casts its coefficients to Int; embeddedCoefficients maps its natural exponents injectively into Ordinal. ExactEmbedding preserves every finite coefficient, gives zero at every transfinite exponent, and calibrates the accepted finitePart projection. No transfinite exponent is redirected to zero.

ActualRealization provides an actual ordinal a below omega^omega with exactly that full signedCNF, not only the correct finitePart. It also proves the projected equality and a=0 iff the input polynomial is zero, equivalently positive a iff nonzero input. Zero polynomial is included and yields ordinal zero; it is not falsely declared an admissible positive first field.

This is an existence and exact algebraic representation theorem. It does not yet build closed ClosedGrade 1 expressions, norm-bounded AdmissibleSubstitution vectors, a simultaneous system lift, primitive-recursive numeric syntax, the zero-pattern compiler, or any undecidability theorem. Fixed-Phi functional hardness and its external polynomial-linear-system source theorem remain pending. No register/manuscript/export changes.
