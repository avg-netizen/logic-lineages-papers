# Frozen original beta / congruence bridge

The three targets retain every original parameter and use the existing object formulas literally. ActualBetaCongruence derives congruent(c,r,1+(i+1)b) from beta(c,b,i,r). ActualBoundedCongruenceEquality derives r=s from the original congruence(r,s,m) and both original strict bounds r<m and s<m. ActualBoundedCongruenceBeta derives the unchanged OrdinaryArithmetic.betaFormula(c,b,i,r) from congruent(c,r,InternalBetaWitness.modulus(b,i)) and the original strict remainder bound r<modulus(b,i).

These are genuine InternalCalculus derivations, uniformly over arbitrary predicate bodies and original free-variable types. The reverse bridge must use the already checked internal beta totality, remainder arithmetic and uniqueness, not interpretation in Nat. No new coprimality, quotient, residue choice or semantic assumption is allowed. This is a beta coding prerequisite, not full sequence coding or a whole-paper theorem.

Targets and this correspondence are frozen before proof authoring. Target-first compilation precedes proofs. Existing accepted source files are immutable.

The initial target-only check failed on a misspelled source identifier ltFormula. The failed source and freeze are preserved; the corrected identifier is the existing OrdinaryArithmetic.lessFormula, with the same intended strict bound. No proof was authored before this correction.
