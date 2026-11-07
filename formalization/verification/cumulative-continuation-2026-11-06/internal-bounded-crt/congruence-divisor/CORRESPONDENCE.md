# Congruence under divisor: supporting internal CRT lemma

Exact target: InternalCongruenceDivisorTargets.ActualDivisor.
This supporting lemma preserves the existing literal `InternalLinearCombination.divides d m`
(single existential quotient, m = q*d) and `InternalModularArithmetic.congruent a b m`
(two existential offsets, a + q*m = b + p*m). It concludes the same congruence
formula at modulus d. All body predicates, free-variable types, contexts and four
terms are universally quantified. No positivity or coprimality assumption is added.
The intended proof eliminates the three actual object existential witnesses and
reassociates their products. It makes no claim to complete a numbered paper theorem
or the bounded CRT induction. The frozen target and supplier hash manifest were
recorded before proof authoring; compile-first must precede proof authoring.
