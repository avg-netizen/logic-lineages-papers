# Additive source decisions with free parameters

This supporting BASE component extends the existing additive-source closed
formula decision to every finite ambient valuation, using the unchanged source
translation, linear quantifier elimination and plain parameter solver. The
additional solver block is empty, so all original free variables are fixed to
the supplied ambient values; missing entries are zero.

The original additive grammar admits constants, names, sums, equality, strict
order, negation, conjunction and named existential binders. Arbitrary Boolean
and binder positions, including alternation represented by negation, remain
in scope for this additive grammar. Every Phi node, even constant or unused,
is rejected by the unchanged AdditiveSource.test. No mixed Phi alternation,
general first-order BASE or source-register promotion is claimed.

Six exact targets require purely variable output summands, the exact acceptance
domain, original source truth for both Boolean answers, literal source-code
calibration, the concrete primitive-recursive program, and all-natural-code
correctness through the existing bijective source codec. No supplied QE or
computability witness is accepted as a premise.
