# Scoped free-parameter Phi applications

This semantic component retains the existing actual SourceFormula and BaseTerm
grammars, original Boolean positions, original binder names and shadowing.
The syntax test tracks the entire active binder list. Every Phi application is
accepted only when all names in its argument lie outside that list. Nested Phi
on such parameters is allowed. Bound-dependent Phi is rejected syntactically,
even if semantic cancellation might erase that dependence.

The transformation evaluates each entire Phi application using the one fixed
ambient valuation, replaces it by the corresponding literal numeral, and leaves
ordinary variables, sums, Boolean nodes and binders in place. Its scoped
correctness theorem allows arbitrary assignments at active bound coordinates
and requires agreement only outside them. The binder step must establish the
extended agreement condition, including repeated/shadowed names.

Seven exact targets require additive term/formula outputs, scoped term/formula
meaning, finite-ambient decision domain/truth, and the exact scope boundary.
Arbitrary quantifier alternation is permitted only through additive occurrences
of bound names; Phi arguments use free parameters. This does not admit general
bound-dependent Phi alternation, full BASE, arbitrary word syntax or a source
register promotion. Numeric calibration/computability is a separate next stage,
not asserted by these semantic targets or supplied as a premise.
