# Bridge the existing Boolean BASE compiler output

Common-head and balanced comparison compilers already return BaseFormula.Formula
and its original postfix instruction list. This bridge preserves that Boolean
meaning, the exact original variable-occurrence list and arbitrary nested BASE
terms. Truth/falsity become constant source atoms; disjunction becomes its exact
De Morgan source encoding. No comparison algorithm is rebuilt.

Eight targets require literal stack/compiler calibration, original-prefix and
closure decisions, and actual primitive recursion of the postfix-to-source
machine and all numeric decision wrappers. Correctness is on actual Formula.encode
programs. No arbitrary malformed postfix-program contract, alternating quantified
comparison theorem, QE or complete BASE endpoint is asserted.
