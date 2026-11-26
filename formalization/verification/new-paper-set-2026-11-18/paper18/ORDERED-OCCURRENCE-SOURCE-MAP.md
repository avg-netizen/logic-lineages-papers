# Ordered occurrence dispatcher: exact supporting scope

Primary Snyatkov p43 ordered-name/equality/maximum preparation for current m:thm:snyatkov. Input is the actual NormalForm.Formula, not arbitrary SourceFormula. No asserted full normalization.

rows traverses every atom in every Boolean position; roster records original row and occurrence indices, signed coefficient and literal summand. ExactRoster includes repeated and zero-coefficient entries. live filters nonzero nonlinear bound-name occurrences only; the original compiled formula is never filtered, so all original syntactic domain guards stay at their Boolean locations. Inactive is a literal computed list, not an assumption that every bound name occurs nonlinearly.

Dispatch has explicit outcomes: finished empty block; unchanged inactive continuation; genuinely reduced equality/tie branches; unchanged-length strict-order/maximum continuations. Tags and exact provenance are targets. Maximum compares actual unweighted occurrence values, not coefficients. All permutations are literal enumeration, and maximum candidates use actual roster order. All equality/tie and maximum ties are retained. Other names share one valuation throughout.

TieReduction alone claims strict binder decrease. FullCoverage proves actual block existential equivalence to the finite output disjunction; it does NOT say all outputs terminate. FreeSupport forbids newly free names. Programs is a conclusion requiring a genuine all-input computable descriptor constructor calibrated to actual Formula.encode; no semantic decision oracle is an input. Malformed program inputs may be totalized arbitrarily, with every actual syntax code calibrated.

No inactive-variable projection, row separation, dominant-versus-runner-up partition, modular normalization, output normalized-grammar closure, or alternating QE/termination is accepted. The nondecreasing continuation tags make these debts explicit.
