# Uniform computability of actual finite-pair collapse

Target-only proposal toward paper09 hardness.tex lines316–319. The domain here is actual ordinary omega*a+b for natural a,b, not every source term.

SearchValue is Nat.rfindOpt over the unchanged calibrated bounded indexed evaluator. ExactSearch requires actual-value membership, totality, unique output, and a successful fuel with every smaller fuel returning None, for arbitrary H. No default-zero replacement for failure is introduced. UniformPartialRecursive assumes Computable H : Nat×Nat→Nat. UniformComputable then establishes the actual ordinal collapseWith value jointly in the control-family index and pair input, using proved totality.

FixedGammaComputable specializes to each fixed b using the accepted Primrec(gamma b) theorem. It does not assert joint uniformity in b without a separate control-family certificate. No monotonicity or majorization premise is needed for the generic result.

This claims computability, not primitive recursiveness of unbounded search/value or a runtime bound. General restricted-source evaluation, calibration of natural ordinal operations, upper bound/completeness, weak comparison and publication remain separate. Existing collapse, source semantics, manuscripts and register remain unchanged.
