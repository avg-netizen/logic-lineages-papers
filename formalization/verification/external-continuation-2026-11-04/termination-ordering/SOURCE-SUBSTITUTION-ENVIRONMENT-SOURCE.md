# Actual typed-variable enumeration and substitution environment coordinates

Source: paper06 finite computable substitution invariant, lines576–580 and620–622. variableAt Gamma i is the actual de Bruijn variable of type Gamma.get i: here at index0 and there recursively for successor positions. Targets1/2 prove its existing SourceTypedPorts.variableIndex equals i.val and its packed typed-variable enumeration is exhaustive. Empty Gamma has no indices or variables; repeated types remain distinct positions.

substitutionValues uses a literal typed auxiliary substitution theta:Gamma→Delta and assigns coordinate i the existing representativeCode of theta(variableAt Gamma i), retaining its exact type Gamma.get i. Target3 assumes the actual per-type formula calibration, then proves environment formula truth iff pointwise C_tau of every actual variable image. The packed equality from exhaustiveness handles dependent types explicitly; no untyped cast or index identification is assumed.

This coordinate iff does not need a decoded Context or GoodSubstitution and does not infer either. The separate accepted GoodSubstitution predicate is precisely guarded: for v:Variable Gamma tau, it supplies Good(theta v) only given tau∈S. Thus later literal confinement extraction requires both GoodSubstitution and type membership. Numeric C of a representative alone must not stand in for those premises. The symbols/S used for representative codes are explicit, and context interpretation remains separately supplied to C.

No semantic preservation under arbitrary substitutions, lambda/numbered constructor theorem, ID1 derivation, all-term C, WF or original transitivity claim. Proof absent pending review/freeze.
