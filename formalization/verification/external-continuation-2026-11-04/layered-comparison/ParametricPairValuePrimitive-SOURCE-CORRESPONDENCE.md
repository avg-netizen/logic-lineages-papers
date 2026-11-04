# Primitive-recursive actual finite-pair value

This strengthens the finite-iteration justification relevant to paper09 hardness.tex lines 316–319 using the independently proved generic finite-coefficient identity, corresponding to foundations.tex lines 268–277.

iterateValue is the explicit input-dependent iteration of the indexed section H(i,·), repeated a times on 2*a+b, then adding a. The numerical constructor is primitive recursive whenever H is jointly primitive recursive. Identifying it with the actual ordinal pair-collapse value additionally requires StrictMono and identity majorization for every indexed section; no claim follows from PR alone.

FixedGammaPrimitive uses the existing fixed-b actual table-clock Gamma PR and monotonicity/majorization suppliers. It does not infer joint-in-b primitive recursiveness from sectionwise PR. No value definition, collapse recurrence or evaluator is changed.

This component establishes actual finite-pair value PR, not worklist fuel/runtime PR, a fixed iteration count independent of inputs, generic parameterized fold PR, whole-source evaluator PR or any change to the earlier proof-method qualification before composition is checked. No manuscript/register/export changes.
