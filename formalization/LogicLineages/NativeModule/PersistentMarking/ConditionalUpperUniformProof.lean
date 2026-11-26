module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformBridgeProof
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperProof

/-! Conditional `thm:upper` with the uniform internal hypothesis: E4 and, for each closed window,
ID₁-derivability of the all-terms sentence at programs evaluating the original checks.  The
bridge reduces it to the individual form of #1466 (`exact_ConditionalUpper`). -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperUniformProof
open ConditionalUpperUniformTargets

theorem individualOfUniform (uniform : UniformAccessibility) : ConditionalUpperTargets.IndividualAccessibility := by
  intro S K hk
  obtain ⟨i, j, r, d, c, evaluates, accessible⟩ := uniform S K hk
  exact ⟨i, j, r, d, c, evaluates, fun x hx =>
    ConditionalUpperUniformBridgeProof.exact_UniformToIndividual S K hk i j r d c evaluates accessible x hx⟩

theorem exact_ConditionalUpperUniform : ConditionalUpperUniform := by
  intro BH norm uniform
  exact ConditionalUpperProof.exact_ConditionalUpper BH norm (individualOfUniform uniform)

#print axioms exact_ConditionalUpperUniform

end LogicLineages.PersistentMarking.ConditionalUpperUniformProof
