module
public import LogicLineages.OrdinalComparison.WWTypedComponentTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualTypedOrdinalVariableVector : Targets.ActualTypedOrdinalVariableVector := by
  intro Γ σ v
  constructor
  · simp [ordinalVariableVector]
  · intro i
    simp only [ordinalVariableVector, List.getElem?_ofFn, dif_pos i.isLt]

theorem actualTypedOrdinalRenaming : Targets.ActualTypedOrdinalRenaming := by
  constructor
  · intro Γ t
    induction t <;> simp_all [ordinalExpressionRename, substitute, ordinalComponentRename]
  · intro Γ Δ Ξ ρ π t
    induction t <;> simp_all [ordinalExpressionRename, substitute, ordinalComponentRename]

theorem actualTypedOrdinalVectorRenaming : Targets.ActualTypedOrdinalVectorRenaming := by
  intro Γ Δ ρ σ v
  rw [ordinalVariableVector, List.map_ofFn]
  rfl

theorem actualTypedOrdinalHeadClosure : Targets.ActualTypedOrdinalHeadClosure := by
  constructor
  · intro Γ σ i
    rfl
  · intro Γ σ t
    induction t <;> simp_all [ordinalHeadClosure, ordinalExpressionRename, substitute,
      ordinalComponentRename, ordinalHeadClosureComponent, Renaming.weaken]

end LogicLineages.OrdinalComparison.Source
