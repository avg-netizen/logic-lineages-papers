module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedTypedSemanticsProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.NumericProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedWitnessProof
open Source Source.ForwardTranslation Source.SourceClasses LevelTwoCounterexample

/-- A concrete uniform numerical witness, with no caller-supplied classifier,
package metadata, word solver, or termination premise. -/
theorem fullInternalLevelTwoComparison : Targets.FullInternalLevelTwoComparison := by
  refine ⟨solve,ProgramsProof.solve_computable,?_⟩
  intro Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,hav,hbv,_,hdecision⟩ := BoundedDecisionProof.actualTypedDecision Γ hΓ τ υ a b hla hlb mode
  exact ⟨av,bv,hav,hbv,hdecision⟩

#print axioms fullInternalLevelTwoComparison

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.BoundedWitnessProof
