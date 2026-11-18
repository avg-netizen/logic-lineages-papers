import LogicLineages.PersistentMarking.RefinementFullCallProof
import LogicLineages.PersistentMarking.RefinementMarkProof
namespace LogicLineages.PersistentMarking.RefinementSyntaxProof

/- Complete frozen source conjunction, not a selectable helper subset. -/
theorem fullSyntax : RefinementSyntaxTargets.FullSyntax :=
  ⟨AuxiliaryReflexivityProof.refinementRefl,
   RefinementTransitivityProof.transitive,
   RefinementSubstitutionProof.freeSubstitution,
   RefinementFreshOpeningProof.opening,
   RefinementSubstitutionProof.arbitraryRenaming,
   AuxiliaryReflexivityProof.refinementRetyping,
   RefinementMarkProof.refinementMarkReflection,
   RefinementFullCallProof.fullApplication⟩
end LogicLineages.PersistentMarking.RefinementSyntaxProof
