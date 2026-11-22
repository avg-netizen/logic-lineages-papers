module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionFamilyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalElimination)
open NumberedWindowInternalCoverOwnEarlierTargets (ownMatrix)
open NumberedWindowInternalCoverOwnEarlierSyntaxProof (ownWitness)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedInductionFamilyProof (exact_OpenCoverCombinedRestrictedOwnFamily)
open NumberedWindowInternalCoverCombinedRestrictedInductionTargets

theorem exact_OpenCoverCombinedRestrictedInductionOwn : ExactOpenCoverCombinedRestrictedInductionOwn := by
  intro V TV M M0 B T s body α Γ raw vertices ctx result P valid typed held
  obtain ⟨allKeys⟩ := exact_OpenCoverCombinedRestrictedOwnFamily V TV M M0 B T s body α Γ raw
  obtain ⟨valid⟩ := valid
  have family := Derivation.implicationElimination allKeys valid
  have atOutput := actualFiniteUniversalElimination body α 3 Γ (ownMatrix P.W P.cover s raw)
    (fun i => emb (![ctx,result,vertices] i)) ⟨family⟩
  rw [ownWitness] at atOutput
  obtain ⟨atOutput⟩ := atOutput
  obtain ⟨typed⟩ := typed
  obtain ⟨held⟩ := held
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination atOutput typed) held⟩

#print axioms exact_OpenCoverCombinedRestrictedInductionOwn

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionProof
