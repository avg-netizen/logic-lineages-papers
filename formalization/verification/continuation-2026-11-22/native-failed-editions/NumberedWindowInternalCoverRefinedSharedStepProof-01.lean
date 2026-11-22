module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAny layout)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedSyntaxUpdate)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverRefinedStep : ExactOpenCoverRefinedStep := by
  intro V T body α Γ prior old row
  let xs : Fin 4 → OTerm α := ![prior,old,z,z]
  obtain ⟨both⟩ := conjunctionRecover (sharedSyntaxUpdate V T) headerOnRow xs row.update
  have key := unaryGraph .succ (.projection 0) (suc prior) prior xs
    (successorValue ![prior]) (projectionValue 0 xs)
  have check : Nonempty (Derivation body Γ (unary (headerAny layout) (suc z) (suc prior))) := by
    apply compositionRecover (headerAny layout) (fun _ : Fin 1 => currentKey)
      (suc z) xs ![suc prior] ⟨Derivation.conjunctionRight both⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact key
  exact ⟨⟨Derivation.conjunctionLeft both⟩,check⟩

#print axioms exact_OpenCoverRefinedStep

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedStepProof
