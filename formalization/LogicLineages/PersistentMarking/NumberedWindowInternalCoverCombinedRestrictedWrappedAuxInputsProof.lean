module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverThinMatchingWindowInputs : ExactOpenCoverThinMatchingWindowInputs := by
  intro C baseW V s body α Γ ctx ty raw actual
  let xs : Fin 3 → OTerm α := ![ctx,ty,raw]
  let rawCall : Program 3 := .composition V (fun _ : Fin 1 => .projection 2)
  let D := conjunction thinContextPresent (thinOwnSeed C s)
  obtain ⟨parts⟩ := conjunctionRecover (thinSyntaxWindow baseW V) D xs actual
  obtain ⟨syntaxReports⟩ := conjunctionRecover baseW rawCall xs ⟨Derivation.conjunctionLeft parts⟩
  obtain ⟨conditions⟩ := conjunctionRecover thinContextPresent (thinOwnSeed C s) xs
    ⟨Derivation.conjunctionRight parts⟩
  have rawValid : Nonempty (Derivation body Γ (unary V (suc z) raw)) := by
    apply compositionRecover V (fun _ : Fin 1 => .projection 2) (suc z) xs ![raw]
      ⟨Derivation.conjunctionRight syntaxReports⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 2 xs
  exact ⟨rawValid,⟨Derivation.conjunctionLeft syntaxReports⟩,⟨Derivation.conjunctionLeft conditions⟩⟩

#print axioms exact_OpenCoverThinMatchingWindowInputs

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
