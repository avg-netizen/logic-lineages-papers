module
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestCompositionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackForceProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalControlGraphChoiceProof (excludedMiddle)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (shapeReject)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralLambdaFrameProof
open NumberedWindowInternalLiteralLambdaFallbackOpenProof (exact_OpenClippedLambdaFallbackCall)
open NumberedWindowInternalLiteralBoundedFallback (fallback)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLambdaHeaderTest (q w r : OTerm α)
    (head : D B Γ (unary cellHead (numeral 2) q)) :
    D B Γ (bit lambdaHeadTest ![q,w,r]) := by
  let gate : Program 1 := .composition equalityTest ![cellHead,literal 1 2]
  have good : D B Γ (unary gate (suc z) q) := by
    apply compositionValue equalityTest ![cellHead,literal 1 2] (suc z) ![q] ![numeral 2,numeral 2]
      (equalitySelf (numeral 2))
    intro j
    exact Fin.cases head (Fin.cases (literalGraph 2 ![q]) (fun e => Fin.elim0 e)) j
  exact onTape gate 0 (suc z) ![q,w,r] good

/-- For an actual lambda header, a successful remaining callback must
be the original tag-one witness. Every other contextual witness is
rejected physically, not by appeal to the callback's numeric meaning. -/
theorem exact_OpenLambdaFallbackForcesWitness (other : Program 3) (q w r n : OTerm α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (step : D B Γ (programGraph (fallback (lambdaFallback other)) (suc n) ![q,w,r])) :
    D B Γ (bit lambdaWitnessTest ![q,w,r]) := by
  let tape : Fin 3 → OTerm α := ![q,w,r]
  let ok := bit lambdaWitnessTest tape
  obtain ⟨arc⟩ := exact_OpenClippedLambdaFallbackCall other q w r n step
  obtain ⟨guard⟩ := exact_OpenLambdaHeaderTest q w r head
  have no : D B (ok.not :: Γ) ok := by
    have tagZero := shapeReject (literal 1 1) 1 1 tape
      (⟨Derivation.hypothesis List.mem_cons_self⟩ : D B (ok.not :: Γ) ok.not)
    have defaultRun := zeroBranchElim lambdaWitnessTest (otherLambdaCases other) chosenLambdaFrame
      (suc n) tape tagZero ⟨addHyp arc _⟩
    have bad := successorBranchElim lambdaHeadTest other (constantZero 3)
      (suc n) z tape ⟨addHyp guard _⟩ defaultRun
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc n) z tape bad (constantZeroValue tape)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  exact ⟨disjunctionElimination (excludedMiddle ok)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)) (Derivation.implicationIntroduction (Classical.choice no))⟩

#print axioms exact_OpenLambdaHeaderTest
#print axioms exact_OpenLambdaFallbackForcesWitness
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackForceProof
