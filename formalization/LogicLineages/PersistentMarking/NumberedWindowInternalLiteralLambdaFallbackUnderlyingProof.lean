module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicTickNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackForceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFallbackDecoderProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFirstTickSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackUnderlyingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalTagArithmeticSupportProof (symm cancelSuc sucNeZeroApply)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrame (chosenFrame)
open NumberedWindowInternalSparseRawTick (tagFiveTest)
open NumberedWindowInternalLiteralAuxFirstTickSupportProof (shapeReject)
open NumberedWindowInternalLiteralAuxRootLeafFieldsProof (sourceParts)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D bit)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback sourceIsAux)
open NumberedWindowInternalLiteralAtomicTickNumericProof (atomicFallback)
open NumberedWindowInternalLiteralAtomicFallbackDecoderProof (exact_OpenAtomicFallbackUnderlying)
open NumberedWindowInternalLiteralBoundedFallback (fallback)
open NumberedWindowInternalLiteralLambdaFrameProof (lambdaFallback)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenLambdaRejectsAuxiliarySource (q w r : OTerm α)
    (held : D B Γ (unary cellHead (numeral 2) q)) :
    D B Γ (programGraph sourceIsAux z ![q,w,r]) := by
  let E := bit sourceIsAux (![q,w,r] : Fin 3 → OTerm α)
  have no : D B (E :: Γ) (⊥ : Formula α) := by
    apply sourceParts q w r ⊥ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Δ d c f a keep same _
    have head := renameInto held j Δ (fun φ h => keep φ (List.mem_cons_of_mem _ h))
    rw [unaryRename,numeralRename] at head
    obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Δ) (numeral 6 : OTerm β) (packedBody [d,c,f,a])
    have aux : D B Δ (unary cellHead (numeral 6) (auxiliaryTerm d c f a)) :=
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
    obtain ⟨eq⟩ := same
    have six := headTransport cellHead (numeral 6) (auxiliaryTerm d c f a) (q.relabel j) ![] ⟨symm eq⟩ aux
    obtain ⟨absurd⟩ := valueUnique cellHead (numeral 2) (numeral 6) ![q.relabel j] head six
    exact ⟨sucNeZeroApply (symm (cancelSuc (cancelSuc absurd)))⟩
  obtain ⟨no⟩ := no
  exact shapeReject (literal 1 6) 4 0 ![q,w,r] ⟨Derivation.implicationIntroduction no⟩

/-- The actual installed auxiliary/atomic guards do not hide the
tag-one lambda fallback. The same candidate is exposed on the same
raw child limit in the same program, with the other tests retained. -/
theorem exact_OpenFullLambdaFallbackUnderlying (other : Program 3) (q w r n : OTerm α)
    (head : D B Γ (unary cellHead (numeral 2) q))
    (held : D B Γ (programGraph (auxiliaryFallback (atomicFallback (fallback (lambdaFallback other))))
      (suc n) ![q,w,r])) :
    D B Γ (programGraph (fallback (lambdaFallback other)) (suc n) ![q,w,r]) := by
  let F := fallback (lambdaFallback other)
  have no := exact_OpenLambdaRejectsAuxiliarySource q w r head
  have arc := zeroBranchElim sourceIsAux (atomicFallback F) (branch tagFiveTest (constantZero 3) chosenFrame)
    (suc n) ![q,w,r] no held
  exact exact_OpenAtomicFallbackUnderlying F q w r n arc

#print axioms exact_OpenLambdaRejectsAuxiliarySource
#print axioms exact_OpenFullLambdaFallbackUnderlying
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaFallbackUnderlyingProof
