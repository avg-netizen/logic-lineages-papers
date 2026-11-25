module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicFrameZeroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxFallbackDefinitions
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFunctionGuardFieldsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralAtomProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAuxShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open SourceComputabilityFormulaSupportProof (numeral)
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (headTransport projectionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTestProof (rejectBackwardOrder)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalRecursionGraphExtensionSupportProof (successorOrder)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalLiteralNeutralAtomProof (zeroBelowSuccessor)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody unaryRename)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalLiteralFunctionGuardFieldsProof (nodeAtCases)
open NumberedWindowInternalLiteralAtomicRawGuardOpenProof (D)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest)
open NumberedWindowInternalLiteralAtomicFrameZeroProof (nodeTagReject)
open NumberedWindowInternalLiteralAuxFallback (sourceIsAux)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Original checked tag and arity six exclude each of the real raw
atom selectors. The conclusion supplies literal zero of the physical
selectors in the same scope, not merely failure of numeric evaluation. -/
theorem exact_OpenAuxiliaryNotAtoms (q w r : OTerm α)
    (held : D B Γ (programGraph sourceIsAux (suc z) ![q,w,r])) :
    D B Γ (unary freeTest z q ⊓ unary bottomTest z q) := by
  apply nodeAtCases 6 4 0 ![q,w,r] (unary freeTest z q ⊓ unary bottomTest z q) held
  intro β j Δ fs keep _ shape _
  simp only [conjunctionRename,unaryRename,zRelabel]
  let seed := rawCons (numeral 6) (packedBody fs)
  obtain ⟨eq⟩ := shape
  have a : D B Δ (ltF (z : OTerm β) (numeral 6)) := zeroBelowSuccessor (numeral 5)
  have b : D B Δ (ltF (numeral 3 : OTerm β) (numeral 6)) :=
    successorOrder (numeral 2) (numeral 5)
      (successorOrder (numeral 1) (numeral 4)
        (successorOrder (numeral 0) (numeral 3) (zeroBelowSuccessor (numeral 2))))
  have free : D B Δ (unary freeTest z seed) :=
    nodeTagReject 0 2 (numeral 6) fs (rejectBackwardOrder (numeral 6) z a)
  have bottom : D B Δ (unary bottomTest z seed) :=
    nodeTagReject 3 1 (numeral 6) fs (rejectBackwardOrder (numeral 6) (numeral 3) b)
  obtain ⟨f⟩ := headTransport freeTest z seed (q.relabel j) ![] ⟨symm eq⟩ free
  obtain ⟨t⟩ := headTransport bottomTest z seed (q.relabel j) ![] ⟨symm eq⟩ bottom
  exact ⟨Derivation.conjunctionIntroduction f t⟩

#print axioms exact_OpenAuxiliaryNotAtoms
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAuxShapeProof
