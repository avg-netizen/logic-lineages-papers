module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeafMeasureDispatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentOpenProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept constantZeroValue)
open ID1Completion.InternalPairing (pairing)
open ID1Completion.InternalPairingSupportProof (pairingOfNotLess)
open ID1Completion.InternalApplicationValidityStackAppendTransitionProof (notLessZero)
open ID1Completion.InternalControlGraphProof (zeroTestAtZero)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (makeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeavesTargets (typeLeafTerm)
open NumberedWindowInternalCoverTypeLeafMeasureDispatchProof (exact_OpenCoverTypeLeafMeasureDispatch)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (selectedArgsMeasure)
open NumberedWindowInternalCoverSingletonTypeArgumentTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem singletonCodePair : Nonempty (Derivation body Γ
    (codePair singletonMeasureCode (numeral 2 : OTerm α) z)) :=
  pairingOfNotLess (numeral 2) z (notLessZero (numeral 2))

private theorem literalGuard (ty : OTerm α) :
    Nonempty (Derivation body Γ (unary singletonTypeGuard (suc z) (singletonTypeKey ty))) := by
  let q := typeLeafTerm ty
  let raw := singletonTypeKey ty
  let Z := LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.zeroTest
  obtain ⟨cell⟩ := canonicalCell (body := body) (Γ := Γ) q z
  have head := (exact_OpenCoverTypeLeafMeasureDispatch body α Γ ty z).2.2
  have hh := makeUnary (header 3 1) cellHead (suc z) raw q head
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩
  have tail : Nonempty (Derivation body Γ (unary Z (suc z) (z : OTerm α))) :=
    zeroTestAtZero z ⟨refl z⟩
  have tt := makeUnary Z cellTail (suc z) raw z tail
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight cell)⟩
  exact conjunctionAccept cellGood (conjunction (applyUnary (header 3 1) cellHead) (applyUnary Z cellTail))
    ![raw] ⟨Derivation.conjunctionLeft cell⟩
    (conjunctionAccept (applyUnary (header 3 1) cellHead) (applyUnary Z cellTail) ![raw] hh tt)

theorem exact_OpenCoverSingletonTypeArgument : ExactOpenCoverSingletonTypeArgument := by
  intro A body α Γ ty
  let raw := singletonTypeKey ty
  have paired : Nonempty (Derivation body Γ (unary singletonPair20 singletonMeasureCode raw)) := by
    apply compositionValue pairing ![literal 1 2,constantZero 1] singletonMeasureCode ![raw]
      ![numeral 2,z] singletonCodePair
    intro i
    exact Fin.cases (literalGraph 2 ![raw])
      (Fin.cases (constantZeroValue ![raw]) (fun j => Fin.elim0 j)) i
  have chosen := successorBranchIntro singletonTypeGuard A singletonPair20 singletonMeasureCode z ![raw]
    (literalGuard ty) paired
  exact successorBranchIntro (.projection 0) (constantZero 1) (singletonTypeArgs A)
    singletonMeasureCode _ ![raw] (projectionValue 0 ![raw]) chosen

#print axioms singletonCodePair
#print axioms exact_OpenCoverSingletonTypeArgument

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeArgumentOpenProof
