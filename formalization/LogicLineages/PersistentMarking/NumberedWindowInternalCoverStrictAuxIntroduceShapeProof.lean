module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceShapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (ltTest)
open ID1Completion.InternalLessThanSupportProof (acceptOfLess)
open ID1Completion.InternalControlGraphSupportProof (projectionValue successorValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalSparsePairGraphProof (consGraph)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (termReports)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalAuxMeasureOpenDataProof (bothChildBounds)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph binaryGraph)
open NumberedWindowInternalAuxMeasureStepTargets (childAt shapeCheck earlierAt certain)
open NumberedWindowInternalAuxWindowStepTargets (functionCode argumentCode resultCode)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

structure ExactData (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (xs : Fin 4 → OTerm α) (dom cod fn arg : OTerm α) : Prop where
  shape : Nonempty (Derivation body Γ (programGraph shapeCheck (suc z) xs))
  bothEarlier : Nonempty (Derivation body Γ (programGraph certain (suc z) xs))
  domain : Nonempty (Derivation body Γ (programGraph (childAt 0) dom xs))
  codomain : Nonempty (Derivation body Γ (programGraph (childAt 1) cod xs))
  function : Nonempty (Derivation body Γ (programGraph (childAt 2) fn xs))
  argument : Nonempty (Derivation body Γ (programGraph (childAt 3) arg xs))
  fnCode : Nonempty (Derivation body Γ (programGraph functionCode (suc (rawCons dom cod)) xs))
  argCode : Nonempty (Derivation body Γ (programGraph argumentCode (suc dom) xs))
  result : Nonempty (Derivation body Γ (programGraph resultCode (suc cod) xs))

theorem actualAuxPhysicalData (ctx dom cod fn arg old : OTerm α) :
    ExactData body Γ ![memoPrior dom cod fn arg,old,ctx,z] dom cod fn arg := by
  let prior := memoPrior dom cod fn arg
  let raw := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  have key : Nonempty (Derivation body Γ (programGraph currentKey raw xs)) :=
    unaryGraph .succ (.projection 0) raw prior xs (successorValue ![prior]) (projectionValue 0 xs)
  obtain ⟨tag,fields⟩ := termReports (body := body) (Γ := Γ) dom cod fn arg
  have shape := unaryGraph termShape currentKey (suc z) raw xs tag key
  have f0 := unaryGraph (field 0) currentKey dom raw xs fields.1 key
  have f1 := unaryGraph (field 1) currentKey cod raw xs fields.2.1 key
  have f2 := unaryGraph (field 2) currentKey fn raw xs fields.2.2.1 key
  have f3 := unaryGraph (field 3) currentKey arg raw xs fields.2.2.2.1 key
  have order := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  have lt2 : Nonempty (Derivation body Γ (programGraph (earlierAt 2) (suc z) xs)) :=
    binaryGraph ltTest (childAt 2) currentKey (suc z) fn raw xs (acceptOfLess fn raw order.1) f2 key
  have lt3 : Nonempty (Derivation body Γ (programGraph (earlierAt 3) (suc z) xs)) :=
    binaryGraph ltTest (childAt 3) currentKey (suc z) arg raw xs (acceptOfLess arg raw order.2) f3 key
  have good : Nonempty (Derivation body Γ (programGraph certain (suc z) xs)) :=
    conjunctionAccept shapeCheck (conjunction (earlierAt 2) (earlierAt 3)) xs shape
      (conjunctionAccept (earlierAt 2) (earlierAt 3) xs lt2 lt3)
  let arrow := rawCons dom cod
  have coded := binaryGraph fieldCons (childAt 0) (childAt 1) arrow dom cod xs (consGraph dom cod) f0 f1
  exact ⟨shape,good,f0,f1,f2,f3,
    unaryGraph .succ _ (suc arrow) arrow xs (successorValue ![arrow]) coded,
    unaryGraph .succ _ (suc dom) dom xs (successorValue ![dom]) f0,
    unaryGraph .succ _ (suc cod) cod xs (successorValue ![cod]) f1⟩

#print axioms actualAuxPhysicalData

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceShapeProof
