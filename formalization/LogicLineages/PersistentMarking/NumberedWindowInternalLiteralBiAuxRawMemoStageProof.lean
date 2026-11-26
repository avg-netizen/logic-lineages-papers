module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue outputTransport successorValue)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalAuxExchangeMemoStepTargets
  (unaryAfter binaryAfter rawSource rawTarget currentKey packedKey)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralTypedMemoStageProof
open NumberedWindowInternalLiteralTypedContextUpdateProof (contextUpdate)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- An untyped lift of the original exchange callback: the new arm is
only a pair of syntactically valid auxiliaries with the actual earlier
original exchange paid at either matching child position. Every other
evaluation calls the original directed exchange unchanged. -/
def rawAuxMemoGate (V : Program 1) : Program 4 :=
  conjunction (unaryAfter termShape rawSource)
    (conjunction (unaryAfter V rawSource)
      (conjunction (unaryAfter V rawTarget) (typedMemoStage (constantOne 4))))

def rawAuxMemoStage (X : Program 2) (V : Program 1) : Program 4 :=
  branch (rawAuxMemoGate V) (binaryAfter X rawSource rawTarget) (constantOne 4)

theorem exact_OpenBiAuxRawMemoStage (X : Program 2) (V : Program 1) (old prev q r : OTerm α)
    (key : D B Γ (eqn (suc prev) (pairTerm q r)))
    (shape : D B Γ (unary termShape (suc z) q))
    (left : D B Γ (unary V (suc z) q))
    (right : D B Γ (unary V (suc z) r))
    (inner : D B Γ (acceptEdge (stageGuard (constantOne 4)) (carrierTerm z old prev) z q r)) :
    D B Γ (contextUpdate (rawAuxMemoStage X V) (suc z) z prev old) := by
  let xs : Fin 4 → OTerm α := ![prev,old,z,z]
  have k : D B Γ (programGraph currentKey (suc prev) xs) :=
    unaryGraph .succ (.projection 0) (suc prev) prev xs (successorValue ![prev]) (projectionValue 0 xs)
  have selected := outputTransport currentKey (suc prev) (pairTerm q r) xs key k
  have packed : D B Γ (programGraph packedKey (rawCons q r) xs) :=
    unaryGraph .succ currentKey (rawCons q r) (pairTerm q r) xs (successorValue ![pairTerm q r]) selected
  obtain ⟨decoded⟩ := canonicalCell (body := B) (Γ := Γ) q r
  have a := unaryGraph cellHead packedKey q (rawCons q r) xs
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight decoded)⟩ packed
  have b := unaryGraph cellTail packedKey r (rawCons q r) xs
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight decoded)⟩ packed
  have gate : D B Γ (programGraph (rawAuxMemoGate V) (suc z) xs) :=
    conjunctionAccept (unaryAfter termShape rawSource) _ xs (unaryGraph termShape rawSource (suc z) q xs shape a)
      (conjunctionAccept (unaryAfter V rawSource) _ xs (unaryGraph V rawSource (suc z) q xs left a)
        (conjunctionAccept (unaryAfter V rawTarget) _ xs (unaryGraph V rawTarget (suc z) r xs right b)
          ((exact_OpenTypedMemoStage (constantOne 4) z old prev q r key).mpr inner)))
  exact successorBranchIntro (rawAuxMemoGate V) (binaryAfter X rawSource rawTarget) (constantOne 4)
    (suc z) z xs gate (oneConstantValue xs)

#print axioms exact_OpenBiAuxRawMemoStage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxRawMemoStageProof
