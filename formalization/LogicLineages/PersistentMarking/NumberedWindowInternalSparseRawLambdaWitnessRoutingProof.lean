module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaRunTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaWitnessRoutingProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc zeroNeSuc sucNeZeroApply)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelope (nodeGood applyUnary exactBody)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (packedBody)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (canonicalCell)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparseRawTick (rootTest tagFiveTest)
open NumberedWindowInternalSparseRawFunctionFrameOpenReportsProof (onTape)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalSparseRawLambdaFrame (witnessTerm liftedTape)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem disagrees (child : OTerm α) (tag : Nat)
    (diff : ∀ (Δ : List (Formula α)), Derivation B Δ (eqn (numeral 1) (numeral tag)) →
      Derivation B Δ ⊥) :
    Nonempty (Derivation B Γ (unary (nodeGood (literal 1 tag) 1) z (witnessTerm child))) := by
  let w := witnessTerm child
  let p : Program 1 := .composition equalityTest ![cellHead,literal 1 tag]
  let q := applyUnary (exactBody 1) cellTail
  let H := unary (conjunction cellGood (conjunction p q)) (suc z) w
  change Nonempty (Derivation B Γ (unary (conjunction cellGood (conjunction p q)) z w))
  apply conjunctionReject cellGood (conjunction p q) ![w]
  obtain ⟨cell⟩ := canonicalCell (body := B) (Γ := Γ) (numeral 1) (packedBody [child])
  have h : Nonempty (Derivation B (H :: Γ) H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨a⟩ := conjunctionRecover cellGood (conjunction p q) ![w] h
  obtain ⟨b⟩ := conjunctionRecover p q ![w] ⟨Derivation.conjunctionRight a⟩
  have saw : Nonempty (Derivation B (H :: Γ) (unary cellHead (numeral 1) w)) :=
    withHyp ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight cell)⟩ H
  have expect : Nonempty (Derivation B (H :: Γ) (unary (literal 1 tag) (numeral tag) w)) :=
    literalGraph tag ![w]
  have eq := compositionRecover equalityTest ![cellHead,literal 1 tag] (suc z) ![w]
    ![numeral 1,numeral tag] (show Nonempty (Derivation B (H :: Γ) (unary p (suc z) w)) from
      ⟨Derivation.conjunctionLeft b⟩)
    (fun i => Fin.cases saw (Fin.cases expect (fun j => Fin.elim0 j)) i)
  obtain ⟨e⟩ := equalityOfAcceptance (numeral 1) (numeral tag) eq
  exact ⟨Derivation.implicationIntroduction (diff (H :: Γ) e)⟩

/-- The actual tag-one original witness fails both earlier literal tick
dispatch guards on the same physical source/witness/destination tape. -/
theorem exact_OpenLambdaWitnessRouting (dom src child dst : OTerm α) :
    let xs := liftedTape dom src child dst
    Nonempty (Derivation B Γ (programGraph rootTest z xs)) ∧
      Nonempty (Derivation B Γ (programGraph tagFiveTest z xs)) := by
  let xs := liftedTape dom src child dst
  have no0 := disagrees (B := B) (Γ := Γ) child 0 (fun _ d => sucNeZeroApply d)
  have no5 := disagrees (B := B) (Γ := Γ) child 5 (fun _ d => zeroNeSuc (cancelSuc d))
  exact ⟨onTape (nodeGood (literal 1 0) 1) 1 z xs no0,
    onTape (nodeGood (literal 1 5) 1) 1 z xs no5⟩

#print axioms exact_OpenLambdaWitnessRouting
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawLambdaWitnessRoutingProof
