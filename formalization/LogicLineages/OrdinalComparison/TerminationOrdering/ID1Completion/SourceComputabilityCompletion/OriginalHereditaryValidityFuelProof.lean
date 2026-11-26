module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSumBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityFuelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open OriginalHereditaryValidity InternalPairingSumBounds
open InternalPairingSumBoundsProof InternalPairingSumBoundsArithmeticProof
open InternalRecursionClosureLogicProof InternalUnpairReverseBoundsArithmeticProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalAdditionLawsProof
open InternalSquareRootArithmeticSupportProof

/-- The two literal original pair graphs supply the body count internally.
The context parameter and reconstructed typed child code need not decrease. -/
theorem actualOriginalLambdaPayloadChildFuelBound :
    OriginalHereditaryValidityTargets.ActualOriginalLambdaPayloadChildFuelBound := by
  intro body alpha payload middle d bp
  let premise := lambdaPayloadWitnesses payload middle d bp
  let Gamma := [premise]
  have hp : Derivation body Gamma premise := Derivation.hypothesis List.mem_cons_self
  have houter : Nonempty (Derivation body Gamma (weakBound (add (suc z) middle) payload)) :=
    closedApply (actualOriginalPairingSumBound body alpha payload (suc z) middle)
      ⟨Derivation.conjunctionLeft hp⟩
  have hmiddle : Nonempty (Derivation body Gamma (weakBound (add d bp) middle)) :=
    closedApply (actualOriginalPairingSumBound body alpha middle d bp)
      ⟨Derivation.conjunctionRight hp⟩
  have hb := weakTrans bp (add d bp) middle (rightWeakAdd d bp) hmiddle
  have ht := addWeakLeft (suc z) bp middle hb
  obtain ⟨h⟩ := weakTrans (add (suc z) bp) (add (suc z) middle) payload ht houter
  have he : Derivation body Gamma (eqn (add (suc z) bp) (suc bp)) :=
    trans (leftSuccessor z bp) (congSuc (leftZero bp))
  exact ⟨Derivation.implicationIntroduction (orderLeft (suc payload) he h)⟩

/-- One original opening step is obtained by internal successor monotonicity,
with the exact payload+1 parent fuel and no iteration-success assumption. -/
theorem actualOriginalLambdaPayloadParentFuelBound :
    OriginalHereditaryValidityTargets.ActualOriginalLambdaPayloadParentFuelBound := by
  intro body alpha payload middle d bp
  let premise := lambdaPayloadWitnesses payload middle d bp
  have h : Nonempty (Derivation body [premise] (weakBound (suc bp) payload)) :=
    closedApply (actualOriginalLambdaPayloadChildFuelBound body alpha payload middle d bp)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := successorWeak (suc bp) payload h
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityFuelProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityFuelProof
