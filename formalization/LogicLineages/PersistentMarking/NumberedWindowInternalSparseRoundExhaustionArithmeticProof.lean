module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundChargeArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionArithmeticProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof
open ID1Completion.InternalTagArithmeticSupportProof
open ID1Completion.InternalOriginalOrderSyntaxProof
open ID1Completion.InternalSquareRootArithmeticSupportProof
open ID1Completion.InternalAdditionLawsProof ID1Completion.InternalUnpairArithmeticProof
open ID1Completion.InternalPositiveUnfoldingSupportProof
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount
open ID1Completion.InternalControlGraphSupportProof (zeroSuccessorCases)
open ID1Completion.InternalOriginalOrderProof (actualOriginalOrderIntroduction)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The arithmetic exhaustion rule from the original finite-descent proof. -/
theorem budgetZero (size remaining : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (bounded (add size remaining) size))) :
    Nonempty (Derivation body Delta (eqn remaining z)) := by
  apply zeroSuccessorCases Delta remaining
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩
  · intro beta j Theta predecessor hj he
    simp only [eqnRelabel,zRelabel]
    have hb' := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta hj
    simp only [OrderProof.boundedRename,InternalOriginalOrderSyntaxProof.addRelabel] at hb'
    obtain ⟨he⟩ := he
    have hp : Nonempty (Derivation body Theta
        (ltF (size.relabel j) (add (size.relabel j) (suc predecessor)))) := by
      apply actualOriginalOrderIntroduction body beta Theta (size.relabel j)
        (add (size.relabel j) (suc predecessor)) predecessor
      rw [InternalSourceInversionSupportProof.onEquality]
      exact ⟨refl _⟩
    obtain ⟨hp⟩ := hp
    have hstrict := orderRight (size.relabel j) (congAddLeft (size.relabel j) (symm he)) hp
    exact InternalOriginalPairingOrderArithmeticProof.strictWeakConflict
      (size.relabel j) (add (size.relabel j) (remaining.relabel j)) _ ⟨hstrict⟩
      (OrderProof.strictNext (add (size.relabel j) (remaining.relabel j)) (size.relabel j) hb')

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundExhaustionArithmeticProof
