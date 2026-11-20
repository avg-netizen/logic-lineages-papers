module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputGuardProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerStepSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputNilProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (refl sucNeZeroApply)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalBoundedDescentNormalizerStepSupportProof (conjunctionReject)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparsePositiveOutputTargets
open NumberedWindowInternalSparsePositiveOutputGuardProof (nonemptyCode emptyValue)
open NumberedWindowInternalSparsePositiveOutputTestProof (compareTarget)

attribute [local irreducible] programGraph

theorem rejectNil : OpenPositiveNilReject := by
  intro body raw least α ctx ty source dst
  let xs := args5 ctx ty source z dst
  let ok := programGraph (positive raw least) (suc z) xs
  have bad : Nonempty (Derivation body [] ok.not) := by
    have trueResult : Nonempty (Derivation body [ok] ok) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    change Nonempty (Derivation body [ok]
      (programGraph (ID1Completion.InternalAcceptance.conjunction nonemptyCode
        (compareTarget raw least)) (suc z) xs)) at trueResult
    obtain ⟨selected⟩ := conjunctionRecover nonemptyCode (compareTarget raw least) xs trueResult
    have empty := emptyValue (body := body) (Γ := [ok]) ctx ty source z dst ⟨refl z⟩
    obtain ⟨impossible⟩ := valueUnique nonemptyCode (suc z) z xs ⟨Derivation.conjunctionLeft selected⟩ empty
    exact ⟨Derivation.implicationIntroduction (sucNeZeroApply impossible)⟩
  unfold positive
  exact conjunctionReject nonemptyCode (compareTarget raw least) xs bad

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveOutputNilProof
