module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairEvaluationProof (exactUnpairEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverAlgorithm (grammar)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverNamedLeavesTargets (idsAt boundSuccessor)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange)
open NumberedWindowInternalCoverAscendingRangeNumericThinProof (exact_CoverAscendingRangeValue)
open NumberedWindowInternalCoverSelectedSuccessorTargets (selectedStep termsValue)
open NumberedWindowInternalCoverSelectedSuccessorNumericProof (exact_SelectedCoverSuccessorValue)
open NumberedWindowInternalCoverGrammarStageTargets (initialLayer termsBefore argsBefore)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne vectorTwo literalEvaluation)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFive)
open NumberedWindowInternalCoverSelectedGrammarTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem idsValue (K : List Nat) (M : Nat) :
    evaluate idsAt (numbersNumber K ::ᵥ M ::ᵥ nil) = numbersNumber (List.range (M+1)) := by
  change evaluate ascendingRange (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate boundSuccessor (numbersNumber K ::ᵥ M ::ᵥ nil)) = _
  rw [vectorOne]
  change evaluate ascendingRange ((M+1) ::ᵥ nil) = _
  exact exact_CoverAscendingRangeValue (M+1)

theorem exact_SelectedCoverGrammarRowValue : ExactSelectedCoverGrammarRowValue := by
  intro H K ts args i M
  let code := Nat.pair (numbersNumber ts) (numbersNumber args)
  let xs := i ::ᵥ code ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil
  have found := exactUnpairEvaluation code
  have positions : Nat.unpair code = (numbersNumber ts,numbersNumber args) := Nat.unpair_pair _ _
  rw [positions] at found
  have terms : evaluate termsBefore xs = numbersNumber ts := by
    rw [termsBefore,reorderValue,vectorOne]
    exact found.1
  have args' : evaluate argsBefore xs = numbersNumber args := by
    rw [argsBefore,reorderValue,vectorOne]
    exact found.2
  have ids : evaluate selectedIds xs = numbersNumber (List.range (M+1)) := by
    rw [selectedIds,reorderValue,vectorTwo]
    exact idsValue K M
  change evaluate selectedStep (List.Vector.ofFn fun q => evaluate (selectedRowInputs q) xs) = _
  rw [vectorFive]
  change evaluate selectedStep (numbersNumber H ::ᵥ numbersNumber K ::ᵥ
    evaluate selectedIds xs ::ᵥ evaluate termsBefore xs ::ᵥ evaluate argsBefore xs ::ᵥ nil) = _
  rw [ids,terms,args']
  exact exact_SelectedCoverSuccessorValue H K (List.range (M+1)) ts args

theorem exact_SelectedCoverGrammarValue : ExactSelectedCoverGrammarValue := by
  intro H K depth M
  induction depth with
  | zero =>
    change evaluate initialLayer (numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil) = _
    rw [initialLayer,literalEvaluation]
    rfl
  | succ depth ih =>
    change evaluate selectedGrammarRow (depth ::ᵥ
      evaluate selectedGrammar (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil) ::ᵥ
      numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil) = _
    rw [ih]
    exact exact_SelectedCoverGrammarRowValue H K (grammar H K M depth).1 (grammar H K M depth).2 depth M

theorem exact_SelectedCoverGrammarOutputValues : ExactSelectedCoverGrammarOutputValues := by
  intro H K depth M
  let p := grammar H K M depth
  let xs := depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ M ::ᵥ nil
  have code : evaluate selectedGrammar xs = Nat.pair (numbersNumber p.1) (numbersNumber p.2) :=
    exact_SelectedCoverGrammarValue H K depth M
  have reads := exactUnpairEvaluation (Nat.pair (numbersNumber p.1) (numbersNumber p.2))
  rw [Nat.unpair_pair] at reads
  constructor
  · change evaluate left (List.Vector.ofFn fun _ : Fin 1 => evaluate selectedGrammar xs) = _
    rw [vectorOne,code]
    exact reads.1
  · change evaluate right (List.Vector.ofFn fun _ : Fin 1 => evaluate selectedGrammar xs) = _
    rw [vectorOne,code]
    exact reads.2

#print axioms exact_SelectedCoverGrammarRowValue
#print axioms exact_SelectedCoverGrammarValue
#print axioms exact_SelectedCoverGrammarOutputValues

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumericProof
