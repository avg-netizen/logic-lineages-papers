module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageProgramProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalUnpairEvaluationProof (exactUnpairEvaluation)
open ID1Completion.InternalPairingEvaluationProof (exactPairingEvaluation)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.NativeProof (appendEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowCoverAlgorithm (applications cells grammar)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverAuxApplicationsNumericProof (exact_AuxApplicationsValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorOne vectorTwo literalEvaluation)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour vectorFive)
open NumberedWindowInternalCoverGrammarStageProgramProof (sameListCode chooseLayerParts)
open NumberedWindowInternalCoverGrammarStageTargets

private theorem reorderOne {n : Nat} (P : Program 1) (i : Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P ![i]) v = evaluate P (v.get i ::ᵥ nil) := by
  change evaluate P (List.Vector.ofFn fun j => v.get ((![i] : Fin 1 → Fin n) j)) = _
  rw [vectorOne]
  rfl

private theorem stepValue (prefix : Program 5) (nextArgs : Program 2) (paid : LayerPartsCalibrated prefix nextArgs)
    (H K ts args : List Nat) (maxNumeral i : Nat) :
    evaluate (grammarStep prefix nextArgs) (i ::ᵥ Nat.pair (numbersNumber ts) (numbersNumber args) ::ᵥ
      numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) =
    Nat.pair (numbersNumber (originalPrefix H K maxNumeral ts args ++ applications K ts))
      (numbersNumber (cells ts args)) := by
  let code := Nat.pair (numbersNumber ts) (numbersNumber args)
  let tape := i ::ᵥ code ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil
  have found := exactUnpairEvaluation code
  have positions : Nat.unpair code = (numbersNumber ts,numbersNumber args) := Nat.unpair_pair _ _
  rw [positions] at found
  have tsValue : evaluate termsBefore tape = numbersNumber ts := by
    rw [termsBefore,reorderOne]
    exact found.1
  have asValue : evaluate argsBefore tape = numbersNumber args := by
    rw [argsBefore,reorderOne]
    exact found.2
  have prefixValue : evaluate (prefixAt prefix) tape = numbersNumber (originalPrefix H K maxNumeral ts args) := by
    change evaluate prefix (List.Vector.ofFn (fun j => evaluate
      ((![.projection 2,.projection 3,.projection 4,termsBefore,argsBefore] : Fin 5 → Program 5) j) tape)) = _
    rw [vectorFive]
    change evaluate prefix (numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ
      evaluate termsBefore tape ::ᵥ evaluate argsBefore tape ::ᵥ nil) = _
    rw [tsValue,asValue]
    exact paid.1 H K maxNumeral ts args
  have suffixValue : evaluate applicationsAt tape = numbersNumber (applications K ts) := by
    rw [applicationsAt,binary,compositeTwo,tsValue]
    exact exact_AuxApplicationsValue K ts
  have allTerms : evaluate (termsAtStep prefix) tape = numbersNumber (originalPrefix H K maxNumeral ts args ++ applications K ts) := by
    rw [termsAtStep,binary,compositeTwo,prefixValue,suffixValue]
    have h := appendEvaluation (numbersNumber (originalPrefix H K maxNumeral ts args)) (applications K ts)
    rw [vectorTwo,numbersRoundTrip] at h
    exact h
  change evaluate (grammarStep prefix nextArgs) tape = _
  rw [grammarStep,binary,compositeTwo,allTerms,binary,compositeTwo,tsValue,asValue,paid.2,exactPairingEvaluation]

theorem exact_GrammarStageValue : ExactGrammarStageValue := by
  intro prefix nextArgs paid H K maxNumeral depth
  induction depth with
  | zero =>
    change evaluate initialLayer (numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) = _
    rw [initialLayer,literalEvaluation]
    rfl
  | succ depth ih =>
    change evaluate (grammarStep prefix nextArgs) (depth ::ᵥ
      evaluate (grammarStage prefix nextArgs) (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) ::ᵥ
      numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) = _
    rw [ih]
    exact stepValue prefix nextArgs paid H K (grammar H K maxNumeral depth).1 (grammar H K maxNumeral depth).2 maxNumeral depth

private theorem canonicalTerms (prefix : Program 5) (nextArgs : Program 2) (paid : LayerPartsCalibrated prefix nextArgs)
    (H K : List Nat) (maxNumeral depth : Nat) :
    evaluate (grammarTerms prefix nextArgs) (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil) =
      numbersNumber (grammar H K maxNumeral depth).1 := by
  change evaluate ID1Completion.InternalUnpair.left (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate (grammarStage prefix nextArgs) (depth ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ maxNumeral ::ᵥ nil)) = _
  rw [vectorOne,exact_GrammarStageValue prefix nextArgs paid, (exactUnpairEvaluation _).1, Nat.unpair_pair]

theorem exact_SelectedGrammarStage : ExactSelectedGrammarStage := by
  obtain ⟨prefix,nextArgs,paid⟩ := chooseLayerParts
  refine ⟨prefix,nextArgs,paid,?_⟩
  intro H K m
  obtain ⟨depth,maxNumeral⟩ := m
  rw [sameListCode H,sameListCode K]
  let mCode := Nat.pair depth maxNumeral
  let tape := numbersNumber H ::ᵥ numbersNumber K ::ᵥ mCode ::ᵥ nil
  let ps : Fin 4 → Program 3 := ![reorder ID1Completion.InternalUnpair.left ![2],.projection 0,.projection 1,
    reorder ID1Completion.InternalUnpair.right ![2] ]
  change Nat.succ (evaluate (grammarTerms prefix nextArgs) (List.Vector.ofFn (fun j => evaluate (ps j) tape))) =
    Nat.succ (Encodable.encode (grammar H K maxNumeral depth).1)
  have found := exactUnpairEvaluation mCode
  have positions : Nat.unpair mCode = (depth,maxNumeral) := Nat.unpair_pair _ _
  rw [positions] at found
  rw [vectorFour]
  change Nat.succ (evaluate (grammarTerms prefix nextArgs)
    (evaluate (reorder ID1Completion.InternalUnpair.left ![2]) tape ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ
      evaluate (reorder ID1Completion.InternalUnpair.right ![2]) tape ::ᵥ nil)) = _
  rw [reorderOne,reorderOne]
  change Nat.succ (evaluate (grammarTerms prefix nextArgs)
    (evaluate ID1Completion.InternalUnpair.left (mCode ::ᵥ nil) ::ᵥ numbersNumber H ::ᵥ numbersNumber K ::ᵥ
    evaluate ID1Completion.InternalUnpair.right (mCode ::ᵥ nil) ::ᵥ nil)) = _
  rw [found.1,found.2,canonicalTerms prefix nextArgs paid,sameListCode]

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverGrammarStageNumericProof
