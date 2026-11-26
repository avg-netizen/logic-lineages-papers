module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverTypeLeavesNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryLayerNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNumberedLayerNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalRawListRecursionEvaluationProof (actualRawListRecursionEvaluation)
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open ID1Completion.InternalPairingEvaluationProof (exactPairingEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowCoverAlgorithm (namedLeaves leaves lambdas ordinary numbered applications cells)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowInternalCoverAuxApplicationsTargets (binary reorder)
open NumberedWindowInternalCoverAuxApplicationsNumericThinProof (exact_AuxApplicationsValue)
open NumberedWindowInternalCoverArgumentCellsNumericProof (exact_CoverArgumentCellsValue)
open NumberedWindowInternalCoverTypeLeavesNumericProof (exact_CoverTypeLeavesValue)
open NumberedWindowInternalCoverOrdinaryLayerNumericProof (taggedLayerValue exact_CoverOrdinaryLayerValue)
open NumberedWindowInternalCoverNumberedLayerNumericProof (exact_CoverNumberedLayerValue)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorOne vectorTwo)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour vectorFive)
open NumberedWindowInternalCoverSelectedSuccessorTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem appendFold (xs ys : List Nat) :
    xs.foldr (fun h rest => 1 + Nat.pair h rest) (numbersNumber ys) = numbersNumber (xs ++ ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons,List.cons_append,numbersNumber,ih]

private theorem appendValue (xs ys : List Nat) :
    evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) = numbersNumber (xs ++ ys) := by
  have h := actualRawListRecursionEvaluation
    1 (.projection 0) appendStep (numbersNumber ys ::ᵥ nil) (numbersNumber xs)
  change evaluate append (numbersNumber xs ::ᵥ numbersNumber ys ::ᵥ nil) = _ at h
  rw [h,numbersRoundTrip]
  have hs (head rest : Nat) : evaluate appendStep
      (head ::ᵥ rest ::ᵥ numbersNumber ys ::ᵥ nil) = 1 + Nat.pair head rest :=
    consEvaluation head rest
  simp only [hs]
  exact appendFold xs ys

private theorem joinValue (P Q : Program 5) (xs : List.Vector Nat 5) (l r : List Nat)
    (hp : evaluate P xs = numbersNumber l) (hq : evaluate Q xs = numbersNumber r) :
    evaluate (join P Q) xs = numbersNumber (l ++ r) := by
  rw [join,binary,compositeTwo,hp,hq]
  exact appendValue l r

private theorem stageValues (H K ids ts args : List Nat) :
    let xs := numbersNumber H ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil
    evaluate nonAuxPart xs = numbersNumber (leaves K ids ++ lambdas K ts ++ ordinary H args ++ numbered H K ids args) ∧
    evaluate termsPart xs = numbersNumber (termsValue H K ids ts args) ∧
    evaluate argsPart xs = numbersNumber (cells ts args) := by
  let xs := numbersNumber H ::ᵥ numbersNumber K ::ᵥ numbersNumber ids ::ᵥ numbersNumber ts ::ᵥ numbersNumber args ::ᵥ nil
  have f : evaluate freePart xs = numbersNumber (namedLeaves 0 K ids) := by
    rw [freePart,reorderValue,vectorTwo]
    exact taggedLayerValue 0 K ids
  have b : evaluate boundPart xs = numbersNumber (namedLeaves 1 K ids) := by
    rw [boundPart,reorderValue,vectorTwo]
    exact taggedLayerValue 1 K ids
  have g : evaluate typePart xs = numbersNumber (K.map fun ty => packNode 3 [ty]) := by
    rw [typePart,reorderValue,vectorOne]
    exact exact_CoverTypeLeavesValue K
  have w : evaluate lambdaPart xs = numbersNumber (lambdas K ts) := by
    rw [lambdaPart,reorderValue,vectorTwo]
    exact taggedLayerValue 2 K ts
  have o : evaluate ordinaryPart xs = numbersNumber (ordinary H args) := by
    rw [ordinaryPart,reorderValue,vectorTwo]
    exact exact_CoverOrdinaryLayerValue H args
  have n : evaluate numberedPart xs = numbersNumber (numbered H K ids args) := by
    rw [numberedPart,reorderValue,vectorFour]
    exact exact_CoverNumberedLayerValue H K ids args
  have u : evaluate auxiliaryPart xs = numbersNumber (applications K ts) := by
    rw [auxiliaryPart,reorderValue,vectorTwo]
    exact exact_AuxApplicationsValue K ts
  have a : evaluate argsPart xs = numbersNumber (cells ts args) := by
    rw [argsPart,reorderValue,vectorTwo]
    exact exact_CoverArgumentCellsValue ts args
  have names := joinValue freePart boundPart xs _ _ f b
  have leaf := joinValue namedPart typePart xs _ _ names g
  have first := joinValue leavesPart lambdaPart xs _ _ leaf w
  have second := joinValue throughLambda ordinaryPart xs _ _ first o
  have nonAux := joinValue throughOrdinary numberedPart xs _ _ second n
  have terms := joinValue nonAuxPart auxiliaryPart xs _ _ nonAux u
  refine ⟨?_,?_,a⟩
  · change evaluate (join throughOrdinary numberedPart) xs = _
    simpa only [leaves,List.append_assoc] using nonAux
  · change evaluate (join nonAuxPart auxiliaryPart) xs = _
    simpa only [termsValue,leaves,List.append_assoc] using terms

theorem exact_SelectedCoverNonAuxValue : ExactSelectedCoverNonAuxValue := by
  intro H K ids ts args
  exact (stageValues H K ids ts args).1

theorem exact_SelectedCoverSuccessorValue : ExactSelectedCoverSuccessorValue := by
  intro H K ids ts args
  have h := (stageValues H K ids ts args).2
  rw [selectedStep,binary,compositeTwo,h.1,h.2]
  exact exactPairingEvaluation _ _

#print axioms exact_SelectedCoverNonAuxValue
#print axioms exact_SelectedCoverSuccessorValue

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSuccessorNumericProof
