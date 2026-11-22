module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldNumericThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsNumericThinProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalListCodecEvaluationProof (consEvaluation)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowFieldAlgorithm (packNode)
open NumberedWindowCoverAlgorithm (applications)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo vectorThree literalEvaluation)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalSparsePairEvaluationProof (consValue)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap)
open NumberedWindowInternalCoverCartesianFoldNumericThinProof (fixedCartesianFoldValue)
open NumberedWindowInternalCoverAuxApplicationsTargets

private theorem reorderValue {m n : Nat} (P : Program m) (slots : Fin m → Fin n) (v : List.Vector Nat n) :
    evaluate (reorder P slots) v = evaluate P (List.Vector.ofFn fun i => v.get (slots i)) := rfl

private theorem nodeValue (d c f a : Nat) :
    evaluate auxCode (a ::ᵥ d ::ᵥ c ::ᵥ f ::ᵥ nil) = packNode 6 [d,c,f,a] := by
  simp only [auxCode,binary,compositeTwo,literalEvaluation]
  repeat rw [consValue]
  rfl

private theorem singletonValue (d c f a : Nat) :
    evaluate singletonAux (a ::ᵥ d ::ᵥ c ::ᵥ f ::ᵥ nil) = numbersNumber [packNode 6 [d,c,f,a]] := by
  rw [singletonAux,binary,compositeTwo,nodeValue]
  exact consEvaluation _ 0

private theorem actualArgAxis (T : List Nat) (d c f : Nat) :
    evaluate argAxis (f ::ᵥ numbersNumber T ::ᵥ d ::ᵥ c ::ᵥ nil) =
      numbersNumber (T.map (fun a => packNode 6 [d,c,f,a])) := by
  rw [argAxis,reorderValue,vectorFour]
  change evaluate (flatMap singletonAux) (numbersNumber T ::ᵥ d ::ᵥ c ::ᵥ f ::ᵥ nil) = _
  rw [fixedCartesianFoldValue singletonAux (fun a => [packNode 6 [d,c,f,a]]) T (d ::ᵥ c ::ᵥ f ::ᵥ nil)
    (fun a => singletonValue d c f a)]
  rw [List.map_eq_flatMap]

private theorem actualFnAxis (K T : List Nat) (d c : Nat) :
    evaluate fnAxis (c ::ᵥ numbersNumber K ::ᵥ numbersNumber T ::ᵥ d ::ᵥ nil) =
      numbersNumber (T.flatMap (fun f => T.map (fun a => packNode 6 [d,c,f,a]))) := by
  rw [fnAxis,reorderValue,vectorFour]
  change evaluate (flatMap argAxis) (numbersNumber T ::ᵥ numbersNumber T ::ᵥ d ::ᵥ c ::ᵥ nil) = _
  exact fixedCartesianFoldValue argAxis _ T _ (actualArgAxis T d c)

private theorem actualCodAxis (K T : List Nat) (d : Nat) :
    evaluate codAxis (d ::ᵥ numbersNumber K ::ᵥ numbersNumber T ::ᵥ nil) =
      numbersNumber (K.flatMap (fun c => T.flatMap (fun f => T.map (fun a => packNode 6 [d,c,f,a])))) := by
  rw [codAxis,reorderValue,vectorFour]
  change evaluate (flatMap fnAxis) (numbersNumber K ::ᵥ numbersNumber K ::ᵥ numbersNumber T ::ᵥ d ::ᵥ nil) = _
  exact fixedCartesianFoldValue fnAxis _ K _ (actualFnAxis K T d)

theorem exact_AuxApplicationsValue : ExactAuxApplicationsValue := by
  intro K T
  rw [auxApplications,reorderValue,vectorThree]
  change evaluate (flatMap codAxis) (numbersNumber K ::ᵥ numbersNumber K ::ᵥ numbersNumber T ::ᵥ nil) = _
  exact fixedCartesianFoldValue codAxis _ K _ (actualCodAxis K T)

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsNumericThinProof
