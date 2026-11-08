module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalRawListRecursion InternalListCodec InternalListCodecEvaluationProof
open InternalRawListRecursionEvaluationProof InternalListMap
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof NumberedMultisetNumericTotalityProof

attribute [local irreducible] consCode

theorem mapStepEvaluation {k : Nat} (transform : Program (k+1))
    (params : List.Vector Nat k) (head result : Nat) :
    evaluate (mapStep transform) (head ::ᵥ result ::ᵥ params) =
      1 + Nat.pair (evaluate transform (head ::ᵥ params)) result := by
  have hh : evaluate (mapHead transform) (head ::ᵥ result ::ᵥ params) =
      evaluate transform (head ::ᵥ params) := by
    change evaluate transform (List.Vector.ofFn fun i =>
      evaluate ((Fin.cons (Program.projection 0) (fun i => Program.projection i.succ.succ) :
        Fin (k+1) → Program (k+2)) i)
        (head ::ᵥ result ::ᵥ params)) = _
    congr 1
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (fun q => ?_) i <;> simp [evaluate]
  change evaluate consCode (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons (mapHead transform) (Fin.cons (Program.projection 1) Fin.elim0) :
      Fin 2 → Program (k+2)) i)
      (head ::ᵥ result ::ᵥ params)) = _
  rw [vectorTwo,consEvaluation]
  change 1 + Nat.pair (evaluate (mapHead transform) (head ::ᵥ result ::ᵥ params)) result = _
  rw [hh]

theorem mappedFold {k : Nat} (transform : Program (k+1))
    (params : List.Vector Nat k) (xs : List Nat) :
    xs.foldr (fun head result => evaluate (mapStep transform) (head ::ᵥ result ::ᵥ params)) 0 =
      numbersNumber (xs.map (fun head => evaluate transform (head ::ᵥ params))) := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldr_cons,ih,mapStepEvaluation]
    rfl

theorem actualRawListMapEvaluation : InternalListMapTargets.ActualRawListMapEvaluation := by
  intro k transform params code
  rw [InternalListMap.map,actualRawListRecursionEvaluation]
  change ((decodeNumbers code).getD []).foldr
    (fun head result => evaluate (mapStep transform) (head ::ᵥ result ::ᵥ params)) 0 = _
  exact mappedFold transform params _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
