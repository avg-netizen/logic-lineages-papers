module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsProof
open Source Source.SourceMarkedSyntax NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedTypedRequests

private theorem bindPairSome {A B C : Type} (a : Option A) (b : Option B) (f : A → B → C) :
    (a.bind (fun x => b.bind (fun y => some (f x y)))).isSome = (a.isSome && b.isSome) := by
  cases a <;> cases b <;> rfl

theorem termExpansion : NumberedTypedRequestsTargets.ActualTermExpansion := by
  intro n arity Gamma tau code
  cases code with
  | var index =>
    simp only [decodeTerm, Option.isSome_map, expandedValid, expand]
    rw [NumberedVariableDecoderPrimrecProof.variableSuccessCalibration]
    split <;> simp_all [valid]
  | lam sigma body =>
    cases tau <;> simp [decodeTerm, expandedValid, expand, valid]
    split <;> simp_all [valid]
  | app sigma q a =>
    simp only [decodeTerm, expandedValid, expand, valid, List.all_cons, List.all_nil,
      Bool.and_true, bind, pure]
    exact bindPairSome _ _ _
  | bottom result =>
    simp [decodeTerm, expandedValid, expand]
    split <;> simp_all [valid]
  | ordinary head base =>
    simp [decodeTerm, expandedValid, expand, valid]
    split <;> simp_all [valid]
  | numbered k head result base types extras =>
    simp only [decodeTerm, expandedValid, expand]
    split <;> simp_all only [Option.isSome_none]
    simp only [valid, List.all_cons, List.all_nil, Bool.and_true, bind, pure]
    exact bindPairSome _ _ _
  | argumentsNil => rfl
  | argumentsCons sigma q rest => rfl

theorem argumentsExpansion : NumberedTypedRequestsTargets.ActualArgumentsExpansion := by
  intro n arity Gamma types code
  cases code <;> cases types <;>
    simp [decodeArguments, expandedValid, expand, valid]
  split <;> simp_all [valid, bind, pure, bindPairSome]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedRequestsProof
