module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorEvaluationProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalLambdaConstructor OriginalLambdaConstructorTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem packedEvaluation (v : List.Vector Nat 3) :
    evaluate packedLambda v = Nat.pair (1 + Nat.pair (v.get 0) (v.get 1))
      (Nat.pair 1 (Nat.pair (v.get 0) (v.get 2))) := by
  unfold packedLambda
  rw [pairOfEvaluation,consOfEvaluation,pairOfEvaluation,pairOfEvaluation]
  rfl

theorem constructorEvaluation (v : List.Vector Nat 3) :
    evaluate constructor v = Nat.pair (1 + Nat.pair (v.get 0) (v.get 1))
      (Nat.pair 1 (Nat.pair (v.get 0) (Nat.unpair (v.get 2)).2)) := by
  change evaluate packedLambda (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((![Program.projection 0,.projection 1,rightOf (.projection 2)] : Fin 3 → Program 3) i) v) = _
  rw [packedEvaluation]
  change Nat.pair (1 + Nat.pair (v.get 0) (v.get 1))
    (Nat.pair 1 (Nat.pair (v.get 0) (evaluate (rightOf (.projection 2)) v))) = _
  rw [rightOfEvaluation]
  rfl

theorem tagEvaluation (v : List.Vector Nat 1) :
    evaluate tag v = (Nat.unpair (Nat.unpair (v.get 0)).2).1 := by
  unfold tag
  rw [leftOfEvaluation,rightOfEvaluation]
  rfl

theorem domainEvaluation (v : List.Vector Nat 1) :
    evaluate domain v = (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).1 := by
  unfold domain
  rw [leftOfEvaluation,rightOfEvaluation,rightOfEvaluation]
  rfl

theorem payloadEvaluation (v : List.Vector Nat 1) :
    evaluate bodyPayload v = (Nat.unpair (Nat.unpair (Nat.unpair (v.get 0)).2).2).2 := by
  unfold bodyPayload
  rw [rightOfEvaluation,rightOfEvaluation,rightOfEvaluation]
  rfl

theorem bodyEvaluation (v : List.Vector Nat 2) :
    evaluate bodyCode v = Nat.pair (v.get 0)
      (Nat.unpair (Nat.unpair (Nat.unpair (v.get 1)).2).2).2 := by
  unfold bodyCode
  rw [pairOfEvaluation]
  change Nat.pair (v.get 0)
    (evaluate bodyPayload (List.Vector.ofFn fun _ : Fin 1 => v.get 1)) = _
  rw [payloadEvaluation]
  rfl

theorem actualOriginalLambdaConstructorRawCalibration : ActualOriginalLambdaConstructorRawCalibration := by
  refine ⟨?_,?_,?_⟩
  · intro d e b
    exact constructorEvaluation (List.Vector.ofFn ![d,e,b])
  · intro out
    exact ⟨tagEvaluation (List.Vector.ofFn ![out]),
      domainEvaluation (List.Vector.ofFn ![out]),payloadEvaluation (List.Vector.ofFn ![out])⟩
  · intro e out
    exact bodyEvaluation (List.Vector.ofFn ![e,out])

theorem actualOriginalLambdaConstructorTypedCalibration : ActualOriginalLambdaConstructorTypedCalibration := by
  intro n arity Gamma sigma tau body
  dsimp only
  rw [constructorEvaluation,tagEvaluation,domainEvaluation,bodyEvaluation]
  simp [packedNumber,codeNumber,termCode,typeNumber,Nat.unpair_pair]
  change (typeNumber tau = typeNumber tau ∧
    (Nat.unpair (Nat.pair (typeNumber tau) (codeNumber (termCode body)))).2 =
      codeNumber (termCode body)) ∧
    (Nat.unpair (Nat.unpair (Nat.unpair
      (Nat.pair (1 + Nat.pair (typeNumber sigma) (typeNumber tau))
        (Nat.pair 1 (Nat.pair (typeNumber sigma) (codeNumber (termCode body)))))).2).2).2 =
      codeNumber (termCode body)
  simp only [Nat.unpair_pair, and_self]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorEvaluationProof
