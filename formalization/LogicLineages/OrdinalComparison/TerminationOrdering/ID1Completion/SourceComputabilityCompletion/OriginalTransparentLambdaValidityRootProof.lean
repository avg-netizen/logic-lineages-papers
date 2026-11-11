module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRootProof
open OriginalTransparentLambdaValidity OriginalHereditaryValidity
open OriginalHereditaryValidityEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (oneEvaluation)
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem binaryValueEvaluation (p : Program 2) (v : List.Vector Nat 2) :
    evaluate p v = binaryValue p (v.get 0) (v.get 1) := by
  have hv : v = List.Vector.ofFn ![v.get 0,v.get 1] := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  exact congrArg (evaluate p) hv

theorem resultTypeEvaluation (v : List.Vector Nat 2) :
    evaluate resultType v = resultTypeValue (v.get 0) := by
  rw [resultType, leftOfEvaluation]
  rfl

theorem tagEvaluation (v : List.Vector Nat 2) :
    evaluate tag v = tagValue (v.get 0) := by
  rw [tag, unaryCompositionEvaluation, OriginalLambdaConstructorEvaluationProof.tagEvaluation]
  rfl

theorem domainEvaluation (v : List.Vector Nat 2) :
    evaluate domain v = domainValue (v.get 0) := by
  rw [domain, unaryCompositionEvaluation, OriginalLambdaConstructorEvaluationProof.domainEvaluation]
  rfl

theorem codomainEvaluation (v : List.Vector Nat 2) :
    evaluate codomain v = lambdaCodomainValue (v.get 0) := by
  rw [codomain, unaryCompositionEvaluation, InternalEqualityTestEvaluationProof.vectorOne,
    InternalListCodecEvaluationProof.tailEvaluation,
    resultTypeEvaluation]
  rfl

theorem lambdaShapeEvaluation (v : List.Vector Nat 2) :
    evaluate lambdaShape v = lambdaShapeValue (v.get 0) := by
  rw [lambdaShape, sameEvaluation, consOfEvaluation, resultTypeEvaluation,
    domainEvaluation, codomainEvaluation]
  simp only [lambdaShapeValue, Nat.add_comm 1, Nat.succ_eq_add_one]

theorem sourceRootEvaluation (data : Data) (v : List.Vector Nat 2) :
    evaluate (sourceRoot data) v =
      sourceRootValue (binaryValue data.oldSource) (binaryValue data.member)
        (v.get 0) (v.get 1) := by
  simp only [sourceRoot, evalBranch, sameEvaluation, tagEvaluation, twoEvaluation,
    oneEvaluation, conjunctionEvaluation, lambdaShapeEvaluation, exactOneEvaluation,
    binaryCompositionEvaluation, resultTypeEvaluation, domainEvaluation]
  change (if (if tagValue (v.get 0) = 2 then 1 else 0) = 0 then
    (if (if tagValue (v.get 0) = 1 then 1 else 0) = 0 then evaluate data.oldSource v else
      (if lambdaShapeValue (v.get 0) = 1 ∧
        (if (if binaryValue data.member (resultTypeValue (v.get 0)) (v.get 1) = 1 then 1 else 0) = 1 ∧
            (if binaryValue data.member (domainValue (v.get 0)) (v.get 1) = 1 then 1 else 0) = 1
          then 1 else 0) = 1 then 1 else 0)) else 1) = _
  rw [binaryValueEvaluation data.oldSource v]
  unfold sourceRootValue
  split_ifs <;> simp_all

theorem targetRootEvaluation (data : Data) (v : List.Vector Nat 2) :
    evaluate (targetRoot data) v =
      targetRootValue (binaryValue data.oldTarget) (v.get 0) (v.get 1) := by
  simp only [targetRoot, evalBranch, sameEvaluation, tagEvaluation, twoEvaluation,
    oneEvaluation, lambdaShapeEvaluation]
  rw [binaryValueEvaluation data.oldTarget v]
  unfold targetRootValue
  split_ifs <;> simp_all

theorem actualOriginalTransparentRootCalibration :
    OriginalTransparentLambdaValidityTargets.ActualOriginalTransparentRootCalibration := by
  constructor
  · intro v
    exact ⟨resultTypeEvaluation v, tagEvaluation v, domainEvaluation v,
      codomainEvaluation v, lambdaShapeEvaluation v⟩
  · intro data v
    exact ⟨sourceRootEvaluation data v, targetRootEvaluation data v⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityRootProof
