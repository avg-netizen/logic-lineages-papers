module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationSupportProof
open OriginalHereditaryValidity InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (oneEvaluation zeroEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Composition evaluation at the exact vector of the component outputs. -/
theorem unaryCompositionEvaluation {n : Nat} (p : Program 1) (q : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p (fun _ : Fin 1 => q)) v =
      evaluate p (List.Vector.ofFn ![evaluate q v]) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate q v) = _
  congr 1

theorem binaryCompositionEvaluation {n : Nat} (p : Program 2) (q r : Program n)
    (v : List.Vector Nat n) :
    evaluate (.composition p ![q,r]) v =
      evaluate p (List.Vector.ofFn ![evaluate q v,evaluate r v]) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 2 => evaluate (![q,r] i) v) = _
  have hv : (List.Vector.ofFn fun i : Fin 2 => evaluate (![q,r] i) v) =
      List.Vector.ofFn ![evaluate q v,evaluate r v] := by
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) i <;> rfl
  rw [hv]

theorem exactOneEvaluation {n : Nat} (p : Program n) (v : List.Vector Nat n) :
    evaluate (exactOne p) v = if evaluate p v = 1 then 1 else 0 :=
  InternalApplicationValidityStackEvaluationProof.exactOneEvaluation p v

theorem statusEvaluation (v : List.Vector Nat 1) :
    evaluate status v = (Nat.unpair (v.get 0)).1 := leftEvaluation v

theorem workEvaluation (v : List.Vector Nat 1) :
    evaluate work v = (Nat.unpair (v.get 0)).2 := rightEvaluation v

theorem currentFrameEvaluation (v : List.Vector Nat 1) :
    evaluate currentFrame v = (Nat.unpair (evaluate work v - 1)).1 := by
  change evaluate InternalListCodec.headCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate work v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.headEvaluation]

theorem restEvaluation (v : List.Vector Nat 1) :
    evaluate rest v = (Nat.unpair (evaluate work v - 1)).2 := by
  change evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate work v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.tailEvaluation]

theorem currentRawEvaluation (v : List.Vector Nat 1) :
    evaluate currentRaw v = (Nat.unpair (evaluate currentFrame v)).1 := by
  rw [currentRaw, leftOfEvaluation]

theorem currentParameterEvaluation (v : List.Vector Nat 1) :
    evaluate currentParameter v = (Nat.unpair (evaluate currentFrame v)).2 := by
  rw [currentParameter, rightOfEvaluation]

theorem currentTypeEvaluation (v : List.Vector Nat 1) :
    evaluate currentType v = resultTypeValue (evaluate currentRaw v) := by
  rw [currentType, leftOfEvaluation]
  rfl

theorem currentTagEvaluation (v : List.Vector Nat 1) :
    evaluate currentTag v = tagValue (evaluate currentRaw v) := by
  rw [currentTag, unaryCompositionEvaluation,
    OriginalLambdaConstructorEvaluationProof.tagEvaluation]
  rfl

theorem currentDomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentDomain v = domainValue (evaluate currentRaw v) := by
  rw [currentDomain, unaryCompositionEvaluation,
    OriginalLambdaConstructorEvaluationProof.domainEvaluation]
  rfl

theorem currentFunctionEvaluation (v : List.Vector Nat 1) :
    evaluate currentFunction v = functionChildValue (evaluate currentRaw v) := by
  rw [currentFunction, pairOfEvaluation, consOfEvaluation, currentDomainEvaluation,
    currentTypeEvaluation, functionPayloadEvaluation, appBodyEvaluation]
  rfl

theorem currentArgumentEvaluation (v : List.Vector Nat 1) :
    evaluate currentArgument v = argumentChildValue (evaluate currentRaw v) := by
  rw [currentArgument, pairOfEvaluation, currentDomainEvaluation,
    argumentPayloadEvaluation, appBodyEvaluation]
  rfl

theorem currentCodomainEvaluation (v : List.Vector Nat 1) :
    evaluate currentCodomain v = lambdaCodomainValue (evaluate currentRaw v) := by
  change evaluate InternalListCodec.tailCode
    (List.Vector.ofFn fun _ : Fin 1 => evaluate currentType v) = _
  rw [vectorOne, InternalListCodecEvaluationProof.tailEvaluation, currentTypeEvaluation]
  rfl

theorem currentBodyEvaluation (v : List.Vector Nat 1) :
    evaluate currentBody v = lambdaBodyValue (evaluate currentRaw v) := by
  rw [currentBody, binaryCompositionEvaluation,
    OriginalLambdaConstructorEvaluationProof.bodyEvaluation]
  change Nat.pair (evaluate currentCodomain v)
    (Nat.unpair (Nat.unpair (Nat.unpair (evaluate currentRaw v)).2).2).2 = _
  rw [currentCodomainEvaluation]
  rfl

theorem childParameterEvaluation (v : List.Vector Nat 1) :
    evaluate childParameter v =
      childParameterValue (evaluate currentRaw v) (evaluate currentParameter v) := by
  rw [childParameter, pairOfEvaluation, leftOfEvaluation, consOfEvaluation,
    currentDomainEvaluation, rightOfEvaluation]
  rfl

theorem nodeCheckEvaluation (oldSource oldTarget member : Program 2)
    (v : List.Vector Nat 1) :
    evaluate (nodeCheck oldSource oldTarget member) v =
      nodeCheckValue
        (fun value parameter => evaluate oldSource (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate oldTarget (List.Vector.ofFn ![value,parameter]))
        (fun value parameter => evaluate member (List.Vector.ofFn ![value,parameter]))
        (evaluate currentRaw v) (evaluate currentParameter v) := by
  simp only [nodeCheck, conjunctionEvaluation, exactOneEvaluation,
    binaryCompositionEvaluation, evalBranch, sameEvaluation, currentTagEvaluation,
    currentTypeEvaluation, twoEvaluation, oneEvaluation, nodeCheckValue]
  split_ifs <;> simp_all

theorem poppedEvaluation (v : List.Vector Nat 1) :
    evaluate popped v = Nat.pair 1 (evaluate rest v) := by
  rw [popped, pairOfEvaluation, oneEvaluation]

theorem applicationExpandedEvaluation (v : List.Vector Nat 1) :
    evaluate applicationExpanded v = Nat.pair 1
      (1 + Nat.pair
        (Nat.pair (functionChildValue (evaluate currentRaw v)) (evaluate currentParameter v))
        (1 + Nat.pair
          (Nat.pair (argumentChildValue (evaluate currentRaw v)) (evaluate currentParameter v))
          (evaluate rest v))) := by
  rw [applicationExpanded, pairOfEvaluation, oneEvaluation, consOfEvaluation,
    pairOfEvaluation, currentFunctionEvaluation, consOfEvaluation,
    pairOfEvaluation, currentArgumentEvaluation]

theorem lambdaExpandedEvaluation (v : List.Vector Nat 1) :
    evaluate lambdaExpanded v = Nat.pair 1
      (1 + Nat.pair (Nat.pair (lambdaBodyValue (evaluate currentRaw v))
        (childParameterValue (evaluate currentRaw v) (evaluate currentParameter v)))
        (evaluate rest v)) := by
  rw [lambdaExpanded, pairOfEvaluation, oneEvaluation, consOfEvaluation,
    pairOfEvaluation, currentBodyEvaluation, childParameterEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityEvaluationSupportProof
