module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedExpansion
open InternalApplicationCertificateConstructorsEvaluationProof InternalAcceptanceCalibrationProof
open OriginalRawSyntaxTransportEvaluationSupportProof OriginalRawSyntaxTransportSelectorProof
open OriginalTypedDecoderEvaluationSupportProof
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem projectionEvaluation {n : Nat} (i : Fin n) (v : List.Vector Nat n) :
    evaluate (.projection i) v = v.get i := rfl

theorem tailOfEvaluation {n : Nat} (P : Program n) (v : List.Vector Nat n) :
    evaluate (.composition InternalListCodec.tailCode (fun _ : Fin 1 => P)) v =
      (Nat.unpair (evaluate P v-1)).2 := by
  rw [unaryCompositionEvaluation,InternalEqualityTestEvaluationProof.vectorOne]
  exact InternalListCodecEvaluationProof.tailEvaluation _

def childNumber (k role typ raw : Nat) : Nat :=
  let tag := (Nat.unpair raw).1
  let dom := (Nat.unpair (Nat.unpair raw).2).1
  if tag=1 then Nat.pair 0 (Nat.unpair (typ-1)).2
  else if tag=2 then Nat.pair 0 (if k=0 then 1+Nat.pair dom typ else dom)
  else if tag=4 ∨ tag=5 then Nat.pair 1 0
  else if tag=7 then (if k=0 then Nat.pair 0 dom else Nat.pair 1 0)
  else Nat.pair role typ

theorem childEvaluation (k role typ raw : Nat) :
    evaluate childAnnotation (ofFn ![k,role,typ,raw]) = childNumber k role typ raw := by
  simp only [childAnnotation,ifSameEvaluation,parentTag,domain,termAnnotation,
    listAnnotation,inherited,evalBranch,leftOfEvaluation,rightOfEvaluation,
    pairOfEvaluation,constantEvaluation,tailOfEvaluation,consOfEvaluation,
    projectionEvaluation,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  unfold childNumber
  by_cases h1 : (Nat.unpair raw).1 = 1
  · simp [h1]
  · by_cases h2 : (Nat.unpair raw).1 = 2
    · simp [h1,h2] <;> split_ifs <;> rfl
    · by_cases h4 : (Nat.unpair raw).1 = 4
      · simp [h1,h2,h4]
      · by_cases h5 : (Nat.unpair raw).1 = 5
        · simp [h1,h2,h4,h5]
        · by_cases h7 : (Nat.unpair raw).1 = 7
          · simp [h1,h2,h4,h5,h7] <;> split_ifs <;> rfl
          · simp [h1,h2,h4,h5,h7]

theorem annotationEvaluation (k role typ raw : Nat) :
    evaluate annotation (ofFn ![k,role,typ,raw]) =
      Nat.pair (annotationValue k role typ raw).1 (annotationValue k role typ raw).2 := by
  simp only [annotation,evalBranch,lessCompositionEvaluation,arityOfEvaluation,
    childEvaluation,inherited,pairOfEvaluation,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  by_cases h : k < OriginalRawSyntaxTransport.arityValue raw
  · simp only [h,ite_true,one_ne_zero,ite_false,annotationValue]
    unfold childNumber
    split_ifs <;> rfl
  · simp [h,annotationValue]

theorem fourInputs (P : Program 4) (k role typ raw job : Nat) :
    evaluate (.composition P ![.projection 0,.projection 1,.projection 2,.projection 3])
      (ofFn ![k,role,typ,raw,job]) = evaluate P (ofFn ![k,role,typ,raw]) := by
  change evaluate P (ofFn fun i : Fin 4 => evaluate
    ((![.projection 0,.projection 1,.projection 2,.projection 3] : Fin 4 → Program 5) i)
      (ofFn ![k,role,typ,raw,job])) = _
  congr 1

theorem decorateEvaluation (k role typ raw job : Nat) :
    evaluate decorate (ofFn ![k,role,typ,raw,job]) = decoratedValue k role typ raw job := by
  rw [decorate,pairOfEvaluation,leftOfEvaluation,pairOfEvaluation,rightOfEvaluation]
  have h : evaluate (.composition annotation ![.projection 0,.projection 1,.projection 2,.projection 3])
      (ofFn ![k,role,typ,raw,job]) =
      Nat.pair (annotationValue k role typ raw).1 (annotationValue k role typ raw).2 := by
    rw [fourInputs,annotationEvaluation]
  rw [h]
  simp only [Nat.unpair_pair,projectionEvaluation,List.Vector.get_ofFn,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    decoratedValue,jobNumber]
  rfl

theorem forgetEvaluation (job : Nat) :
    evaluate forget (ofFn ![job]) = forgetNumber job := by
  rw [forget,rightOfEvaluation,rightOfEvaluation]
  rfl

theorem decorateForgetting : OriginalHereditaryAnnotatedExpansionTargets.DecorateForgetting := by
  intro k role typ raw job
  rw [decorateEvaluation,forgetEvaluation]
  simp only [forgetNumber,decoratedValue,jobNumber,Nat.unpair_pair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionEvaluationProof
