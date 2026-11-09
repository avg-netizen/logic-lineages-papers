module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ParameterSliceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalOriginalUniformDescentSelectionEvaluationProof
open InternalOriginalUniformCanonicalResultFoldEvaluationProof
open InternalParameterizedCanonicalResultFold (rootGuard leaf combine foldN actualJ)
open SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

/-- The actual decoded raw leaves and the original canonical leaves have
the SAME semantic values. No equation between their Context codes is used. -/
theorem decodedAtomic (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx) (Gamma : List Ty)
    (ho : ∀ value : Nat, parameterObject value parameter = some (Gamma,value)) :
    ParameterSlice.Atomic data parameter (parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2) := by
  have hp := decodedLeafSlice n arity data hc parameter ctx hctx Gamma ho
  have hq := InternalOriginalUniformDescentSelectionEvaluationProof.leafSlice
    n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2
  refine ⟨?_,?_,?_⟩
  · intro value
    exact (hp value).2.2.1.trans (hq value).2.2.1.symm
  · intro value
    exact (decodedValiditySlice n arity data hc parameter ctx hctx Gamma ho value).trans
      (actualOriginalUniformValidityCalibration
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 value).2.symm
  · intro typ
    exact (hp typ).2.2.2.trans (hq typ).2.2.2.symm

/-- The distinct target validator is supplied by its actual old-target
slice, not inferred from source validity or the three-callback congruence. -/
theorem decodedTargetValidity (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (parameter : Nat) (ctx : OrdinaryArithmeticQuotient.Context n)
    (hctx : Encodable.decode (Nat.unpair parameter).1 = some ctx) (Gamma : List Ty)
    (ho : ∀ value : Nat, parameterObject value parameter = some (Gamma,value)) (value : Nat) :
    evaluate (InternalOriginalUniformDescentSelection.targetValidity data)
        (ofFn ![value,parameter]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value := by
  have hs := decodedLeafSlice n arity data hc parameter ctx hctx Gamma ho
  exact (InternalParameterizedApplicationValidityFoldCalibrationProof.actualOriginalParameterizedValidityFoldCalibration
    n arity ctx.1.1 ctx.1.2 Gamma data.oldSource data.oldTarget data.member parameter
    (fun x => (hs x).1) (fun x => (hs x).2.1) (fun x => (hs x).2.2.2) value).1

/-- All-input actualJ is one original combine after the literal argument
fold. Its raw function, domain and codomain are unrestricted and unchanged. -/
theorem canonicalApplication (n : Nat) (arity : Fin n → Nat) (data : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity data)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (domain codomain function argument : Nat) :
    evaluate (actualJ data)
        (ofFn ![domain,codomain,function,argument,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.applicationValue (ofFn ![domain,codomain,function,
          InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma argument])) := by
  change evaluate (combine data)
    (ofFn ![domain,codomain,function,
      evaluate (foldN data) (ofFn ![argument,parameterCode symbols S Gamma table]),
      parameterCode symbols S Gamma table]) = _
  rw [(actualOriginalUniformCanonicalResultFoldCalibration
    n arity data hc symbols S Gamma table hS argument).1]
  exact InternalOriginalUniformCanonicalResultFoldSupportProof.combineCalibration
    n arity data hc symbols S Gamma table hS domain codomain function _

/-- One actual decoded Gamma precedes EVERY raw input in the frozen
semantic package. Only native evaluations are transferred; no internal
graph reflection, source selection or application-success claim occurs. -/
theorem actualDecodedCompositeCalibration :
    DecodedSourceCalibrationTargets.ActualDecodedCompositeCalibration := by
  intro n arity data hc parameter ctx hctx hS
  obtain ⟨Gamma,ho⟩ := parameterGamma parameter
  have hs := ParameterSliceProof.actualOriginalCompositeParameterSliceCongruence data parameter
    (parameterCode ctx.1.1 ctx.1.2 Gamma ctx.2)
    (decodedAtomic n arity data hc parameter ctx hctx Gamma ho)
  refine ⟨Gamma,{
    objectSlice := ho
    targetValidity := ?_
    sourceValidity := ?_
    representative := ?_
    scalar := ?_
    typed := ?_
    fold := ?_
    goodRun := ?_
    application := ?_ }⟩
  · exact decodedTargetValidity n arity data hc parameter ctx hctx Gamma ho
  · exact decodedValiditySlice n arity data hc parameter ctx hctx Gamma ho
  · intro value
    exact (hs.representative value).trans
      (actualOriginalUniformRepresentativeCalibration
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS value)
  · intro value
    exact (hs.scalar value).trans
      (SourceComputabilityCompletion.RawScalarEvaluationProof.actualOriginalRawScalarCalibration
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS value)
  · intro value typ
    exact (hs.typed value typ).trans
      (actualOriginalUniformTypedCalibration
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS value typ)
  · intro value
    exact (hs.fold value).trans
      (actualOriginalUniformCanonicalResultFoldCalibration
        n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS value).1
  · intro value
    exact InternalParameterizedApplicationResultFoldCalibrationProof.actualOriginalParameterizedResultFoldGoodRunCalibration
      (rootGuard data) (leaf data) (combine data) value parameter
  · intro domain codomain function argument
    exact (hs.application domain codomain function argument).trans
      (canonicalApplication n arity data hc ctx.1.1 ctx.1.2 Gamma ctx.2 hS
        domain codomain function argument)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.DecodedSourceCalibrationProof
