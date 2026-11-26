module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverEvaluationProof
open Source InternalOriginalUniformParameterLeaves
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open InternalAcceptanceCalibrationProof InternalApplicationStepPeelEvaluationSupportProof OriginalActiveClassKernelEvaluationProof
open OriginalClassContextObserver OriginalClassContextNativeDefinitions
open OriginalContextExtensionCalibrationProof OriginalRawObjectTransportEvaluationProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

theorem erasedObjectEvaluation (value parameter : Nat) :
    evaluate erasedObject (ofFn ![value,parameter]) =
      evaluate OriginalRawObjectTransport.eraseObjectRaw
        (ofFn ![Nat.pair (Nat.unpair parameter).2 value]) := by
  change evaluate OriginalRawObjectTransport.eraseObjectRaw
    (ofFn ![evaluate (pairOf (rightOf (.projection 1)) (.projection 0))
      (ofFn ![value,parameter])]) = _
  rw [pairOfEvaluation,rightOfEvaluation]
  rfl

theorem erasedKeyEvaluation (R : Program 2) (value parameter : Nat) :
    evaluate (erasedKey R) (ofFn ![value,parameter]) =
      evaluate R (ofFn ![(Nat.unpair (evaluate erasedObject (ofFn ![value,parameter]))).2,
        Nat.pair (Nat.unpair parameter).1
          (Nat.unpair (evaluate erasedObject (ofFn ![value,parameter]))).1]) := by
  change evaluate R (ofFn ![evaluate (rightOf erasedObject) (ofFn ![value,parameter]),
    evaluate parentParameter (ofFn ![value,parameter])]) = _
  rw [rightOfEvaluation,parentParameter,pairOfEvaluation,leftOfEvaluation,leftOfEvaluation]
  rfl

theorem erasedRankEvaluation (value parameter : Nat) :
    evaluate erasedRank (ofFn ![value,parameter]) =
      evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
        (ofFn ![(Nat.unpair (evaluate erasedObject (ofFn ![value,parameter]))).2]) := by
  change evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
    (ofFn ![evaluate (rightOf erasedObject) (ofFn ![value,parameter])]) = _
  rw [rightOfEvaluation]

theorem erasedObjectSlice (context value : Nat) (Gamma : List Ty) (sigma : Ty) :
    evaluate erasedObject (ofFn ![value,Nat.pair context (Encodable.encode (sigma :: Gamma))]) =
      Nat.pair (Encodable.encode Gamma) (erasedPacked Gamma sigma value) := by
  rw [erasedObjectEvaluation]
  simp only [Nat.unpair_pair]
  have he : (Nat.unpair (evaluate OriginalRawObjectTransport.eraseObjectRaw
      (ofFn ![ContextUniform.objectCode (sigma :: Gamma) value]))).1 = Encodable.encode Gamma := by
    rw [objectEncoding,eraseObjectEvaluation]
    simp only [Nat.unpair_pair,contextEncoding,Nat.succ_sub_one,Nat.unpair_pair]
  rw [← objectEncoding]
  have hp := Nat.pair_unpair (evaluate OriginalRawObjectTransport.eraseObjectRaw
    (ofFn ![ContextUniform.objectCode (sigma :: Gamma) value]))
  rw [he] at hp
  exact hp.symm

theorem erasedKeySlice (R : Program 2) (context value : Nat) (Gamma : List Ty) (sigma : Ty) :
    evaluate (erasedKey R) (ofFn ![value,Nat.pair context (Encodable.encode (sigma :: Gamma))]) =
      evaluate R (ofFn ![erasedPacked Gamma sigma value,Nat.pair context (Encodable.encode Gamma)]) := by
  rw [erasedKeyEvaluation,erasedObjectSlice]
  simp only [Nat.unpair_pair]

theorem erasedRankSlice (context value : Nat) (Gamma : List Ty) (sigma : Ty) :
    evaluate erasedRank (ofFn ![value,Nat.pair context (Encodable.encode (sigma :: Gamma))]) =
      evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
        (ofFn ![erasedPacked Gamma sigma value]) := by
  rw [erasedRankEvaluation,erasedObjectSlice]
  simp only [Nat.unpair_pair]

theorem observerEvaluation (R : Program 2) (v : List.Vector Nat 3) :
    evaluate (observerTest R) v =
      if evaluate (erasedKey R) (ofFn ![v.get 0,v.get 2]) =
          evaluate (erasedKey R) (ofFn ![v.get 1,v.get 2]) ∧
        evaluate erasedRank (ofFn ![v.get 0,v.get 2]) =
          evaluate erasedRank (ofFn ![v.get 1,v.get 2]) then 1 else 0 := by
  rw [observerTest,conjunctionEvaluation,keyEvaluation,keyEvaluation]
  simp

theorem classEvaluation (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) (v : List.Vector Nat 3) :
    evaluate (OriginalClassContextObserver.classTest p H G W P) v =
      if (Nat.unpair (v.get 2)).2 = 0 then evaluate P v else
        if evaluate (OriginalActiveObservedClass.activation p H G W)
            (ofFn ![v.get 0,v.get 2]) = 0 then evaluate P v else
          if evaluate P v = 1 ∧ evaluate (observerTest p.base.oldRepresentative) v = 1
            then 1 else 0 := by
  rw [OriginalClassContextObserver.classTest,evalBranch,rightOfEvaluation,evalBranch,
    seedQueryEvaluation,conjunctionEvaluation]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverEvaluationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverEvaluationProof
