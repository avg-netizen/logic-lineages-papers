module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.SupplierProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.TupleProof
open Source InternalOriginalUniformParameterLeaves TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨Q,hQ⟩ := Proof.allPrimitiveFunctions 2 _ (SeededPrimaryPool.NativeProof.candidatesValuePrimitive n arity)
  obtain ⟨R,D,J,hR,hD,hJ,hX,hOriginal⟩ := ExchangeSelectedRecursor.NativeProof.concreteSelection n arity
  obtain ⟨V,K,hV,hK⟩ := SupplierProof.supplierSelection n
  let B := structural R D J V K
  have hB : ∀ v, evaluate B v = TypedPrimaryEdge.structuralValue n arity v :=
    NativeProof.nativeStructural n arity R D J V K hX hV hK
  let T := OriginalTypedDecoder.target H G
  let P := SeededPrimaryPool.pool T Q
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hP := SeededPrimaryPool.NativeProof.poolCalibration n arity T Q hT hQ
  have hs : TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P (TypedPrimaryEdge.edge B) :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity P hP,hP,
      TypedPrimaryEdge.NativeProof.edgeCalibration n arity B hB⟩
  have hL := TransparentPrimary.NativeProof.calibration n arity T (LengthAlignedPrimary.countOfPool P)
    P (TypedPrimaryEdge.edge B) hT hs
  have hr := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (SeededPrimaryPool.primary T Q (TypedPrimaryEdge.edge B)) hp hH hG hW hL
  exact ⟨Q,R,D,J,V,K,hQ,hR,hD,hJ,hV,hK,hB,hs,hL,hr⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.TupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.TupleProof
