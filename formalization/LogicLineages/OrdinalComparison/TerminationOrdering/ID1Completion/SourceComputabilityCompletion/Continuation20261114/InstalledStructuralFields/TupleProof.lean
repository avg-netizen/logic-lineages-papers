module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.LambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.StructuralExchangeFields.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentLayerInstallation.TupleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.TupleProof
open Source InternalOriginalUniformParameterLeaves TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨Q,hQ⟩ := Proof.allPrimitiveFunctions 2 _ (SeededPrimaryPool.NativeProof.candidatesValuePrimitive n arity)
  obtain ⟨R,hR⟩ := Proof.allPrimitiveFunctions 2 _ (ExchangeNumericSuppliers.PrimitiveProof.rankPrimitive n)
  obtain ⟨D,hD⟩ := Proof.allPrimitiveFunctions 2 _ (ExchangeNumericSuppliers.PrimitiveProof.depsPrimitive n)
  obtain ⟨U,V,hU,hV,hJold⟩ := TransparentLayerInstallation.SelectionProof.supplierSelection n arity
  obtain ⟨C,K,hC,hK⟩ := InstalledExchangeRecursor.SupplierProof.supplierSelection n
  have hJ := (StructuralExchangeFields.NativeProof.nativeFields n arity U V hU hV).2
  let J := StructuralExchangeFields.layer U V
  have hLambda : Targets.LambdaAt U V := LambdaProof.internalLambda U V
  have hApplication : Targets.ApplicationAt U V := by
    intro body alpha Delta cons
    exact StructuralExchangeFields.InternalProof.internalApplication body alpha Delta U V cons
  have hX := TransparentLayerInstallation.TupleProof.recursorCalibration n arity R D J hR hD hJ
  let B := InstalledExchangeRecursor.structural R D J C K
  have hB : ∀ v, evaluate B v = TypedPrimaryEdge.structuralValue n arity v :=
    InstalledExchangeRecursor.NativeProof.nativeStructural n arity R D J C K hX hC hK
  let T := OriginalTypedDecoder.target H G
  let P := SeededPrimaryPool.pool T Q
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hP := SeededPrimaryPool.NativeProof.poolCalibration n arity T Q hT hQ
  have hs : TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P (TypedPrimaryEdge.edge B) :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity P hP,hP,
      TypedPrimaryEdge.NativeProof.edgeCalibration n arity B hB⟩
  have hL := TransparentPrimary.NativeProof.calibration n arity T (LengthAlignedPrimary.countOfPool P)
    P (TypedPrimaryEdge.edge B) hT hs
  have hretain := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (SeededPrimaryPool.primary T Q (TypedPrimaryEdge.edge B)) hp hH hG hW hL
  exact ⟨Q,R,D,U,V,C,K,hQ,hR,hD,hU,hV,hC,hK,hJ,hLambda,hApplication,hB,hs,hL,hretain⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.TupleProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledStructuralFields.TupleProof
