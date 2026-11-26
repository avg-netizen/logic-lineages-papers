module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderSourceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderWindowSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderHeadSelectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesContextGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelSourceProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedFiniteUniverse
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorFibreCountermodel OriginalUniverseDecoder
theorem sourceAt (H G : Program 1) (M W : Program 2)
 (hH : OriginalTypedDecoder.HeadSignatureCalibrated 1 arity H)
 (hG : OriginalTypedDecoder.ContextGuardCalibrated 1 G)
 (hM : ContextMemberCalibrated 1 M) (hW : HeadWindowCalibrated 1 arity W)
 (q : Packed (Fin 1) arity []) (hu : InUniverse context.1.1 context.1.2 q.2) :
 evaluate (source H G M W) (List.Vector.ofFn ![packedNumber q,parameter]) = 1 := by
 rw [OriginalUniverseDecoderSourceCalibrationProof.sourceCalibration 1 arity H G M W hH hG hM hW]
 have hp := OriginalTypedDecoderTargetLeafValuesProof.parameterObjectEncoded (packedNumber q) parameter
   ([] : List Ty) (by simp [parameter,typesNumber])
 have hut := (NumberedNumericCarrierProof.universeTestCorrect (Fin 1) inferInstance arity
   context.1.1 context.1.2 [] q.1 q.2).mpr hu
 simp only [InternalOriginalUniformParameterLeaves.sourceValue,List.Vector.get_ofFn,
   Matrix.cons_val_zero,Matrix.cons_val_one,InternalOriginalUniformParameterLeaves.decodedValue,hp]
 simp only [parameter,contextCode,Nat.unpair_pair,Encodable.encodek]
 simp [NumberedNumericCarrier.rawCarrierTest,NumberedNumericCarrier.decodeUniverse,
   NumberedNumericDecodingProof.packedNumericRoundTrip,hut]
theorem actualSource : EvaluatorFibreCountermodelTargets.ActualSource := by
 obtain ⟨H,hH⟩ := OriginalTypedDecoderHeadSelectionProof.actualOriginalTypedHeadSelection 1 arity
 obtain ⟨G,hG⟩ := OriginalVariableLeavesContextGuardProof.actualOriginalVariableContextGuardSelection 1
 obtain ⟨W,hW⟩ := OriginalUniverseDecoderWindowSelectionProof.actualOriginalUniverseWindowSelection 1 arity
 obtain ⟨s,t,r,member,hcal,_⟩ := InternalOriginalUniformParameterLeavesProof.actualOriginalUniformLeafPrograms 1 arity
 let M := InternalOriginalUniformContextMembership.contextMember member
 have hM : ContextMemberCalibrated 1 M :=
   OriginalUniverseDecoderGuardCalibrationProof.originalMemberCalibration 1 member hcal.2.2.2
 have hw := EvaluatorFibreCountermodelWindowProof.actualWindow
 refine ⟨H,G,M,W,hH,hG,hM,hW,?_,?_,?_,?_,?_,?_⟩
 · rw [hG]
   simp [contextCode]
 · rw [hM]
   simpa [contextCode,context] using OriginalUniverseDecoderGuardCalibrationProof.memberEncoded 1 context Ty.ground
 · rw [hW]
   have he := OriginalUniverseDecoderGuardCalibrationProof.windowEncoded 1 arity context (.ranked (0 : Fin 1))
   simpa only [contextCode,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
     NumberedAuxiliaryCoding.decodeHead,hw.2.2.1,decide_true,Bool.toNat_true] using he
 · rw [hW]
   have he := OriginalUniverseDecoderGuardCalibrationProof.windowEncoded 1 arity context (.zero : NumberedAuxiliaryCoding.HeadCode (Fin 1))
   simpa only [contextCode,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,
     NumberedAuxiliaryCoding.decodeHead,hw.2.2.2.1,decide_true,Bool.toNat_true] using he
 · exact sourceAt H G M W hH hG hM hW leftTerm hw.2.2.2.2.1
 · exact sourceAt H G M W hH hG hM hW rightTerm hw.2.2.2.2.2
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorFibreCountermodelSourceProof
