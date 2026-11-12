module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryExpansionDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointDeletionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
open OriginalHereditaryEvaluatorFixedPointTargets

theorem rangeMapAt (bound : Nat) (f g : Nat → Nat) (k : Nat) (hk : k < bound)
 (h : (List.range bound).map f = (List.range bound).map g) : f k = g k := by
 induction bound generalizing f g k with
 | zero => omega
 | succ bound ih =>
   rw [OriginalHereditaryExpansionDeletionProof.rangeFront,List.map_cons,List.map_cons,List.map_map,List.map_map] at h
   cases k with
   | zero => exact (List.cons.inj h).1
   | succ k =>
     exact ih (fun k => f (Nat.succ k)) (fun k => g (Nat.succ k)) k (by omega) (List.cons.inj h).2

theorem deletionEquality : DeletionEquality := by
 intro R n arity c binders tail sigma q r h
 have hr := OriginalHereditaryEvaluatorFixedPointProof.rowEquality R c q r h
 simp only [value] at hr
 rw [OriginalHereditaryDeletionRowsBoundProof.nativeRows,
   OriginalHereditaryDeletionRowsBoundProof.nativeRows] at hr
 simp only [Nat.unpair_pair,OriginalHereditaryObservationSourceRowsProof.lengthAtContext] at hr
 have hm := NumberedMultisetNumericTotalityProof.encodingInjective hr
 unfold OriginalHereditaryDeletionRows.values at hm
 have hc := rangeMapAt _ _ _ binders.length (by simp) hm
 rw [← OriginalTypedDecoderReconstructionLocalProof.contextNumber,
   OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
   OriginalHereditaryDeletionRowsNativeProof.observationPrefix,
   OriginalClassContextPrefixNativeProof.erasedPackedOnTyped n arity binders tail sigma q,
   OriginalClassContextPrefixNativeProof.erasedPackedOnTyped n arity binders tail sigma r,
   OriginalTypedDecoderReconstructionLocalProof.contextNumber] at hc
 exact hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointDeletionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointDeletionProof
