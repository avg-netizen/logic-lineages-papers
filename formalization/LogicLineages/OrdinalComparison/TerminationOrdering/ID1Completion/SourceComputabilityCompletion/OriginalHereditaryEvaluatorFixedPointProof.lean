module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityDependencyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
open OriginalHereditaryEvaluatorFixedPointTargets OriginalHereditaryFiniteObserver
open OriginalHereditaryNativeBoundDefinitions

theorem fixedPoint : FixedPoint := by
 intro R n arity c Gamma q
 let s : State (Fin n) arity := ⟨Gamma,q⟩
 have he := OriginalHereditaryEvaluatorProof.nativeCalibration R n arity c Gamma q
 have hs := OriginalHereditaryFiniteStabilityProof.stable R n arity c s (weight s) (Nat.le_refl _)
 have hd := OriginalHereditaryFiniteStabilityDependencyProof.localDependency R (family R (weight s))
   (evaluator R) n arity c s (by
     intro t ht
     exact (OriginalHereditarySettledObserverProof.stepNormalization R n arity c s t ht).trans
       (OriginalHereditaryEvaluatorProof.nativeCalibration R n arity c t.context t.term).symm)
 exact he.trans (hs.symm.trans hd)

theorem rowEquality (R : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat)
 {Gamma : List Ty} (q r : Packed (Fin n) arity Gamma)
 (h : value (evaluator R) c ⟨Gamma,q⟩ = value (evaluator R) c ⟨Gamma,r⟩) :
 value (OriginalHereditaryDeletionRows.rows (evaluator R)) c ⟨Gamma,q⟩ =
 value (OriginalHereditaryDeletionRows.rows (evaluator R)) c ⟨Gamma,r⟩ := by
 rw [fixedPoint R n arity c Gamma q,fixedPoint R n arity c Gamma r] at h
 simp only [value] at h ⊢
 rw [OriginalHereditaryObservationLayerNativeProof.native,
   OriginalHereditaryObservationLayerNativeProof.native] at h
 have hh := congrArg (fun x => (Nat.unpair (Nat.unpair x).2).2) h
 simpa only [Nat.unpair_pair] using hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointProof
