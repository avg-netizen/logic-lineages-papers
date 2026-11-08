module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSemanticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationProof
open Source InternalCanonicalResultFoldCalibration
open InternalOriginalStepGuard InternalQuotientEdgeChecker
open InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (exactOneEvaluation zeroEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem actualOriginalCanonicalFoldOpeningCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldOpeningCalibration :=
  InternalCanonicalResultFoldCalibrationSupportProof.actualOriginalCanonicalFoldOpeningCalibration

 theorem actualOriginalCanonicalFoldLeafCombineCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldLeafCombineCalibration :=
  InternalCanonicalResultFoldCalibrationSupportProof.actualOriginalCanonicalFoldLeafCombineCalibration

 theorem actualOriginalSemanticCanonicalFoldCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalSemanticCanonicalFoldCalibration :=
  InternalCanonicalResultFoldCalibrationSemanticProof.actualOriginalSemanticCanonicalFoldCalibration

/-- Consume the checked generic bounded-fold equation at the exact frozen
G/D/D(rawApp) syntax. No semantic correctness or successful-run premise. -/
 theorem normalizerCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (v : List.Vector Nat 1) :
    evaluate (normalizer data) v =
      targetRepresentativeValue n arity symbols S Gamma (v.get 0) := by
  calc
    _ = evaluate (normalizer data) (List.Vector.ofFn ![v.get 0]) :=
      congrArg (evaluate (normalizer data))
        (InternalRepresentativeFoldCalibrationProof.unaryVector v)
    _ = InternalApplicationResultFoldCalibration.semanticFold
        (fun x => evaluate (rootGuard data) (List.Vector.ofFn ![x]))
        (fun x => evaluate (leaf data) (List.Vector.ofFn ![x]))
        (fun d e f a => evaluate (combine data) (List.Vector.ofFn ![d,e,f,a])) (v.get 0) :=
      (InternalApplicationResultFoldCalibrationEvaluationProof.actualOriginalBoundedResultFoldCalibration
        (rootGuard data) (leaf data) (combine data) (v.get 0)).2
    _ = _ := actualOriginalSemanticCanonicalFoldCalibration
      n arity symbols S Gamma table data hc h (v.get 0)

/-- This external all-input success equation does not reflect into the
internal calculus. The exact singleton-run theorem supplies it directly. -/
 theorem goodRunCalibration (data : InternalCanonicalDescentSelection.Data)
    (v : List.Vector Nat 1) : evaluate (goodRun data) v = 1 := by
  calc
    _ = evaluate (goodRun data) (List.Vector.ofFn ![v.get 0]) :=
      congrArg (evaluate (goodRun data))
        (InternalRepresentativeFoldCalibrationProof.unaryVector v)
    _ = 1 :=
      InternalApplicationCertifiedResultFoldClosureCalibrationProof.actualOriginalResultFoldGoodRunCalibration
        (rootGuard data) (leaf data) (combine data) (v.get 0)

 theorem actualOriginalCanonicalFoldProgramCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldProgramCalibration := by
  intro n arity symbols S Gamma table data hc h v
  exact ⟨normalizerCalibration n arity symbols S Gamma table data hc h v,
    goodRunCalibration data v⟩

 theorem actualOriginalCanonicalFoldDataCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldDataCalibration := by
  intro n arity symbols S Gamma table data hc h
  have hv := InternalCanonicalDescentSelectionEvaluationProof.recursiveValidityCalibration
    n arity symbols S Gamma table data h
  have hn := normalizerCalibration n arity symbols S Gamma table data hc h
  refine ⟨hv,⟨h.2.2.1,?_,hn⟩,
    InternalCanonicalDescentSelectionEvaluationProof.actualOriginalCanonicalDescentTypedCalibration
      n arity symbols S Gamma table data hc h⟩
  intro v
  change evaluate (InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne
      (InternalCanonicalDescentSelection.validity data).sourceValid)
    (InternalAcceptance.constantZero 1) (normalizer data)) v = _
  rw [evalBranch,exactOneEvaluation,hv.1,zeroEvaluation,hn,
    InternalRepresentativeFoldCalibrationProof.sourceFromTarget]
  by_cases hs : sourceValidityValue n arity symbols S Gamma (v.get 0) = 1 <;>
    simp only [hs,ite_true,ite_false,Nat.one_ne_zero]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationProof
