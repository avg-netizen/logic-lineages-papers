module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultStackEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSupportProof
open Source InternalCanonicalResultFoldCalibration InternalApplicationValidityStack
open InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof InternalAcceptanceCalibrationProof
open InternalApplicationValidityStackEvaluationProof (unaryEvaluation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

 theorem rootDomainEvaluation (v : List.Vector Nat 1) :
    evaluate InternalCanonicalResultFoldOpening.rootDomain v = domainValue (v.get 0) := by
  rw [InternalCanonicalResultFoldOpening.rootDomain,appDomainEvaluation,appBodyEvaluation]
  rfl

 theorem rootCodomainEvaluation (v : List.Vector Nat 1) :
    evaluate InternalCanonicalResultFoldOpening.rootCodomain v = resultTypeValue (v.get 0) := by
  rw [InternalCanonicalResultFoldOpening.rootCodomain,leftOfEvaluation]
  rfl

 theorem functionChildEvaluation (v : List.Vector Nat 1) :
    evaluate InternalCanonicalResultFoldOpening.functionChild v = functionChildValue (v.get 0) := by
  rw [InternalCanonicalResultFoldOpening.functionChild,pairOfEvaluation,consOfEvaluation,
    rootDomainEvaluation,rootCodomainEvaluation,functionPayloadEvaluation,appBodyEvaluation]
  rfl

 theorem argumentChildEvaluation (v : List.Vector Nat 1) :
    evaluate InternalCanonicalResultFoldOpening.argumentChild v = argumentChildValue (v.get 0) := by
  rw [InternalCanonicalResultFoldOpening.argumentChild,pairOfEvaluation,rootDomainEvaluation,
    argumentPayloadEvaluation,appBodyEvaluation]
  rfl

 theorem rootGuardEvaluation (valid member : Program 1) (v : List.Vector Nat 1) :
    evaluate (InternalCanonicalResultFoldOpening.rootGuard valid member) v =
      if evaluate valid v = 1 ∧
          evaluate valid (List.Vector.ofFn ![functionChildValue (v.get 0)]) = 1 ∧
          evaluate valid (List.Vector.ofFn ![argumentChildValue (v.get 0)]) = 1 ∧
          evaluate member (List.Vector.ofFn ![resultTypeValue (v.get 0)]) = 1
      then 1 else 0 := by
  rw [InternalCanonicalResultFoldOpening.rootGuard,conjunctionEvaluation,
    conjunctionEvaluation,conjunctionEvaluation,unaryEvaluation,unaryEvaluation,
    unaryEvaluation,functionChildEvaluation,argumentChildEvaluation,rootCodomainEvaluation]
  split_ifs <;> simp_all

 theorem actualOriginalCanonicalFoldOpeningCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldOpeningCalibration := by
  intro n arity symbols S Gamma table data _ h v
  have hv := InternalCanonicalDescentSelectionEvaluationProof.recursiveValidityCalibration
    n arity symbols S Gamma table data h
  rw [InternalApplicationResultStackEvaluationProof.openGuardEvaluation,
    InternalApplicationResultStackEvaluationProof.openGuardEvaluation,
    rootGuard,rootGuardEvaluation,hv.1,hv.1,hv.1,h.2.1]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero]
  by_cases ht : tagValue (v.get 0) = 2
  · have ha := InternalApplicationValidityStackInvariantProof.sourceAppAcceptance
      n arity symbols S Gamma (v.get 0) ht
    by_cases hs : InternalOriginalStepGuard.sourceValidityValue
        n arity symbols S Gamma (v.get 0) = 1
    · have hh := ha.mp hs
      simp only [ht,hs,hh.1,hh.2.1,hh.2.2,and_self,ite_true]
    · simp only [ht,hs,false_and,and_false,ite_false,Nat.zero_ne_one]
  · simp only [ht,false_and,ite_false]

 theorem leafCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (v : List.Vector Nat 1) :
    evaluate (leaf data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma (v.get 0) :=
  InternalCanonicalDescentSelectionEvaluationProof.actualOriginalCanonicalDescentCalibration
    n arity symbols S Gamma table data hc h v

 theorem combineCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data)
    (hc : SubtypeClosed (fun tau => tau ∈ S))
    (h : InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data)
    (v : List.Vector Nat 4) :
    evaluate (combine data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.applicationValue v) := by
  change evaluate (leaf data) (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate InternalApplicationCertificateConstructors.application v) = _
  rw [leafCalibration n arity symbols S Gamma table data hc h]
  simp only [List.Vector.get_ofFn,applicationEvaluation]

 theorem actualOriginalCanonicalFoldLeafCombineCalibration :
    InternalCanonicalResultFoldCalibrationTargets.ActualOriginalCanonicalFoldLeafCombineCalibration := by
  intro n arity symbols S Gamma table data hc h
  exact ⟨leafCalibration n arity symbols S Gamma table data hc h,
    combineCalibration n arity symbols S Gamma table data hc h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationSupportProof
