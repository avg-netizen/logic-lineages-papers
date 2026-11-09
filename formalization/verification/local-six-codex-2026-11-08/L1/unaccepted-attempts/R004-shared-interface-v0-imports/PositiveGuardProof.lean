module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardProof
open Source NumberedQuotientPaths NumberedCopyCertificate NumberedQuotientPathCertificates
open PositiveGuard PositiveGuardNativeSupportProof PositiveGuardEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalAllInputPositiveGuardCalibration :
    PositiveGuardTargets.ActualOriginalAllInputPositiveGuardCalibration := by
  intro n arity bottom measure edge hc symbols S Gamma table parameter hS he x y certificate
  let v : List.Vector Nat 4 := List.Vector.ofFn ![x,y,certificate,parameter]
  have hp := InternalParameterizedPathCheckerEvaluationProof.actualOriginalParameterizedPositivePathCheckerEvaluation
    n arity symbols S Gamma table edge parameter he x y certificate
  change evaluate (InternalParameterizedPathChecker.checker edge true) v = _ at hp
  change evaluate (checker bottom measure edge) v = _
  rw [checker,conjunctionEvaluation,conjunctionEvaluation,hp]
  cases hn : positivePathTest n arity symbols S Gamma table x y certificate with
  | false => simp [hn]
  | true =>
    have hpath := (NumberedQuotientPathCertificatesProof.numericPositivePathCertificates
      n arity symbols S Gamma table x y).mp ⟨certificate,hn⟩
    have hb := positiveNotBottom n arity bottom measure hc symbols S Gamma hS (tableAbove table) x y hpath
    have hspine := positiveSpine n arity bottom measure hc symbols S Gamma hS (tableAbove table) x y hpath
    have hbottom : evaluate (nonBottomGuard bottom) v = 1 := by
      rw [nonBottomEvaluation]
      simpa only [v,List.Vector.get_ofFn,Matrix.cons_val_zero,if_neg hb]
    have hs : evaluate (spineGuard measure) v = 1 := by
      rw [spineGuardEvaluation]
      simp only [v,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one]
      by_cases hx : flagValue measure x = 1
      · obtain ⟨hy,hd⟩ := hspine hx
        simp only [hx,hy,hd,ite_true,and_self]
      · simp only [hx,ite_false]
    simp only [hn,hbottom,hs,ite_true,and_self]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PositiveGuardProof
