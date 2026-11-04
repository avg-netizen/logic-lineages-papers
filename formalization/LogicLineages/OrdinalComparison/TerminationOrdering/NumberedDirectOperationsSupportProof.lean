module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsSupportProof
open Source NumberedAuxiliaryCoding NumberedRewriteSyntax NumberedRewriteReduction
open NumberedAuxiliaryShift NumberedDirectCertificate NumberedDirectOperations

theorem typedArgumentAppend : NumberedDirectOperationsTargets.ActualTypedArgumentAppend := by
  intro Symbol arity Gamma xs ys a b
  induction xs with
  | nil => cases a; rfl
  | cons sigma xs ih => cases a with
    | cons q rest => exact congrArg (Code.argumentsCons sigma (termCode q)) (ih rest)

theorem typedOpeningCalibration : NumberedDirectOperationsTargets.ActualTypedOpeningCalibration := by
  intro Symbol arity Gamma k f sigma tau base types extras
  have hb : argumentsCode (renameArguments base (Renaming.weaken Gamma sigma))=shiftCode 0 (argumentsCode base) := by
    simpa only [prefixWeakening,List.nil_append,List.length_nil] using
      (NumberedAuxiliaryShiftSupportProof.argumentShiftCalibration Symbol arity [] Gamma _ sigma base)
  have he : argumentsCode (renameArguments extras (Renaming.weaken Gamma sigma))=shiftCode 0 (argumentsCode extras) := by
    simpa only [prefixWeakening,List.nil_append,List.length_nil] using
      (NumberedAuxiliaryShiftSupportProof.argumentShiftCalibration Symbol arity [] Gamma types sigma extras)
  simp only [openNumbered,termCode]
  rw [typedArgumentAppend,hb,he]
  rfl

theorem abstractionCodeCalibration : NumberedDirectOperationsTargets.ActualAbstractionCodeCalibration := by
  intro n arity Gamma q
  rcases q with ⟨tau,q⟩
  cases q with
  | var v => rfl
  | lam body => rfl
  | app f a => rfl
  | bottom tau => rfl
  | ordinary f base => rfl
  | numbered k f tau base types extras =>
    cases k with
    | zero => rfl
    | succ k => cases tau with
      | ground => rfl
      | arrow sigma tau =>
        simp only [termCode,abstractionCode,directTarget,Option.map_some]
        rw [typedOpeningCalibration]

theorem putCodeCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (label : Nat)
    (q : Packed (Fin n) arity Gamma) :
    putCode label q.1 (termCode q.2)=(directTarget arity Gamma (.put label) q).map (fun r => termCode r.2) := by
  rcases q with ⟨tau,q⟩
  cases q <;> rfl

theorem bottomCodeCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (q : Packed (Fin n) arity Gamma) :
    bottomCode q.1 (termCode q.2)=(directTarget arity Gamma .bottom q).map (fun r => termCode r.2) := by
  rcases q with ⟨tau,q⟩
  cases q <;> rfl

theorem directTypePreservation (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (rule : DirectRule) (q r : Packed (Fin n) arity Gamma) (h : directTarget arity Gamma rule q=some r) : r.1=q.1 := by
  have hi := (NumberedDirectCertificateProof.directRuleCheck n arity Gamma rule q r).mp h
  cases hi <;> rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectOperationsSupportProof
