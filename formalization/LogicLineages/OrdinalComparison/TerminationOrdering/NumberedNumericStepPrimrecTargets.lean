module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecTargets
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedStepCertificate
open NumberedNumericStep NumberedNumericStepPrimrec

/-- Every actual typed step test, including focus, replacement and selector failure. -/
def ActualStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau) (certificate : StepCertificate),
    stepCodeTest n arity symbols S Gamma table tau (termCode q) (termCode r) certificate =
      stepTest n arity symbols S Gamma table q r certificate

/-- The original whole numeric step checker, genuinely joint in Gamma and all data. -/
def ActualNumericStepPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) ×
        List Ty × Nat × Nat × Nat =>
      numericStepTest n arity p.1.1 p.1.2 p.2.2.1 p.2.1
        p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecTargets
