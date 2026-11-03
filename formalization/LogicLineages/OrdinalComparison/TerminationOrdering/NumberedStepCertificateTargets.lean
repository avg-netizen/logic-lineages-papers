module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCopyCertificate NumberedStepContexts NumberedTypedFocus NumberedNumericRoot NumberedStepCertificate

def ActualStepCertificateSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau) (certificate : StepCertificate),
  stepTest n arity symbols S Gamma table q r certificate=true → WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r

def ActualStepCertificateComplete : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (tau : Ty) (q r : AuxTerm (Fin n) arity Gamma tau),
  WindowStep (Fin n) arity symbols S (tableAbove table) Gamma tau q r → ∃ certificate,stepTest n arity symbols S Gamma table q r certificate=true

def ActualStepCertificateConfinement : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma tau) (certificate : StepCertificate),
  stepTest n arity symbols S Gamma table q r certificate=true → InUniverse symbols S q → InUniverse symbols S r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateTargets
