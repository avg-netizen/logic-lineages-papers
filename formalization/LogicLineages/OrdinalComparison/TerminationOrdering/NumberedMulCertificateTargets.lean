module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedMultisetCertificate NumberedMulCertificate

def ActualTypedMulCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (q r : Packed (Fin n) arity Gamma),
  (∃ certificate,mulCertificateTest n arity symbols S Gamma q r certificate=true) ↔ MulInstance n arity symbols S Gamma q r

def ActualTypedMulSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (above : Fin n → Fin n → Prop) (q r : Packed (Fin n) arity Gamma) (certificate : MultisetCertificate n arity Gamma),
  mulCertificateTest n arity symbols S Gamma q r certificate=true → InUniverse symbols S q.2 →
    InUniverse symbols S r.2 ∧ ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),
      q=⟨tau,a⟩ ∧ r=⟨tau,b⟩ ∧ WindowStep (Fin n) arity symbols S above Gamma tau a b

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMulCertificateTargets
