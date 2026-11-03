module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedSelectCertificate

def ActualSelectCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  (∃ (types : List Ty) (index : Nat),selectTarget arity Gamma types index q=some r) ↔ SelectInstance n arity Gamma q r

def ActualSelectCertificateSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (above : Fin n → Fin n → Prop)
    (types : List Ty) (index : Nat) (q r : Packed (Fin n) arity Gamma),
  selectTarget arity Gamma types index q=some r → InUniverse symbols S q.2 →
    InUniverse symbols S r.2 ∧ ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),
      q=⟨tau,a⟩ ∧ r=⟨tau,b⟩ ∧ WindowStep (Fin n) arity symbols S above Gamma tau a b

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSelectCertificateTargets
