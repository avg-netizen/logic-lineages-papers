module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedDirectCertificate

def ActualDirectRuleCheck : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (rule : DirectRule)
    (q r : Packed (Fin n) arity Gamma),directTarget arity Gamma rule q=some r ↔ DirectInstance n arity Gamma rule q r

def ActualDirectRuleSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (above : Fin n → Fin n → Prop) (rule : DirectRule)
    (q r : Packed (Fin n) arity Gamma),
  directTarget arity Gamma rule q=some r → InUniverse symbols S q.2 →
    InUniverse symbols S r.2 ∧ ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),
      q=⟨tau,a⟩ ∧ r=⟨tau,b⟩ ∧ WindowStep (Fin n) arity symbols S above Gamma tau a b

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedDirectCertificateTargets
