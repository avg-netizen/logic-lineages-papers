module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientApplication

def ActualApplicationConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (a : AuxTerm Symbol arity Gamma sigma),
      InUniverse symbols S f → InUniverse symbols S a → InUniverse symbols S (applicationPacked f a).2

def ActualRepresentativeApplicationCongruence : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (Gamma : List Ty) (sigma tau : Ty)
      (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a b : AuxTerm (Fin n) arity Gamma sigma),
      InUniverse symbols S f → InUniverse symbols S g → InUniverse symbols S a → InUniverse symbols S b →
      representativeCode symbols S ⟨.arrow sigma tau,f⟩ = representativeCode symbols S ⟨.arrow sigma tau,g⟩ →
      representativeCode symbols S ⟨sigma,a⟩ = representativeCode symbols S ⟨sigma,b⟩ →
      representativeCode symbols S (applicationPacked f a) = representativeCode symbols S (applicationPacked g b)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationTargets
