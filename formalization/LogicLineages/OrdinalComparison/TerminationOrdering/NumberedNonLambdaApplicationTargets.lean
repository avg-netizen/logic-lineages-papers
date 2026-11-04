module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedPrimaryShapes
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

def ActualNonLambdaApplicationStep : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (f : AuxTerm Symbol arity Gamma (.arrow sigma tau))
    (a : AuxTerm Symbol arity Gamma sigma) (q : AuxTerm Symbol arity Gamma tau),
    isLambda f = false →
    (WindowStep Symbol arity symbols S above Gamma tau (.app f a) q ↔
      q = .bottom tau ∨ ∃ g : AuxTerm Symbol arity Gamma (.arrow sigma tau),
        WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) f g ∧ q = .app g a)

def ActualNonLambdaApplicationEdge : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (sigma tau : Ty) (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (target : Nat),
    InUniverse symbols S f → InUniverse symbols S a → isLambda f = false →
    QuotientEdge n arity symbols S above Gamma (representativeCode symbols S (applicationPacked f a)) target →
    target = representativeCode symbols S (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma) ∨
    ∃ g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau), InUniverse symbols S g ∧
      QuotientEdge n arity symbols S above Gamma
        (representativeCode symbols S ⟨.arrow sigma tau,f⟩) (representativeCode symbols S ⟨.arrow sigma tau,g⟩) ∧
      target = representativeCode symbols S (applicationPacked g a)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNonLambdaApplicationTargets
