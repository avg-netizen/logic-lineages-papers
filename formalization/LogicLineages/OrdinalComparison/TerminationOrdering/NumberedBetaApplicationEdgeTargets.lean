module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedQuotientApplication

def ActualBetaApplicationEdge : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (sigma tau : Ty) (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (a : AuxTerm (Fin n) arity Gamma sigma) (target : Nat),
    InUniverse symbols S (.lam body) → InUniverse symbols S a →
    QuotientEdge n arity symbols S above Gamma (representativeCode symbols S (applicationPacked (.lam body) a)) target →
    target = representativeCode symbols S (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma) ∨
    (∃ (body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (a' : AuxTerm (Fin n) arity Gamma sigma),
      InUniverse symbols S body' ∧ InUniverse symbols S a' ∧
      WindowPrimary (Fin n) arity symbols S (sigma :: Gamma) ⟨tau,body⟩ ⟨tau,body'⟩ ∧
      WindowPrimary (Fin n) arity symbols S Gamma ⟨sigma,a⟩ ⟨sigma,a'⟩ ∧
      target = representativeCode symbols S ⟨tau,substitute body' (singleSubstitution a')⟩) ∨
    target = representativeCode symbols S (applicationPacked (.bottom (.arrow sigma tau)) a) ∨
    ∃ next : AuxTerm (Fin n) arity (sigma :: Gamma) tau, InUniverse symbols S next ∧
      QuotientEdge n arity symbols S above (sigma :: Gamma)
        (representativeCode symbols S ⟨tau,body⟩) (representativeCode symbols S ⟨tau,next⟩) ∧
      target = representativeCode symbols S (applicationPacked (.lam next) a)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBetaApplicationEdgeTargets
