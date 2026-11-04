module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence

def ActualPrimaryLambdaBody : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S Gamma : List Ty) (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma :: Gamma) tau)
    (q : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma ⟨.arrow sigma tau,.lam body⟩ q ↔
    ∃ body' : AuxTerm Symbol arity (sigma :: Gamma) tau,
      q = ⟨.arrow sigma tau,.lam body'⟩ ∧
      WindowPrimary Symbol arity symbols S (sigma :: Gamma) ⟨tau,body⟩ ⟨tau,body'⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyTargets
