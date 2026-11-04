module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryShapes

def ActualPrimaryLambdaShape : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r → isLambda q.2 = isLambda r.2

def ActualPrimaryApplicationComponents : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (sigma tau : Ty)
    (f : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (a : AuxTerm Symbol arity Gamma sigma)
    (q : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma ⟨tau,.app f a⟩ q ↔
    ∃ (g : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (b : AuxTerm Symbol arity Gamma sigma),
      q = ⟨tau,.app g b⟩ ∧
      WindowPrimary Symbol arity symbols S Gamma ⟨.arrow sigma tau,f⟩ ⟨.arrow sigma tau,g⟩ ∧
      WindowPrimary Symbol arity symbols S Gamma ⟨sigma,a⟩ ⟨sigma,b⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesTargets
