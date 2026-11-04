module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootTargets
open Source NumberedRewriteSyntax NumberedWindowReduction

def ActualLambdaStepCases : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma::Gamma) tau)
    (q : AuxTerm Symbol arity Gamma (.arrow sigma tau)),
    WindowStep Symbol arity symbols S above Gamma (.arrow sigma tau) (.lam body) q ↔
    q = .bottom (.arrow sigma tau) ∨
    ∃ body' : AuxTerm Symbol arity (sigma::Gamma) tau,
      WindowStep Symbol arity symbols S above (sigma::Gamma) tau body body' ∧ q = .lam body'

def ActualBetaApplicationStepCases : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma::Gamma) tau)
    (a : AuxTerm Symbol arity Gamma sigma) (q : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau (.app (.lam body) a) q ↔
    q = .bottom tau ∨
    q = NumberedRewriteSyntax.substitute body (singleSubstitution a) ∨
    q = .app (.bottom (.arrow sigma tau)) a ∨
    ∃ body' : AuxTerm Symbol arity (sigma::Gamma) tau,
      WindowStep Symbol arity symbols S above (sigma::Gamma) tau body body' ∧ q = .app (.lam body') a

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootTargets
