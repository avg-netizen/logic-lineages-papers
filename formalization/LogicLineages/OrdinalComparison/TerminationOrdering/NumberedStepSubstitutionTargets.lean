module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionTargets
open Source NumberedRewriteSyntax NumberedWindowReduction

def ActualStepSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r →
    substitute q theta = substitute r theta ∨
    WindowStep Symbol arity symbols S above Delta tau (substitute q theta) (substitute r theta)

def ActualArgumentStepSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (types : List Ty) (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types base target →
    substituteArguments base theta = substituteArguments target theta ∨
    WindowArgumentStep Symbol arity symbols S above Delta types
      (substituteArguments base theta) (substituteArguments target theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionTargets
