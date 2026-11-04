module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportTargets
open Source NumberedRewriteSyntax NumberedWindowReduction NumberedRenamingSupport

def ActualStepSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (P : VariablePredicate Gamma)
    (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r → supports P q → supports P r

def ActualArgumentStepSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (P : VariablePredicate Gamma)
    (types : List Ty) (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types base target → supportsArguments P base → supportsArguments P target

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportTargets
