module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingTargets
open Source NumberedRewriteSyntax NumberedWindowReduction

def ActualStepRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r →
    WindowStep Symbol arity symbols S above Delta tau (NumberedRewriteSyntax.rename q rho) (NumberedRewriteSyntax.rename r rho)

def ActualArgumentStepRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma Delta : List Ty) (rho : Renaming Gamma Delta)
    (types : List Ty) (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types base target →
    WindowArgumentStep Symbol arity symbols S above Delta types (renameArguments base rho) (renameArguments target rho)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingTargets
