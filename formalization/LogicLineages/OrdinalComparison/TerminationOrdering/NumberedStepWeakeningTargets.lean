module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningTargets
open Source NumberedRewriteSyntax NumberedWindowReduction

def ActualStepWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty) (sigma tau : Ty)
    (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r ↔
    WindowStep Symbol arity symbols S above (sigma :: Gamma) tau
      (NumberedRewriteSyntax.rename q (Renaming.weaken Gamma sigma)) (NumberedRewriteSyntax.rename r (Renaming.weaken Gamma sigma))

def ActualArgumentStepWeakening : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S : List Ty) (above : Symbol → Symbol → Prop) (Gamma : List Ty) (sigma : Ty) (types : List Ty)
    (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types base target ↔
    WindowArgumentStep Symbol arity symbols S above (sigma :: Gamma) types
      (renameArguments base (Renaming.weaken Gamma sigma)) (renameArguments target (Renaming.weaken Gamma sigma))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakeningTargets
