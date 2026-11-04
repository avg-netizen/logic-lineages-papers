module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionTargets
open Source NumberedRewriteSyntax

def ActualTermRenamingComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (rho : Renaming Gamma Delta) (eta : Renaming Delta Theta)
    (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    NumberedRewriteSyntax.rename (NumberedRewriteSyntax.rename q rho) eta =
    NumberedRewriteSyntax.rename q (fun v => eta (rho v))

def ActualArgumentRenamingComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (rho : Renaming Gamma Delta) (eta : Renaming Delta Theta)
    (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    NumberedRewriteSyntax.renameArguments (NumberedRewriteSyntax.renameArguments args rho) eta =
    NumberedRewriteSyntax.renameArguments args (fun v => eta (rho v))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRenamingCompositionTargets
