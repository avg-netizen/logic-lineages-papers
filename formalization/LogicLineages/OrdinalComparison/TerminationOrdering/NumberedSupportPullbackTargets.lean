module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackTargets
open Source NumberedRewriteSyntax NumberedRenamingSupport

def ActualTermSupportPullback : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (rho : Renaming Gamma Delta) (Q : VariablePredicate Delta) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    supports Q (NumberedRewriteSyntax.rename q rho) ↔ supports (fun v => Q (rho v)) q

def ActualArgumentSupportPullback : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (rho : Renaming Gamma Delta) (Q : VariablePredicate Delta) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    supportsArguments Q (renameArguments args rho) ↔ supportsArguments (fun v => Q (rho v)) args

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportPullbackTargets
