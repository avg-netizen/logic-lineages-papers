module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingTargets
open Source NumberedRewriteSyntax

def ActualTermSubstituteRename : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (rho : Renaming Gamma Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    substitute (NumberedRewriteSyntax.rename q rho) theta = substitute q (fun v => theta (rho v))

def ActualArgumentSubstituteRename : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (rho : Renaming Gamma Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    substituteArguments (renameArguments args rho) theta = substituteArguments args (fun v => theta (rho v))

def ActualTermRenameSubstitute : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (rho : Renaming Delta Theta)
    (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    NumberedRewriteSyntax.rename (substitute q theta) rho = substitute q (fun v => NumberedRewriteSyntax.rename (theta v) rho)

def ActualArgumentRenameSubstitute : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (rho : Renaming Delta Theta)
    (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    renameArguments (substituteArguments args theta) rho = substituteArguments args (fun v => NumberedRewriteSyntax.rename (theta v) rho)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMixedBindingTargets
