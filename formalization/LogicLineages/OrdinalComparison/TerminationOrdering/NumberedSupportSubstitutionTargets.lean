module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRenamingSupport

def ActualTermSupportSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (P : VariablePredicate Gamma) (Q : VariablePredicate Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    supports P q → (∀ {upsilon : Ty} (v : Variable Gamma upsilon), P v → supports Q (theta v)) →
    supports Q (substitute q theta)

def ActualArgumentSupportSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma Delta : List Ty)
    (P : VariablePredicate Gamma) (Q : VariablePredicate Delta)
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    supportsArguments P args → (∀ {upsilon : Ty} (v : Variable Gamma upsilon), P v → supports Q (theta v)) →
    supportsArguments Q (substituteArguments args theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSupportSubstitutionTargets
