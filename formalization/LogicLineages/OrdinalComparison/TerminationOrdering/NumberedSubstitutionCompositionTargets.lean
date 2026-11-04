module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionTargets
open Source NumberedRewriteSyntax

def ActualTermSubstitutionComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (eta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    substitute (substitute q theta) eta = substitute q (fun v => substitute (theta v) eta)

def ActualArgumentSubstitutionComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta Theta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (eta : NumberedRewriteSyntax.Substitution Symbol arity Delta Theta) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    substituteArguments (substituteArguments args theta) eta = substituteArguments args (fun v => substitute (theta v) eta)

def ActualBetaSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (sigma tau : Ty) (body : AuxTerm Symbol arity (sigma::Gamma) tau) (a : AuxTerm Symbol arity Gamma sigma),
    substitute (substitute body (singleSubstitution a)) theta =
    substitute (substitute body (liftSubstitution theta)) (singleSubstitution (substitute a theta))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionTargets
