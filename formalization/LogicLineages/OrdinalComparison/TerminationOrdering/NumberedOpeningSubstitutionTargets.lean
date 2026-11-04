module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction

def ActualTermWeakeningSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (sigma tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    substitute (NumberedRewriteSyntax.rename q (Renaming.weaken Gamma sigma)) (liftSubstitution theta) =
    NumberedRewriteSyntax.rename (substitute q theta) (Renaming.weaken Delta sigma)

def ActualArgumentWeakeningSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (sigma : Ty) (types : List Ty) (args : AuxArguments Symbol arity Gamma types),
    substituteArguments (renameArguments args (Renaming.weaken Gamma sigma)) (liftSubstitution theta) =
    renameArguments (substituteArguments args theta) (Renaming.weaken Delta sigma)

def ActualOpenNumberedSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (label : Nat) (f : Head Symbol) (sigma tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes),
    substitute (openNumbered label f sigma tau base extraTypes extras) (liftSubstitution theta) =
    openNumbered label f sigma tau (substituteArguments base theta) extraTypes (substituteArguments extras theta)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOpeningSubstitutionTargets
