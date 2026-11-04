module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction

def ActualApplyArgumentsSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (types : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma (arrows types tau))
    (args : AuxArguments Symbol arity Gamma types),
    substitute (applyArguments q args) theta = applyArguments (substitute q theta) (substituteArguments args theta)

def ActualSelfArgumentsSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (label : Nat) (f : Head Symbol) (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (extraTypes : List Ty) (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty),
    substituteArguments (selfArguments label f base extraTypes extras types) theta =
    selfArguments label f (substituteArguments base theta) extraTypes (substituteArguments extras theta) types

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionTargets
