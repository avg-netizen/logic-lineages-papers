module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimarySubstitution

def ActualPrimarySubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma Delta : List Ty)
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r →
    WindowPrimary Symbol arity symbols S Delta (substitutePacked rho q) (substitutePacked rho r)

def ActualArgumentPrimarySubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma Delta types : List Ty)
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types base target →
    WindowArgumentPrimary Symbol arity symbols S Delta types
      (NumberedRewriteSyntax.substituteArguments base rho) (NumberedRewriteSyntax.substituteArguments target rho)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionTargets
