module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution

def ActualFiniteMarkSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (label : Nat) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    finiteMark label q = some r →
    finiteMark label (NumberedRewriteSyntax.substitute q rho) = some (NumberedRewriteSyntax.substitute r rho)

def ActualPrimitiveMarkSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (q r : Packed Symbol arity Gamma), PrimitiveMark Symbol arity Gamma q r →
    PrimitiveMark Symbol arity Delta (substitutePacked rho q) (substitutePacked rho r)

def ActualPrimitiveMultisetSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
    (source target : List (Packed Symbol arity Gamma)), PrimitiveMultiset source target →
    PrimitiveMultiset (source.map (substitutePacked rho)) (target.map (substitutePacked rho))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionTargets
