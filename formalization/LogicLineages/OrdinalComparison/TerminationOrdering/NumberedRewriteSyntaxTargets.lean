module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax

def ActualCanonicalNumbering : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau),
    Represents Symbol arity n Gamma tau q (canonical n q)

def ActualBudgetLowering : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n m : Nat),m≤n →
    ∀ (Gamma : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau),
    Represents Symbol arity n Gamma tau q Q → Represents Symbol arity m Gamma tau q Q

def ActualOrdinaryTranslation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma : List Ty) (tau : Ty) (q : Term Symbol arity Gamma tau),
    Represents Symbol arity n Gamma tau (embed q) (translateOriginal q)

def ActualRenaming : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma Delta : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau)
    (rho : Renaming Gamma Delta),Represents Symbol arity n Gamma tau q Q →
    Represents Symbol arity n Delta tau (Source.SourceMarkedBinding.renameTerm q rho) (NumberedRewriteSyntax.rename Q rho)

def ActualRelatedSubstitution : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (n : Nat)
    (Gamma Delta : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau)
    (rho : Source.SourceMarkedBinding.MarkedSubstitution Symbol arity Gamma Delta)
    (sigma : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    (∀ (upsilon : Ty) (v : Variable Gamma upsilon),Represents Symbol arity n Delta upsilon (rho v) (sigma v)) →
    Represents Symbol arity n Gamma tau q Q →
    Represents Symbol arity n Delta tau (Source.SourceMarkedBinding.substituteTerm q rho) (NumberedRewriteSyntax.substitute Q sigma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteSyntaxTargets
