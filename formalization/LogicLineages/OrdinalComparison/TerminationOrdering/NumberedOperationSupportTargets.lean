module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportTargets
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction NumberedRenamingSupport

def ActualApplyArgumentsSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (types : List Ty) (tau : Ty)
    (q : AuxTerm Symbol arity Gamma (arrows types tau)) (args : AuxArguments Symbol arity Gamma types),
    supports P (applyArguments q args) ↔ supports P q ∧ supportsArguments P args

def ActualSelfArgumentsSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (label : Nat) (f : Head Symbol)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
    (extras : AuxArguments Symbol arity Gamma extraTypes) (types : List Ty),
    supportsArguments P base → supportsArguments P extras → supportsArguments P (selfArguments label f base extraTypes extras types)

def ActualOpenNumberedSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (label : Nat) (f : Head Symbol) (sigma tau : Ty)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
    (extras : AuxArguments Symbol arity Gamma extraTypes),
    supports (liftPredicate P) (openNumbered label f sigma tau base extraTypes extras) ↔
      supportsArguments P base ∧ supportsArguments P extras

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOperationSupportTargets
