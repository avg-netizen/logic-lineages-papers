module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedRenamingSupport

def ActualArgumentSupportList : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty)
    (P : VariablePredicate Gamma) (args : AuxArguments Symbol arity Gamma types),
    supportsArguments P args ↔ ∀ q ∈ argumentList args, supports P q.2

def ActualPrimarySupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S Gamma : List Ty) (P : VariablePredicate Gamma) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r → (supports P q.2 ↔ supports P r.2)

def ActualArgumentPrimarySupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol)
    (S Gamma : List Ty) (P : VariablePredicate Gamma) (types : List Ty)
    (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types base target →
      (supportsArguments P base ↔ supportsArguments P target)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySupportTargets
