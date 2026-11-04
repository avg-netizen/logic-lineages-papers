module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRenamingSupport

def ActualFiniteMarkSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (label : Nat) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    finiteMark label q = some r → (supports P q ↔ supports P r)

def ActualPrimitiveMarkSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (q r : Packed Symbol arity Gamma),
    PrimitiveMark Symbol arity Gamma q r → (supports P q.2 ↔ supports P r.2)

def ActualPrimitiveMultisetSupport : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty)
    (P : VariablePredicate Gamma) (source target : List (Packed Symbol arity Gamma)),
    PrimitiveMultiset source target → (∀ q ∈ source, supports P q.2) → ∀ r ∈ target, supports P r.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportTargets
