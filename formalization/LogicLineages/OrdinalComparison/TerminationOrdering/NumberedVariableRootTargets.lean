module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedWindowEquivalence

def ActualVariablePrimaryRigid : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (tau : Ty) (v : Variable Gamma tau)
    (q : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma ⟨tau,AuxTerm.var v⟩ q →
    q = ⟨tau,AuxTerm.var v⟩

def ActualVariableStepBottom : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (v : Variable Gamma tau) (q : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau (.var v) q ↔ q = .bottom tau

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableRootTargets
