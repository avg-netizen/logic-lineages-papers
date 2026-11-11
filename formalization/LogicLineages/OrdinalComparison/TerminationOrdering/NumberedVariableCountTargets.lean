module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedVariableCount

def ActualPrimaryVariableCount : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r → packedVariableCount q = packedVariableCount r

def ActualArgumentPrimaryVariableCount : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma types : List Ty) (base target : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types base target →
    argumentVariableCount base = argumentVariableCount target

def ActualRepresentativeVariableCount : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    representativeCode symbols S q = representativeCode symbols S r →
    packedVariableCount q = packedVariableCount r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountTargets
