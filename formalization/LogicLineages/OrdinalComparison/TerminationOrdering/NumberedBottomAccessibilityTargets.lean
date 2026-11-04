module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowReduction NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedQuotientPaths
open OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility

def ActualBottomPrimaryRigid : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (tau : Ty) (q : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma ⟨tau,AuxTerm.bottom tau⟩ q →
    q = ⟨tau,AuxTerm.bottom tau⟩

def ActualBottomStepTerminal : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q : AuxTerm Symbol arity Gamma tau),
    ¬ WindowStep Symbol arity symbols S above Gamma tau (.bottom tau) q

def ActualBottomPositiveTerminal : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty), tau ∈ S → ∀ y : Nat,
    ¬ PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma)) y

def ActualBottomAccessibleLeast : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (context : Nat) (ctx : Context n) (scalar : Positive (Fin 2)),
    Encodable.decode context = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
    Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) →
    ∀ tau : Ty, tau ∈ ctx.1.2 →
    let value := representativeCode ctx.1.1 ctx.1.2 (⟨tau,AuxTerm.bottom tau⟩ : Packed (Fin n) arity Gamma)
    Acc (fun successor source => encodedR n arity Gamma context source successor) value ∧
      value ∈ leastSet scalar context

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityTargets
