module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedRewriteApplication

def ActualPrimaryTypePreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (q r : Packed Symbol arity Gamma),Primary Symbol arity Gamma q r → q.1=r.1

def ActualPrimarySizePreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (q r : Packed Symbol arity Gamma),Primary Symbol arity Gamma q r → size q.2=size r.2

def ActualTraceZero : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (q r : Packed Symbol arity Gamma),Trace Symbol arity above Gamma 0 q r ↔ Primary Symbol arity Gamma q r

def ActualTraceTypePreservation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (n : Nat) (q r : Packed Symbol arity Gamma),Trace Symbol arity above Gamma n q r → q.1=r.1

def ActualRawPathTrace : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),RawSteps Symbol arity above Gamma tau q r →
      ∃ n,Trace Symbol arity above Gamma n ⟨tau,q⟩ ⟨tau,r⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryEquivalenceTargets
