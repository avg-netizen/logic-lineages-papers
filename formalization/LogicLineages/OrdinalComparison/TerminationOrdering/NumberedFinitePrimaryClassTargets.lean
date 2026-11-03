module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedFinitePrimaryClass

def ActualReachableBound : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma : List Ty) (q : Packed Symbol arity Gamma) (n : Nat),
  reachable symbols S q n ⊆ vertices symbols S q

def ActualCardinalitySaturation : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma : List Ty) (q : Packed Symbol arity Gamma),
  reachStep symbols S q (primaryClass symbols S q)=primaryClass symbols S q

def ActualExactPrimaryClass : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q : Packed Symbol arity Gamma),
  InUniverse symbols S q.2 → ∀ r,r∈primaryClass symbols S q ↔ WindowPrimary Symbol arity symbols S Gamma q r

def ActualPrimaryDecision : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q : Packed Symbol arity Gamma),
  InUniverse symbols S q.2 → ∀ r,primaryTest symbols S q r=true ↔ WindowPrimary Symbol arity symbols S Gamma q r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFinitePrimaryClassTargets
