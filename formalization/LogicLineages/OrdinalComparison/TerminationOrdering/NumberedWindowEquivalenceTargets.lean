module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseOperationsTargets NumberedWindowEquivalence

def ActualPrimaryErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma : List Ty) (q r : NumberedRewriteReduction.Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r → Primary Symbol arity Gamma q r

def ActualArgumentErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma types : List Ty) (a b : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types a b → ArgumentPrimary Symbol arity Gamma types a b

def ActualPrimaryConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma : List Ty) (q r : NumberedRewriteReduction.Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r →
    (PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) q ↔
     PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) r)

def ActualArgumentConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (Gamma types : List Ty) (a b : AuxArguments Symbol arity Gamma types),
    WindowArgumentPrimary Symbol arity symbols S Gamma types a b →
    (GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a ↔
     GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) b)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceTargets
