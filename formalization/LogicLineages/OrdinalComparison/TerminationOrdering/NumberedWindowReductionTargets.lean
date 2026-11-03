module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedWindowReduction

def ActualStepErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r → RawStep Symbol arity above Gamma tau q r

def ActualArgumentErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (a b : AuxArguments Symbol arity Gamma types),
    WindowArgumentStep Symbol arity symbols S above Gamma types a b → ArgumentStep Symbol arity above Gamma types a b

def ActualStepConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
    SubtypeClosed (fun t => t∈S) → ∀ (above : Symbol → Symbol → Prop) (Gamma : List Ty) (tau : Ty)
    (q r : AuxTerm Symbol arity Gamma tau),WindowStep Symbol arity symbols S above Gamma tau q r →
    InUniverse symbols S q → InUniverse symbols S r

def ActualArgumentConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
    SubtypeClosed (fun t => t∈S) → ∀ (above : Symbol → Symbol → Prop) (Gamma types : List Ty)
    (a b : AuxArguments Symbol arity Gamma types),WindowArgumentStep Symbol arity symbols S above Gamma types a b →
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a →
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) b

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowReductionTargets
