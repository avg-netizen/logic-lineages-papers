module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseOperationsTargets NumberedWindowTraces

def ActualTypedPresentation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity Gamma tau),
    WindowTrace Symbol arity symbols S above Gamma n ⟨tau,q⟩ ⟨tau,r⟩ ↔ WindowTypedTrace Symbol arity symbols S above Gamma tau n q r

def ActualLambdaContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity (sigma::Gamma) tau),
    WindowTypedTrace Symbol arity symbols S above (sigma::Gamma) tau n q r →
    WindowTypedTrace Symbol arity symbols S above Gamma (.arrow sigma tau) n (.lam q) (.lam r)

def ActualFunctionContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau))
    (a : AuxTerm Symbol arity Gamma sigma),WindowTypedTrace Symbol arity symbols S above Gamma (.arrow sigma tau) n q r →
    WindowTypedTrace Symbol arity symbols S above Gamma tau n (.app q a) (.app r a)

def ActualTupleCons : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma types : List Ty) (sigma : Ty) (m n : Nat) (q r : AuxTerm Symbol arity Gamma sigma)
    (rest target : AuxArguments Symbol arity Gamma types),WindowTypedTrace Symbol arity symbols S above Gamma sigma m q r →
    WindowTupleTrace Symbol arity symbols S above Gamma types n rest target →
    WindowTupleTrace Symbol arity symbols S above Gamma (sigma::types) (m+n) (.cons q rest) (.cons r target)

def ActualOrdinaryContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (f : Head Symbol) (n : Nat) (base target : AuxArguments Symbol arity Gamma (headArguments arity f)),
    WindowTupleTrace Symbol arity symbols S above Gamma (headArguments arity f) n base target →
    WindowTypedTrace Symbol arity symbols S above Gamma (headResult f) n (.ordinary f base) (.ordinary f target)

def ActualNumberedBaseContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (k : Nat) (f : Head Symbol) (tau : Ty) (n : Nat)
    (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma (headArguments arity f) n base target →
    WindowTypedTrace Symbol arity symbols S above Gamma tau n (.numbered k f tau base types extras) (.numbered k f tau target types extras)

def ActualNumberedExtrasContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (k : Nat) (f : Head Symbol) (tau : Ty) (n : Nat)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras target : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma types n extras target →
    WindowTypedTrace Symbol arity symbols S above Gamma tau n (.numbered k f tau base types extras) (.numbered k f tau base types target)

def ActualPackedErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (n : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma n q r → NumberedPrimaryEquivalence.Trace Symbol arity above Gamma n q r

def ActualTupleErasure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (n : Nat) (a b : AuxArguments Symbol arity Gamma types),
    WindowTupleTrace Symbol arity symbols S above Gamma types n a b → NumberedTraceContexts.TupleTrace Symbol arity above Gamma types n a b

def ActualAllBoundaries : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
    SubtypeClosed (fun t => t∈S) → ∀ (above : Symbol → Symbol → Prop) (Gamma : List Ty) (n : Nat)
    (q r : Packed Symbol arity Gamma) (h : WindowTrace Symbol arity symbols S above Gamma n q r),
    PackedGood (fun t => t∈S) (HeadInWindow arity symbols S) q → allBoundaries h

def ActualAllTupleBoundaries : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
    SubtypeClosed (fun t => t∈S) → ∀ (above : Symbol → Symbol → Prop) (Gamma types : List Ty) (n : Nat)
    (a b : AuxArguments Symbol arity Gamma types) (h : WindowTupleTrace Symbol arity symbols S above Gamma types n a b),
    GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a → allTupleBoundaries h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowTracesTargets
