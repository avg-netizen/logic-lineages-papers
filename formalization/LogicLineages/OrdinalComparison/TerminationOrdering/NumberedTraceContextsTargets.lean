module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedTraceContexts

def ActualTypedPresentation : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity Gamma tau),
    Trace Symbol arity above Gamma n ⟨tau,q⟩ ⟨tau,r⟩ ↔ TypedTrace Symbol arity above Gamma tau n q r

def ActualLambdaContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity (sigma::Gamma) tau),
    TypedTrace Symbol arity above (sigma::Gamma) tau n q r →
    TypedTrace Symbol arity above Gamma (.arrow sigma tau) n (.lam q) (.lam r)

def ActualFunctionContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (sigma tau : Ty) (n : Nat) (q r : AuxTerm Symbol arity Gamma (.arrow sigma tau))
    (a : AuxTerm Symbol arity Gamma sigma),TypedTrace Symbol arity above Gamma (.arrow sigma tau) n q r →
    TypedTrace Symbol arity above Gamma tau n (.app q a) (.app r a)

def ActualTupleCons : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma types : List Ty) (sigma : Ty) (m n : Nat) (q r : AuxTerm Symbol arity Gamma sigma)
    (rest target : AuxArguments Symbol arity Gamma types),TypedTrace Symbol arity above Gamma sigma m q r →
    TupleTrace Symbol arity above Gamma types n rest target →
    TupleTrace Symbol arity above Gamma (sigma::types) (m+n) (.cons q rest) (.cons r target)

def ActualOrdinaryContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (f : Head Symbol) (n : Nat) (base target : AuxArguments Symbol arity Gamma (headArguments arity f)),
    TupleTrace Symbol arity above Gamma (headArguments arity f) n base target →
    TypedTrace Symbol arity above Gamma (headResult f) n (.ordinary f base) (.ordinary f target)

def ActualNumberedBaseContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (k : Nat) (f : Head Symbol) (tau : Ty) (n : Nat)
    (base target : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras : AuxArguments Symbol arity Gamma types),
    TupleTrace Symbol arity above Gamma (headArguments arity f) n base target →
    TypedTrace Symbol arity above Gamma tau n (.numbered k f tau base types extras) (.numbered k f tau target types extras)

def ActualNumberedExtrasContext : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (k : Nat) (f : Head Symbol) (tau : Ty) (n : Nat)
    (base : AuxArguments Symbol arity Gamma (headArguments arity f))
    (types : List Ty) (extras target : AuxArguments Symbol arity Gamma types),
    TupleTrace Symbol arity above Gamma types n extras target →
    TypedTrace Symbol arity above Gamma tau n (.numbered k f tau base types extras) (.numbered k f tau base types target)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTraceContextsTargets
