module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkTargets
open Source Source.SourceMarkedSyntax Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation RecursiveComparison TypedObservationAccess SourceConstructorIteration ActualStrictMark

def MarkConfinement : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (Γ : List Ty) (τ : Ty) (q : ConfinedTerm I Γ τ) (r : MarkedTerm Symbol arity Γ τ),
    strictMark q.val=some r → Confined I r

def MarkBitEquality : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ : List Ty) (τ : Ty)
    (q : ConfinedTerm I Γ τ) (r : MarkedTerm Symbol arity Γ τ) (hr : Confined I r),strictMark q.val=some r →
    ∀ (P : World I) (ρ : Environment I Γ P) (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)),
    readBit true (interpret q (limit I above) P ρ) o=readBit false (interpret ⟨r,hr⟩ (limit I above) P ρ) o

def UndefinedMarkFalse : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity) (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (Γ : List Ty) (τ : Ty)
    (q : ConfinedTerm I Γ τ),strictMark q.val=none →
    ∀ (P : World I) (ρ : Environment I Γ P) (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)),
    VariablesStrictEmpty ρ → readBit true (interpret q (limit I above) P ρ) o=false

def IdentityUndefinedMarkFalse : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (I : Input Symbol arity)
    (above : Symbol → Symbol → Prop) (_ : DecidableRel above) (P : World I) (τ : Ty)
    (q : ConfinedTerm I (portTypes P.val++I.context) τ),strictMark q.val=none →
    ∀ (o : Source.SourceOpenedObservations.Observation Symbol arity I.context (budget I)),
    readBit true (interpret q (limit I above) P (identity I P)) o=false

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMarkTargets
