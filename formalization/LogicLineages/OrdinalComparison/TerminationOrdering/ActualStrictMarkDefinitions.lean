module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralSpecialApplicationValueProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMark
open Source Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment TypedObservationAccess

def StrictEmpty {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P : World I} {τ : Ty} (a : Value I τ P) : Prop :=
  ∀ (Q : Future P) (o : ObservationAt I τ Q.val),coordinate true a Q o=false

def VariablesStrictEmpty {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ : List Ty} {P : World I} (ρ : Environment I Γ P) : Prop :=∀ {τ} (v : Variable Γ τ),StrictEmpty (ρ v)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualStrictMark
