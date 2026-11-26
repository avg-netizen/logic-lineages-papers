import LogicLineages.PersistentMarking.MarkedBaseTuples
namespace LogicLineages.PersistentMarking.MarkedFamilyParameters
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

/- Literal head, output type, port context, positional base tuple, extras. -/
abbrev Parameter := Head × Ty × Context × List Code × List MarkedExtras.Tagged

def raw (E : Environment) (heads : List Head) : List Parameter :=
  heads.flatMap fun f => E.types.flatMap fun τ =>
    (contexts E.types E.ports).flatMap fun Γ =>
      (MarkedBaseTuples.headTuples E Γ f).flatMap fun bs =>
        (MarkedExtras.extras E Γ).map fun es => (f,τ,Γ,bs,es)

def parameterEq (a b : Parameter) : Bool :=
  decide (a.1=b.1) && decide (a.2.1=b.2.1) &&
  decide (a.2.2.1=b.2.2.1) && decide (a.2.2.2.1=b.2.2.2.1) &&
  decide (a.2.2.2.2=b.2.2.2.2)

def parameters (E : Environment) (heads : List Head) : List Parameter :=
  dedupBy parameterEq (raw E heads)

def Valid (E : Environment) (heads : List Head) (p : Parameter) : Prop :=
  p.1 ∈ heads ∧ p.2.1 ∈ E.types ∧ WellFormed E.types E.ports p.2.2.1 ∧
  TupleValues E p.2.2.1 p.1.arguments p.2.2.2.1 ∧
  MarkedExtras.Extra E p.2.2.1 p.2.2.2.2

def bound (E : Environment) (p : Parameter) : Nat :=
  ((descriptor E p.2.1).carriers p.2.2.1).length

def schema (E : Environment) (heads : List Head) : List (Parameter × Nat) :=
  (parameters E heads).map fun p => (p,bound E p)
end LogicLineages.PersistentMarking.MarkedFamilyParameters
