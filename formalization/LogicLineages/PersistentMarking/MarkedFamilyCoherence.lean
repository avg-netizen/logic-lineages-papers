import LogicLineages.PersistentMarking.MarkedFamilyCoding
namespace LogicLineages.PersistentMarking.MarkedFamilyCoherence
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedFamilyParameters MarkedFamilyCoding

def InputLE (E : Environment) (p q : Parameter) : Prop :=
  p.1=q.1 ∧ p.2.1=q.2.1 ∧ p.2.2.1=q.2.2.1 ∧
  HereditaryDomainSemantics.ValuesLE E p.2.2.1 p.1.arguments p.2.2.2.1 q.2.2.2.1 ∧
  ∀ a, a ∈ p.2.2.2.2 → a ∈ q.2.2.2.2

def inputLe (E : Environment) (p q : Parameter) : Bool :=
  decide (p.1=q.1) && decide (p.2.1=q.2.1) && decide (p.2.2.1=q.2.2.1) &&
  MarkedBaseTuples.tupleLe E p.2.2.1 p.1.arguments p.2.2.2.1 q.2.2.2.1 &&
  p.2.2.2.2.all (fun a => decide (a ∈ q.2.2.2.2))

def weakenParameter (E : Environment) (p : Parameter) (Δ : Context) : Parameter :=
  (p.1,p.2.1,Δ,
    MarkedBaseTuples.restrictTuple E p.2.2.1 Δ p.1.arguments p.2.2.2.1,
    MarkedExtras.weaken E p.2.2.1 Δ p.2.2.2.2)

def monotoneBool (E : Environment) (heads : List Head) (c : Code) : Bool :=
  (parameters E heads).all fun p => (parameters E heads).all fun q =>
    if inputLe E p q then
      match MarkedFamilyCoding.output E heads c p,MarkedFamilyCoding.output E heads c q with
      | some a,some b => (descriptor E p.2.1).le p.2.2.1 a b
      | _,_ => false
    else true

def coherentBool (E : Environment) (heads : List Head) (c : Code) : Bool :=
  (parameters E heads).all fun p =>
    (FiniteDomainSchema.extensions E.types E.ports p.2.2.1).all fun Δ =>
      match MarkedFamilyCoding.output E heads c p,
        MarkedFamilyCoding.output E heads c (weakenParameter E p Δ) with
      | some a,some b => decide ((descriptor E p.2.1).restrict p.2.2.1 Δ a = b)
      | _,_ => false

def Monotone (E : Environment) (heads : List Head) (v : Family) : Prop :=
  ∀ p q, MarkedFamilyParameters.Valid E heads p → MarkedFamilyParameters.Valid E heads q →
    InputLE E p q → (descriptor E p.2.1).le p.2.2.1 (v p) (v q) = true

def Coherent (E : Environment) (heads : List Head) (v : Family) : Prop :=
  ∀ p, MarkedFamilyParameters.Valid E heads p → ∀ Δ,
    WellFormed E.types E.ports Δ → Extends p.2.2.1 Δ →
    (descriptor E p.2.1).restrict p.2.2.1 Δ (v p) = v (weakenParameter E p Δ)

def ValidFamily (E : Environment) (heads : List Head) (v : Family) : Prop :=
  OutputsValid E heads v ∧ Monotone E heads v ∧ Coherent E heads v

def retained (E : Environment) (heads : List Head) : List Code :=
  (MarkedFamilyCoding.rawCodes E heads).filter fun c => monotoneBool E heads c && coherentBool E heads c
end LogicLineages.PersistentMarking.MarkedFamilyCoherence
