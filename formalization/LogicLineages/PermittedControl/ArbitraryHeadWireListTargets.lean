module
public import LogicLineages.PermittedControl.ArbitraryHeadSharedWireTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadWireList
open OrdinalComparison ArbitraryHeadSharedWire
open NaturalAffineGateGraph (Expression)

structure Gate where
  head : NONote
  source : Nat
  output : Nat
  hidden : Nat

inductive NormalGate where
  | affine (expression : Expression) (output : Nat)
  | limitPair (head : Nat) (expression : Expression) (hidden output : Nat)

def Gate.finite (g : Gate) : Bool := encodedFiniteTest (headCode g.head)

def Gate.shift (g : Gate) (ν : Valuation) : Nat :=
  (ArbitraryFixedHeadCollapse.transported (headCode g.head,ν g.source)).2

def Gate.hiddenName (g : Gate) : Option Nat :=
  match g.finite with
  | true => none
  | false => some g.hidden

def hiddenNames (gates : List Gate) : List Nat := gates.filterMap Gate.hiddenName

/-- Infinite hidden aliases are distinct and avoid the original wires of
every gate, including the original wires of finite-head gates. The dummy
hidden field of a finite gate is never allocated. -/
def Fresh (gates : List Gate) : Prop :=
  (hiddenNames gates).Nodup ∧
    ∀ g ∈ gates, g.source ∉ hiddenNames gates ∧ g.output ∉ hiddenNames gates

def normalizeGate (g : Gate) : NormalGate :=
  match g.finite with
  | true => .affine (finiteExpression g.head g.source) g.output
  | false => .limitPair (limitCode g.head) (shiftedExpression g.head g.source) g.hidden g.output

def normalize (gates : List Gate) : List NormalGate := gates.map normalizeGate

def NormalGate.Holds (f : Nat → Nat) (θ : Valuation) : NormalGate → Prop
  | .affine e o => (NaturalAffineGateGraph.graph o e).eval θ
  | .limitPair h e i o => AffineCollapseGraphComposition.graph f h e i o θ

def OriginalAt (f : Nat → Nat) (ν : Valuation) (gates : List Gate) : Prop :=
  ∀ g ∈ gates, originalGraph f g.head g.source g.output ν

def NormalizedAt (f : Nat → Nat) (θ : Valuation) (gates : List Gate) : Prop :=
  ∀ n ∈ normalize gates, n.Holds f θ

def Agrees (gates : List Gate) (ν θ : Valuation) : Prop :=
  ∀ n : Nat, n ∉ hiddenNames gates → θ n = ν n

def Prescribed (gates : List Gate) (ν θ : Valuation) : Prop :=
  ∀ g ∈ gates, g.finite = false → θ g.hidden = g.shift ν

/-- Only hidden coordinates are installed; the original values at all
source/output names are never recomputed or overwritten. -/
def extend (ν : Valuation) : List Gate → Valuation
  | [] => ν
  | g :: gs =>
    match g.finite with
    | true => extend ν gs
    | false => Function.update (extend ν gs) g.hidden (g.shift ν)

def ExactWireListAssignments : Prop :=
  ∀ (gates : List Gate) (ν θ : Valuation), (hiddenNames gates).Nodup →
    (Agrees gates ν θ ∧ Prescribed gates ν θ ↔ θ = extend ν gates)

def ExactSharedWireList : Prop :=
  ∀ (f : Nat → Nat) (gates : List Gate), Fresh gates → ∀ ν θ : Valuation,
    (NormalizedAt f θ gates ∧ Agrees gates ν θ ↔
      OriginalAt f ν gates ∧ θ = extend ν gates)

def UniqueSharedWireList : Prop :=
  ∀ (f : Nat → Nat) (gates : List Gate), Fresh gates → ∀ ν : Valuation,
    ((∃! θ : Valuation, NormalizedAt f θ gates ∧ Agrees gates ν θ) ↔ OriginalAt f ν gates) ∧
      ∀ g ∈ gates, extend ν gates g.source = ν g.source ∧ extend ν gates g.output = ν g.output

def FullArbitraryHeadWireList : Prop :=
  ExactWireListAssignments ∧ ExactSharedWireList ∧ UniqueSharedWireList

end LogicLineages.PermittedControl.ArbitraryHeadWireList
