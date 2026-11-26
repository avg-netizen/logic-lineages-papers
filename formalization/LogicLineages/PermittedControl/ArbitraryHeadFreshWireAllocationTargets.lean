module
public import LogicLineages.PermittedControl.ArbitraryHeadWireListTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
open OrdinalComparison ArbitraryHeadWireList
open ArbitraryHeadSharedWire (Valuation originalGraph)

structure Wire where
  head : NONote
  source : Nat
  output : Nat

def install (wire : Wire) (name : Nat) : Gate :=
  ⟨wire.head,wire.source,wire.output,name⟩

def strip (gate : Gate) : Wire := ⟨gate.head,gate.source,gate.output⟩

def maximum : List Wire → Nat
  | [] => 0
  | w :: ws => max (max w.source w.output) (maximum ws)

def attach : Nat → List Wire → List Gate
  | _, [] => []
  | n, w :: ws => install w n :: attach (n+1) ws

/-- The original list is unchanged. Every position gets a strictly
monotone candidate name; a finite gate never allocates that candidate. -/
def allocate (wires : List Wire) : List Gate := attach (maximum wires + 1) wires

def OriginalConjunction (f : Nat → Nat) (ν : Valuation) (wires : List Wire) : Prop :=
  ∀ w ∈ wires, originalGraph f w.head w.source w.output ν

def ExactFreshAllocation : Prop :=
  ∀ wires : List Wire,
    (allocate wires).map strip = wires ∧ Fresh (allocate wires) ∧
      ∀ n ∈ hiddenNames (allocate wires), maximum wires < n

def ExactAllocatedWireNormalization : Prop :=
  ∀ (f : Nat → Nat) (wires : List Wire) (ν : Valuation),
    (∀ θ : Valuation,
      (NormalizedAt f θ (allocate wires) ∧ Agrees (allocate wires) ν θ) ↔
        OriginalConjunction f ν wires ∧ θ = extend ν (allocate wires)) ∧
    ((∃! θ : Valuation, NormalizedAt f θ (allocate wires) ∧ Agrees (allocate wires) ν θ) ↔
      OriginalConjunction f ν wires) ∧
    (∀ n : Nat, n ≤ maximum wires → extend ν (allocate wires) n = ν n)

def FullArbitraryHeadFreshWireAllocation : Prop :=
  ExactFreshAllocation ∧ ExactAllocatedWireNormalization

end LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
