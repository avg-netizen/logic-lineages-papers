module
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction
def coefficient (e : Nat) : Nat := 2^e
def oddConstant (b : Nat) : Nat := 2*b+5
def argument (b e t : Nat) : Nat := coefficient e * (2*t+oddConstant b)

/-- Exactly the displayed three equations, over natural-number witnesses. -/
def Conjunction (b e t z y w : Nat) : Prop :=
  z+4 = coefficient e * (2*t+oddConstant b) ∧
  y = SourceMachineControlNonperiodicity.gamma b (z+4) ∧ y = w+w+1

def Satisfiable (b e : Nat) : Prop := ∃ t z y w : Nat, Conjunction b e t z y w
end LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction
