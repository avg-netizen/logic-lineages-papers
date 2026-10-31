module
public import LogicLineages.ModelsAlgebra.Forests.RankedIdealMachineDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata
open RankedParse ProfileAutomatonEncoding

/-- Literal finite transition tables, including epsilon transitions.
No language, regularity, productivity or determinization oracle is a field. -/
structure Automaton where
  State : Type
  stateFintype : Fintype State
  stateDecidableEq : DecidableEq State
  leaf : Finset State
  node : Operation → State → State → Finset State
  epsilon : State → Finset State
  final : Finset State
attribute [instance] Automaton.stateFintype Automaton.stateDecidableEq

inductive Run (A : Automaton) : Term → A.State → Prop where
  | atom {q} : q ∈ A.leaf → Run A .atom q
  | node {l r x y q} (o) : Run A l x → Run A r y → q ∈ A.node o x y →
      Run A (.node o l r) q
  | epsilon {t x y} : Run A t x → y ∈ A.epsilon x → Run A t y

def Accepts (A : Automaton) (t : Term) : Prop := ∃ q, Run A t q ∧ q ∈ A.final

def step (A : Automaton) (S : Finset A.State) : Finset A.State :=
  S ∪ S.biUnion A.epsilon

def steps (A : Automaton) (S : Finset A.State) : Nat → Finset A.State
  | 0 => S
  | n+1 => step A (steps A S n)

def close (A : Automaton) (S : Finset A.State) : Finset A.State :=
  steps A S (Fintype.card A.State)

inductive Closure (A : Automaton) (S : Finset A.State) : A.State → Prop where
  | seed {q} : q ∈ S → Closure A S q
  | edge {q r} : Closure A S q → r ∈ A.epsilon q → Closure A S r

def nodeSeeds (A : Automaton) (o : Operation) (S T : Finset A.State) : Finset A.State :=
  S.biUnion (fun x => T.biUnion (A.node o x))

def evaluate (A : Automaton) : Term → Finset A.State
  | .atom => close A A.leaf
  | .node o l r => close A (nodeSeeds A o (evaluate A l) (evaluate A r))

def determinize (A : Automaton) : Machine where
  State := Finset A.State
  stateFintype := inferInstance
  leaf := close A A.leaf
  node := fun o S T => close A (nodeSeeds A o S T)
  accept := fun S => decide (∃ q ∈ S, q ∈ A.final)
end LogicLineages.ModelsAlgebra.Forests.RankedIdealAutomata
