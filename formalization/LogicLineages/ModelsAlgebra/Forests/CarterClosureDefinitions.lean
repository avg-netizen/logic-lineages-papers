module

public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataDefinitions
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.SDiff

/-! Effective closure for the literal total deterministic machines. Boolean
product tables do not assume semantic correctness; it is proved separately. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterAutomata

def complementMachine {k q : Nat} (M : Automaton k q) : Automaton k q :=
  { M with accepting := Finset.univ \ M.accepting }

def productMachine {k q r : Nat} (mode : Bool → Bool → Bool)
    (M : Automaton k q) (N : Automaton k r) : Automaton k (q * r) where
  leafState a := finProdFinEquiv (M.leafState a, N.leafState a)
  nodeState a x y := finProdFinEquiv
    (M.nodeState a (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
     N.nodeState a (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  accepting := Finset.univ.filter (fun s =>
    mode (decide ((finProdFinEquiv.symm s).1 ∈ M.accepting))
      (decide ((finProdFinEquiv.symm s).2 ∈ N.accepting)) = true)

def intersectionMachine {k q r : Nat} (M : Automaton k q) (N : Automaton k r) :=
  productMachine Bool.and M N

def unionMachine {k q r : Nat} (M : Automaton k q) (N : Automaton k r) :=
  productMachine Bool.or M N

def symmetricDifferenceMachine {k q r : Nat} (M : Automaton k q) (N : Automaton k r) :=
  productMachine Bool.xor M N

def languageEquivalent {k q r : Nat} (M : Automaton k q) (N : Automaton k r) : Bool :=
  languageEmpty (symmetricDifferenceMachine M N)

end LogicLineages.ModelsAlgebra.Forests.CarterAutomata
