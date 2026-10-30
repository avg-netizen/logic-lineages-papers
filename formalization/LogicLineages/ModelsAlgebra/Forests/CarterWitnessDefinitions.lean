module

public import LogicLineages.ModelsAlgebra.Forests.CarterAutomataDefinitions
public import Mathlib.Data.List.FinRange

/-! Explicit bounded syntax enumeration and accepted-tree witness extraction.
No topological containment or source forest representation is asserted. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CarterAutomata

def treesUpTo (k : Nat) : Nat → List (BinaryLabelTree k)
  | 0 => []
  | n + 1 => (List.finRange k).map BinaryLabelTree.leaf ++
      (List.finRange k).flatMap (fun a => (treesUpTo k n).flatMap
        (fun l => (treesUpTo k n).map (BinaryLabelTree.node a l)))

def vertexCount {k : Nat} : BinaryLabelTree k → Nat
  | .leaf _ => 1
  | .node _ l r => 1 + vertexCount l + vertexCount r

def acceptedWitness {k q : Nat} (M : Automaton k q) : Option (BinaryLabelTree k) :=
  (treesUpTo k q).find? (fun t => decide (run M t ∈ M.accepting))

end LogicLineages.ModelsAlgebra.Forests.CarterAutomata
