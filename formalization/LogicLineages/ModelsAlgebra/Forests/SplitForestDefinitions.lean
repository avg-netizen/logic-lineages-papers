module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestDefinitions

/-! Explicit second negative-width witness on m≥4 leaves: root split 2+(m−2).
The right child may multifurcate when m>4; the theorem allows arbitrary forests,
and only the comb requires full binary/maximal-cluster structure. At m=4 this
is the source balanced seven-vertex binary tree. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

def splitLeft (m : Nat) : Finset (Fin m) := Finset.univ.filter (fun i => i.val < 2)

def splitRight (m : Nat) : Finset (Fin m) := Finset.univ.filter (fun i => 2 ≤ i.val)

def splitFamily (m : Nat) : Finset (Finset (Fin m)) :=
  Finset.univ.image (fun i : Fin m => {i}) ∪ {Finset.univ, splitLeft m, splitRight m}

end LogicLineages.ModelsAlgebra.Forests
