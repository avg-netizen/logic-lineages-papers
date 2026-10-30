module

public import LogicLineages.ModelsAlgebra.Forests.LaminarForestDefinitions

/-! Concrete comb cluster family on m leaves. Suffix indices lie in Fin m, so
no empty terminal suffix is included. The rooted binary comb targets require
m>0; m=1 is the singleton case. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

def combSuffix (m : Nat) (k : Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun i => k ≤ i)

def combFamily (m : Nat) : Finset (Finset (Fin m)) :=
  Finset.univ.image (fun i : Fin m => {i}) ∪ Finset.univ.image (combSuffix m)

end LogicLineages.ModelsAlgebra.Forests
