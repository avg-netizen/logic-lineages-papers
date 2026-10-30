module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiltrationDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth

/-- Literal ordinary-language universal annihilation clause. -/
def annihilationFormula (c n : ℕ) : Formula n :=
  .conjAll {0} (fun _ => 1)
    (fun _ => .qf (.equal (multipleTerm c (.var (Fin.natAdd n (0 : Fin 1)))) .zero))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
