module
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
/-- Close every free variable by joining it to each existing existential
block. The positive-Sigma hypothesis in the theorem excludes the fallback. -/
def sigmaCloseAll {n:ℕ} : Formula n→Formula 0
  | .disjEx s m matrix => .disjEx s (fun i=>n+m i)
      (fun i=>renameFormula (Fin.natAdd 0) (matrix i))
  | _ => .qf .falsum
def piCloseAll {n:ℕ} (φ:Formula n) : Formula 0 := (sigmaCloseAll φ.dual).dual
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
