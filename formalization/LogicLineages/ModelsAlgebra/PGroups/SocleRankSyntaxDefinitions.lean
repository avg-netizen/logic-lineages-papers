module
public import LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteConjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
noncomputable def socleUpperFormula (p:ℕ) [Fact p.Prime] (j n m:ℕ) : Formula n :=
  (socleLowerFormula p j n (m+1)).dual
noncomputable def infiniteSocleFormula (p:ℕ) [Fact p.Prime] (j n:ℕ) : Formula n :=
  countableConjAll (fun _:ℕ=>0) (fun m=>socleLowerFormula p j n m)
noncomputable def socleRankEntry (p:ℕ) [Fact p.Prime] (j n:ℕ) : Option ℕ → Formula n
  | none => infiniteSocleFormula p j n
  | some m => piConjunction (piWrap (socleLowerFormula p j n m)) (socleUpperFormula p j n m)
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
