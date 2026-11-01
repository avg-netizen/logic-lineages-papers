module
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryRenamingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
/-- A literal finite group table together with finitely many labelled
original-language observations; variables for table entries are appended. -/
noncomputable def pointedTableMatrix (K:Type) [AddCommGroup K] [Fintype K]
    (n m:ℕ) (a:Fin m→K) (t:Fin m→GroupTerm n) : QF (n+Fintype.card K) :=
  .and (finiteImageTableMatrix K 1 n)
    (finiteAnd m fun i=>.equal (tableTerm K 1 n (a i))
      (renameTerm (Fin.castAdd (Fintype.card K)) (t i)))
noncomputable def pointedTableFormula (K:Type) [AddCommGroup K] [Fintype K]
    (n m:ℕ) (a:Fin m→K) (t:Fin m→GroupTerm n) : Formula n :=
  .disjEx {0} (fun _=>Fintype.card K) (fun _=>.qf (pointedTableMatrix K n m a t))
end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
