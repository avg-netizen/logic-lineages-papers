module
public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

def distinctTermMatrix {n m : ℕ} (t : Fin m → GroupTerm n) : QF n :=
  finiteAnd m fun i => finiteAnd m fun j =>
    if i = j then .neg .falsum else .neg (.equal (t i) (t j))

/-- A finite table evaluated on terms in the original free variables;
no extra witnesses or quantifiers are introduced. -/
noncomputable def finiteTermTable (K : Type u) [AddCommGroup K] [Fintype K]
    {n : ℕ} (t : K → GroupTerm n) : QF n :=
  let e := Fintype.equivFin K
  .and (distinctTermMatrix (fun i => t (e.symm i)))
    (.and (.equal (t 0) .zero)
      (.and (finiteAnd (Fintype.card K) fun i =>
        .equal (t (-e.symm i)) (.neg (t (e.symm i))))
        (finiteAnd (Fintype.card K) fun i => finiteAnd (Fintype.card K) fun j =>
          .equal (t (e.symm i + e.symm j)) (.add (t (e.symm i)) (t (e.symm j))))))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
