module

public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Literal complete finite group tables for paper01 lines 174–182.
Finite enumeration is ordinary (not a promised computable compiler). Every
entry is a real original-language term/equality; no table correctness oracle
or abstract image-isomorphism predicate is used in the formulas. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u w

/-- The actual additive subgroup of c-multiples. -/
def multipleImage (G : Type u) [AddCommGroup G] (c : ℕ) : AddSubgroup G :=
  (nsmulAddMonoidHom c : G →+ G).range

noncomputable def tableTerm (K : Type w) [AddCommGroup K] [Fintype K]
    (c n : ℕ) (x : K) : GroupTerm (n + Fintype.card K) :=
  multipleTerm c (.var (Fin.natAdd n (Fintype.equivFin K x)))

/-- Exhaustive distinctness, zero, negation and addition tables, evaluated
on the c-multiples of all finite witnesses. -/
noncomputable def finiteImageTableMatrix (K : Type w) [AddCommGroup K] [Fintype K]
    (c n : ℕ) : QF (n + Fintype.card K) :=
  let e := Fintype.equivFin K
  let t := tableTerm K c n
  .and (distinctMultipleMatrix c n (Fintype.card K))
    (.and (.equal (t 0) .zero)
      (.and
        (finiteAnd (Fintype.card K) fun i =>
          .equal (t (-e.symm i)) (.neg (t (e.symm i))))
        (finiteAnd (Fintype.card K) fun i => finiteAnd (Fintype.card K) fun j =>
          .equal (t (e.symm i + e.symm j)) (.add (t (e.symm i)) (t (e.symm j))))))

noncomputable def finiteImageTableFormula (K : Type w) [AddCommGroup K] [Fintype K]
    (c n : ℕ) : Formula n :=
  .disjEx {0} (fun _ => Fintype.card K) (fun _ => .qf (finiteImageTableMatrix K c n))

/-- The full source finite-image description: a table embedding, plus the
actual cardinality upper bound. -/
noncomputable def finiteImageIsomorphismFormula (K : Type w) [AddCommGroup K] [Fintype K]
    (c : ℕ) : DifferenceFormula 0 :=
  ⟨finiteImageTableFormula K c 0, boundedMultipleImage c (Fintype.card K)⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
