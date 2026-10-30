module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v w

def groupOneImageIsomorphism : Prop :=
  ∀ (G : Type u) [AddCommGroup G], Nonempty (multipleImage G 1 ≃+ G)

/-- Literal finite group table and cardinality bound in the ordinary language. -/
def groupFiniteIsomorphismSentence : Prop :=
  ∀ (K : Type w) [AddCommGroup K] [Fintype K],
    (finiteImageIsomorphismFormula K 1).AtLevel (1 : Ordinal.{v}) ∧
      ∀ (G : Type u) [AddCommGroup G],
        (finiteImageIsomorphismFormula K 1).Realize (Fin.elim0 : Fin 0 → G) ↔
          Nonempty (G ≃+ K)

/-- Relative d-Sigma-one Scott description of a finite additive group.
This includes the trivial group without an exact-minimality assertion. -/
def groupFiniteDifferenceScott : Prop :=
  ∀ (K : Type u) [AddCommGroup K] [Fintype K],
    DifferenceScottSentence K (finiteImageIsomorphismFormula K 1)

end LogicLineages.ModelsAlgebra.PGroups.Targets
