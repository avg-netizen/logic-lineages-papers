module

public import LogicLineages.ModelsAlgebra.PGroups.EndomorphismIteration
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Countable.Basic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

instance iterationDirectedSystem {G : Type*} [AddCommGroup G] (f : G →+ G) :
    DirectedSystem (fun _ : ℕ => G) (iterationTransition f · · ·) where
  map_self := fun {i} x => iteration_transition_identity G f i x
  map_map := fun {k j i} hij hjk x => iteration_transition_composition G f i j k hij hjk x

/-- The actual quotient direct limit of the iterated endomorphism system. -/
abbrev EndomorphismLimit {G : Type*} [AddCommGroup G] (f : G →+ G) :=
  DirectLimit (fun _ : ℕ => G) (iterationTransition f)

/-- Actual canonical additive homomorphism into the quotient, not a supplied embedding. -/
noncomputable def limitStage {G : Type*} [AddCommGroup G] (f : G →+ G) (i : ℕ) :
    G →+ EndomorphismLimit f where
  toFun x := ⟦⟨i, x⟩⟧
  map_zero' := (DirectLimit.zero_def (G := fun _ : ℕ => G) (f := iterationTransition f) i).symm
  map_add' x y := (DirectLimit.add_def (G := fun _ : ℕ => G) (f := iterationTransition f) i x y).symm

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
