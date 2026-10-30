module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions

@[expose] public section

/-! Literal difference-of-Sigma syntax and finite image cardinality formulas.
The two components are ordinary formulas; truth is their actual conjunction.
This adds no constructor to the already frozen Sigma/Pi normal-form syntax. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

universe u v

structure DifferenceFormula (n : ℕ) where
  sigmaPart : Formula n
  piPart : Formula n

def DifferenceFormula.Realize {n : ℕ} {G : Type u} [AddCommGroup G]
    (d : DifferenceFormula n) (a : Fin n → G) : Prop :=
  d.sigmaPart.Realize a ∧ d.piPart.Realize a

/-- The source d-Sigma_alpha convention, with both concrete syntactic ranks. -/
def DifferenceFormula.AtLevel {n : ℕ} (α : Ordinal.{v}) (d : DifferenceFormula n) : Prop :=
  Complexity .sigma α d.sigmaPart ∧ Complexity .pi α d.piPart

/-- All (m+1)-tuples have two equal c-multiples, expressed by the literal
negation of their finite distinctness matrix. -/
def boundedMultipleImage (c m : ℕ) : Formula 0 :=
  .conjAll {0} (fun _ => m + 1)
    (fun _ => .qf (.neg (distinctMultipleMatrix c 0 (m + 1))))

/-- At least m distinct values, and at most m values. This is an actual
conjunction, not an isomorphism table or a Scott predicate. -/
def exactMultipleImageCard (c m : ℕ) : DifferenceFormula 0 :=
  ⟨distinctMultiples c 0 m, boundedMultipleImage c m⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
