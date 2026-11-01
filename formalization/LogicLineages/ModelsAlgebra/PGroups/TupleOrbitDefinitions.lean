module
public import LogicLineages.ModelsAlgebra.PGroups.StableStageDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Actual group automorphism orbit; filtration or complexity is not built
into its meaning. -/
def TupleOrbit {G:Type} [AddCommGroup G] {n:ℕ} (a b:Fin n→G) : Prop :=
  ∃ e:G≃+G, ∀i, e (a i)=b i
end LogicLineages.ModelsAlgebra.PGroups
