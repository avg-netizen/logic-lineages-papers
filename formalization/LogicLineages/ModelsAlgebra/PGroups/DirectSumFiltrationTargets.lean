module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumFiltrationDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v w
/-- Exact semantics bridge for the embedded subgroup direct sum. -/
def directSumSubgroupCoordinates : Prop :=
  ∀ {ι : Type u} {G : ι → Type v} [∀ i, AddCommGroup (G i)]
    (S : ∀ i, AddSubgroup (G i)) (x : DirectSum ι G),
    x ∈ directSumSubgroup S ↔ ∀ i, x i ∈ S i
/-- Source eq:p-filtration-direct-sums, without countability or prime restrictions. -/
def transfiniteDirectSum : Prop :=
  ∀ {ι : Type u} {G : ι → Type v} [∀ i, AddCommGroup (G i)]
    (p : ℕ) (α : Ordinal.{w}),
    (transfiniteFiltration p α : AddSubgroup (DirectSum ι G)) =
      directSumSubgroup (fun i => (transfiniteFiltration p α : AddSubgroup (G i)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
