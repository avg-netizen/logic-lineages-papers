module
public import LogicLineages.ModelsAlgebra.PGroups.DirectSumUlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe u v w
/-- Source statement following eq:p-filtration-direct-sums: actual heterogeneous
Ulm layers commute with arbitrary direct sums at every ordinal. -/
def transfiniteDirectSumUlm : Prop :=
  ∀ {ι : Type u} {G : ι → Type v} [∀ i, AddCommGroup (G i)]
    (p : ℕ) (α : Ordinal.{w}),
    Nonempty (UlmLayer p (transfiniteFiltration p α : AddSubgroup (DirectSum ι G)) ≃ₗ[ZMod p]
      DirectSum ι (fun i => UlmLayer p (transfiniteFiltration p α : AddSubgroup (G i))))
/-- Actual cardinal dimensions add; no assigned invariant or classification premise. -/
def transfiniteDirectSumUlmRank : Prop :=
  ∀ {ι : Type u} {G : ι → Type v} [∀ i, AddCommGroup (G i)]
    (p : ℕ) [Fact p.Prime] (α : Ordinal.{w}),
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (DirectSum ι G))) =
      Cardinal.sum (fun i => Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p α : AddSubgroup (G i))))
end LogicLineages.ModelsAlgebra.PGroups.Targets
