module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual tail identification determines exact original length, with no
realization/length oracle. Nontriviality is the source prescribed-tail guard. -/
def tailExactLengthTransport : Prop :=
  ∀ (G T:Type) [AddCommGroup G] [AddCommGroup T] [Nontrivial T]
    (p:ℕ) (δ ell:Ordinal.{0}),
    Nonempty ((transfiniteFiltration p δ:AddSubgroup G)≃+T) →
    PGroupExactLength p T ell → PGroupExactLength p G (δ+ell)
end LogicLineages.ModelsAlgebra.PGroups.Targets
