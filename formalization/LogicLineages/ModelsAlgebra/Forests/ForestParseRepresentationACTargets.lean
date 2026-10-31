module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationACDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.Targets
open RankedParse

/-- Every literal same-operation association/permutation move preserves the
actual graph. The converse and canonical reduced uniqueness remain separate. -/
def GraphAssociationSound : Prop :=
  ∀ s t, AssociationEquivalent s t → Nonempty (graph s ≃g graph t)

/-- Actual root-kind discrimination by connectedness and complement connectedness,
using the nonempty leaf occurrences in both child graphs. -/
def RootConnectivity : Prop :=
  ∀ s t,
    ¬ (graph (.node .union s t)).Connected ∧
    (graph (.node .join s t)).Connected ∧
    (graph (.node .union s t))ᶜ.Connected ∧
    ¬ (graph (.node .join s t))ᶜ.Connected

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationAC.Targets
