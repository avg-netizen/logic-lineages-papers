module

public import LogicLineages.ModelsAlgebra.Forests.LeafClusterDefinitions

/-! Literal JEP for the finite forest width classes, paper03 thm:width.
Embeddings are ordinary order embeddings, with no root/meet/leaf restrictions. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests

def WidthHasJEP (m : Nat) : Prop :=
  ∀ F G : FiniteOrderForest, WidthAtMost F.Carrier m → WidthAtMost G.Carrier m →
    ∃ H : FiniteOrderForest, WidthAtMost H.Carrier m ∧
      Nonempty (F.Carrier ↪o H.Carrier) ∧ Nonempty (G.Carrier ↪o H.Carrier)

end LogicLineages.ModelsAlgebra.Forests
