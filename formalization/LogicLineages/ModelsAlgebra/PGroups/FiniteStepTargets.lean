module
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Both actual extension steps must be proved, not assumed as a finiteness oracle. -/
def groupFiniteStepFiniteUlm : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) (S : AddSubgroup G),
    Finite (pStep p S) → Finite (UlmLayer p S) → Finite S

end LogicLineages.ModelsAlgebra.PGroups.Targets
