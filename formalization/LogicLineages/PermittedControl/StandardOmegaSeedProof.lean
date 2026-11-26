module
public import LogicLineages.PermittedControl.StandardOmegaPairProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardOmegaSeed.Proof
 theorem standardOmegaSeed : StandardOmegaSeed.StandardOmegaSeed :=
  ⟨SelectedOmegaSeed.Proof.closedSeed, higherSource, actualScaledPair⟩
end LogicLineages.PermittedControl.StandardOmegaSeed.Proof
