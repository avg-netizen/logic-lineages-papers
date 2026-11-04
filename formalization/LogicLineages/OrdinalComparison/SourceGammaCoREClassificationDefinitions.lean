module
public import LogicLineages.OrdinalComparison.SourceGammaSemidecisionDefinitions
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCoREClassification
def language (b : Nat) : Nat → Prop :=
  SourceGammaRestrictedReduction.Member (SourceMachineControlNonperiodicity.gamma b)
def nonhalting (e : Nat) : Prop := ¬SourceBlankMachineSimulation.Halts e
end LogicLineages.OrdinalComparison.Source.SourceGammaCoREClassification
