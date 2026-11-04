module
public import LogicLineages.OrdinalComparison.SourceGammaWeakSemidecisionDefinitions
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification
def language (b : Nat) : Nat → Prop :=
  SourceGammaWeakCodedReduction.Member (SourceMachineControlNonperiodicity.gamma b)
def nonhalting (e : Nat) : Prop := ¬SourceBlankMachineSimulation.Halts e
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCoREClassification
