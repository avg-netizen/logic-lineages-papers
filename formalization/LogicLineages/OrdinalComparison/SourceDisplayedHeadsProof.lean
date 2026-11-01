module
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProgramProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProvenanceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceDisplayedHeads

theorem full : Targets.FullDisplayedSourceHeads :=
  ⟨program, validity, budget, argument_drop, root_provenance, signed_argument_drop⟩

end LogicLineages.OrdinalComparison.SourceDisplayedHeads
