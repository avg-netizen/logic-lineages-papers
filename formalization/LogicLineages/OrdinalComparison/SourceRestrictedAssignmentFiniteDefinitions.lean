module
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentDefinitions
public import LogicLineages.OrdinalComparison.SourceMachineRawValuationsDefinitions
public import LogicLineages.OrdinalComparison.ParametricSourceEraserDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Syntactic absence of the literal omega constructor, not absence of collapse. -/
def OmegaFree {ι : Type} : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι → Prop
  | .var _ | .zero | .one => True
  | .omega => False
  | .add a b | .emul a b | .collapse a b => OmegaFree a ∧ OmegaFree b
end LogicLineages.OrdinalComparison.Source.SourceRestrictedAssignmentFinite
