module
public import LogicLineages.OrdinalComparison.WWOriginalInputFrontendDefinitions
public import LogicLineages.OrdinalComparison.WWEffectiveFrontendTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-- Identical bound functions on original raw source-query codes, not bounds
on compiler outputs. The two sides use the same original-coordinate arity. -/
def OriginalFrontendBoundEquivalence : Prop :=
  FrontendCoordinateBound OriginalInput.frontend ↔ OriginalInput.CoordinateBound

/-- Original fixed-default source comparison, not the larger numerical query
domain; malformed raw codes carry the explicitly documented true extension. -/
def OriginalSourceCounterEnumerable : Prop :=
  REPred (fun n : Nat => ¬ OriginalInput.CodedGood n)

def OriginalSourceDecisionIffBound : Prop :=
  ComputablePred OriginalInput.CodedGood ↔ OriginalInput.CoordinateBound

def ActualOriginalCounterBound : Prop :=
  OriginalSourceCounterEnumerable ∧ OriginalSourceDecisionIffBound
end LogicLineages.OrdinalComparison.Source.Targets
