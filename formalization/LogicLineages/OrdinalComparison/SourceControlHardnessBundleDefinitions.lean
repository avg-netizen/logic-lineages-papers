module
public import LogicLineages.OrdinalComparison.SourceGammaCoREClassificationDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaWeakCoREClassificationDefinitions
public import LogicLineages.OrdinalComparison.ParametricCanonicalObservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle
/-- Standard co-RE universal property on natural codes, spelled out independently. -/
def CoREComplete (P : Nat → Prop) : Prop :=
  REPred (fun n => ¬P n) ∧ ∀ Q : Nat → Prop,
    REPred (fun n => ¬Q n) → ManyOneReducible Q P
end LogicLineages.OrdinalComparison.Source.SourceControlHardnessBundle
