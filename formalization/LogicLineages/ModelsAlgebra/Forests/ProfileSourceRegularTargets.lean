module
public import LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegularDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.Targets
open RankedParse RankedGraphImage ProfileAutomatonEncoding ForestParseRepresentation

/-- Explicit source-input algorithm, with P4/C4 adjoined, including an empty
additional forbidden graph. No exception is omitted from recognition. -/
def SourceMachineCorrect : Prop :=
  ∀ (F : List RawGraph) (t : Term),
    (sourceMachine F).accept (machineRun (sourceMachine F) t) = true ↔
      GeneralForbiddenLanguage (F.map rawFinite) t

/-- Full source parse-regular language endpoint: a constructed finite ranked
machine recognizes the exact arbitrary source forbidden graph class, whose
language is downward closed under the literal ranked relation. Abstract graph
representation completeness is semantic; the actual input algorithm is the
separate SourceMachineCorrect theorem on conventional finite matrices. -/
def GeneralForbiddenRegular : Prop :=
  ∀ (B : List FiniteGraph),
    (∃ F : List RawGraph, ∀ t,
      (machine F).accept (machineRun (machine F) t) = true ↔
        GeneralForbiddenLanguage B t) ∧
    (∀ s t, Homeomorphic s t → GeneralForbiddenLanguage B t →
      GeneralForbiddenLanguage B s)

end LogicLineages.ModelsAlgebra.Forests.ProfileSourceRegular.Targets
