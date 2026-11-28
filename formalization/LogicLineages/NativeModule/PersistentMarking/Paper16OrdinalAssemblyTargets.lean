module

public import LogicLineages.NativeModule.PersistentMarking.Paper16RemainingOrdinalTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperUniformTargets

@[expose] public section

/-! # Paper 16 ordinal assembly: which inputs the remaining statements rest on

Frozen before proof (local Fable-trio round, 27 November 2026, root lane). Every statement is an
implication between targets of `Paper16RemainingOrdinalTargets`; nothing here asserts an input.
The inputs are named, never discharged:

- `NormAtActualEndpoint` / `NormTheorem citedBH` (the cited inductive-norm theorem),
- `UniformAccessibility` (= `lem:arithmetic-accessibility`, uniform internal form),
- `AllTowerCalibration` (the cited calibration, pointwise on the actual collapse),
- `IdentifyCitedEndpoint citedBH` (the cited endpoint identification). -/

namespace LogicLineages.PersistentMarking.Paper16OrdinalAssemblyTargets
open Ordinal ActualCollapse ConditionalTowerCofinality
open Paper16RemainingOrdinalTargets ExternalOrdinalInterfaceTargets
open ConditionalUpperUniformTargets (UniformAccessibility)
open ConditionalHeightEffectiveTargets (HeightIsBHEffective)
open ConditionalMain16UniformEffectiveCodedTargets (Main16StatementCodedEffective)

/-- The endpoint value identifies the endpoint of its own collapse. -/
def EndpointSelfIdentification : Prop :=
  ∀ A : OrdinalSemantics, BHIdentification A.collapse A.endpointValue

/-- The pointwise calibration supplies the existential interface of the assembly. -/
def CalibrationFromPointwise : Prop := AllTowerCalibration → CalibrationForAssembly

/-- `thm:upper` at the actual endpoint from the norm theorem there and uniform accessibility. -/
def UpperFromInputs : Prop :=
  NormAtActualEndpoint → UniformAccessibility → UpperAtActualEndpoint

/-- `thm:upper` at the cited ordinal needs, besides its stated norm premise, only accessibility. -/
def UpperAtCitedFromAccessibility : Prop :=
  ∀ citedBH : Ordinal.{0}, UniformAccessibility → UpperAtCitedOrdinal citedBH

/-- `lem:tower-cofinality` at the cited ordinal from the endpoint identification alone. -/
def CitedCofinalityFromIdentification : Prop :=
  ∀ citedBH : Ordinal.{0}, IdentifyCitedEndpoint citedBH → CofinalityAtCitedOrdinal citedBH

/-- `thm:height` at the actual endpoint from the three open inputs. -/
def HeightFromInputs : Prop :=
  NormAtActualEndpoint → UniformAccessibility → AllTowerCalibration → HeightAtActualEndpoint

/-- `thm:main` at the actual endpoint from the three open inputs. -/
def PrincipalFromInputs : Prop :=
  NormAtActualEndpoint → UniformAccessibility → AllTowerCalibration → PrincipalAtActualEndpoint

/-- The four printed statements at an independently specified ordinal, from the four inputs. -/
def PrintedFromInputs : Prop :=
  ∀ citedBH : Ordinal.{0},
    ExternalOrdinalInterfaceID1Targets.NormTheorem citedBH → UniformAccessibility →
    AllTowerCalibration → IdentifyCitedEndpoint citedBH →
    ConditionalUpperTargets.UpperStatement citedBH ∧
    (∀ A : OrdinalSemantics, (⨆ n, A.collapse.psi (actualArgument n)) = citedBH) ∧
    HeightIsBHEffective citedBH ∧ Main16StatementCodedEffective citedBH

end LogicLineages.PersistentMarking.Paper16OrdinalAssemblyTargets
