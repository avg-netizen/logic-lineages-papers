module

public import LogicLineages.NativeModule.PersistentMarking.ActualCollapseMainTargets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.Paper16RemainingOrdinalTargets
open Ordinal OrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerSequenceTargets
open ActualCollapse ConditionalTowerCofinality

/-- The operations in the printed construction, with their arithmetic
and omega equations. ActualCollapseMain.SolutionExists supplies existence. -/
structure OrdinalSemantics where
  zero : CountableOrdinal
  successor : CountableOrdinal → CountableOrdinal
  add : CountableOrdinal → CountableOrdinal → CountableOrdinal
  mul : CountableOrdinal → CountableOrdinal → CountableOrdinal
  omega : CountableOrdinal
  one : CountableOrdinal
  pow : CountableOrdinal → CountableOrdinal
  fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal
  arithmetic : OrdinalArithmeticEquations zero successor add mul
  omegaEquations : OmegaArithmeticEquations zero successor mul omega one pow fix

def OrdinalSemanticsExistence : Prop := Nonempty OrdinalSemantics

noncomputable def OrdinalSemantics.collapse (A : OrdinalSemantics) :
    CollapseData ActualIndex Ordinal.{0} :=
  veblenData A.fix A.pow A.omega

noncomputable def OrdinalSemantics.endpointValue (A : OrdinalSemantics) : Ordinal.{0} :=
  A.collapse.psi actualEndpoint

/-- The pointwise identity for the actual native tower and the actual
clause-(P) collapse at the same ordinal operations. -/
def CalibrationAt (A : OrdinalSemantics) (n : Nat) : Prop :=
  (sequenceValue A.fix A.pow A.omega n).val = A.collapse.psi (actualArgument n)

def AllTowerCalibration : Prop := ∀ (A : OrdinalSemantics) (n : Nat), CalibrationAt A n

/-- The existing assembly consumes an existential choice of operations
for each actual collapse. The pointwise target above supplies it by
choosing the operations of that very collapse. -/
def CalibrationForAssembly : Prop :=
  ∀ A : OrdinalSemantics, ExternalOrdinalInterfaceTargets.Calibration A.collapse

/-- One explicit way to discharge the ordinal-analysis input against the
actual endpoint used by the native lower construction. -/
def NormAtActualEndpoint : Prop :=
  ∀ A : OrdinalSemantics, ExternalOrdinalInterfaceID1Targets.NormTheorem A.endpointValue

/-- The printed identification, parameterized by the independently
specified ordinal of the cited inductive-norm theorem. -/
def IdentifyCitedEndpoint (citedBH : Ordinal.{0}) : Prop :=
  ∀ A : OrdinalSemantics, ExternalOrdinalInterfaceTargets.BHIdentification A.collapse citedBH

/-- An independent arithmetic calibration candidate. Identifying this
least bound with the cited ordinal requires a separate source theorem. -/
def LeastNormBound (β : Ordinal.{0}) : Prop :=
  ExternalOrdinalInterfaceID1Targets.NormTheorem β ∧
    ∀ γ : Ordinal.{0}, ExternalOrdinalInterfaceID1Targets.NormTheorem γ → β ≤ γ

/-- The source upper-bound assembly at the ordinal of the norm theorem. -/
def UpperAtCitedOrdinal (citedBH : Ordinal.{0}) : Prop :=
  ExternalOrdinalInterfaceID1Targets.NormTheorem citedBH →
    ConditionalUpperTargets.UpperStatement citedBH

def UpperAtActualEndpoint : Prop :=
  ∀ A : OrdinalSemantics, ConditionalUpperTargets.UpperStatement A.endpointValue

/-- The first equality of the printed tower lemma, in the actual data.
The equality with the cited ordinal is the separate identification target. -/
def CofinalityAtActualEndpoint : Prop :=
  ∀ A : OrdinalSemantics, (⨆ n, A.collapse.psi (actualArgument n)) = A.endpointValue

def CofinalityAtCitedOrdinal (citedBH : Ordinal.{0}) : Prop :=
  ∀ A : OrdinalSemantics,
    (⨆ n, A.collapse.psi (actualArgument n)) = A.endpointValue ∧ A.endpointValue = citedBH

def HeightAtActualEndpoint : Prop :=
  ∀ A : OrdinalSemantics,
    ConditionalHeightEffectiveTargets.HeightIsBHEffective A.endpointValue

def PrincipalAtActualEndpoint : Prop :=
  ∀ A : OrdinalSemantics,
    ConditionalMain16UniformEffectiveCodedTargets.Main16StatementCodedEffective A.endpointValue

end LogicLineages.PersistentMarking.Paper16RemainingOrdinalTargets
