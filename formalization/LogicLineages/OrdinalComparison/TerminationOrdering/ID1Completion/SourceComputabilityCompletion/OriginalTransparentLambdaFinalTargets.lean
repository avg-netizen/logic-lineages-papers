module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargets
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion OriginalTransparentLambdaFinal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal fields of the ACTUAL selection for arbitrary raw Data,
representative and window Programs. No graph law follows from native equality. -/
def ActualOriginalTransparentFinalSelectionFields : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
  (selectedData rawData representative window).oldSource =
      BottomParameter.normalized (OriginalTransparentLambdaValidity.sourceValidator rawData) ∧
  (selectedData rawData representative window).oldTarget =
      BottomParameter.normalized (OriginalTransparentLambdaValidity.targetValidator rawData) ∧
  (selectedData rawData representative window).member =
      InternalOriginalUniformContextMembership.normalizedMember rawData.member

/-- All-output internal absorption of the existing target application fold,
independent of calibration, source validity or representative properties. -/
def ActualOriginalTransparentFinalTargetCollapse : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
    TargetCollapse rawData (selectedData rawData representative window)

/-- All-output internal absorption of the existing universe application fold
with its actual once-normalized member and bottom-normalized source leaf. -/
def ActualOriginalTransparentFinalUniverseCollapse : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
    UniverseCollapse rawData (selectedData rawData representative window)

/-- Keep target AND source validators in the exact final conjunction. No
unproved source-to-target property is added as a hypothesis or hidden field. -/
def ActualOriginalTransparentFinalSourceCollapse : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
    SourceCollapse rawData (selectedData rawData representative window)

/-- Actual final source lambda elimination/reconstruction, including both
outer and domain membership and its SAME final source at the actual body.
All raw Data and representatives are arbitrary; no body acceptance is assumed. -/
def ActualOriginalTransparentFinalSourceLambda : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
    SourceLambdaLaw (selectedData rawData representative window)

/-- Actual final target lambda elimination/reconstruction has NO source-
window membership and calls the SAME final target at the actual body. -/
def ActualOriginalTransparentFinalTargetLambda : Prop :=
  ∀ (rawData : Data) (representative : Program 2) (window : Program 1),
    TargetLambdaLaw (selectedData rawData representative window)

/-- Native calibration and literal AST identities are distinct obligations.
The actual final tuple is the generic representative-independent selection
at its own final representative and window; there is no earlierData proxy. -/
def ActualOriginalTransparentFinalPreparation : Prop :=
  (∀ p : GlobalSourcePackage.Inputs,
    finalData p = selectedData p.base (finalInputs p).base.oldRepresentative
        (finalInputs p).window ∧
      (finalInputs p).window = p.window) ∧
  (∀ (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs),
    GlobalSourcePackage.InputsCalibrated n arity p → NativeRefinement n arity p)

/-- ONE original globally calibrated p is selected before every finite
window, Gamma and internal derivation. Preserve the ENTIRE prior hereditary
Properties at refineInputs p and append the new validity laws at precisely
its SAME finalData. No part of the original Package is replaced or dropped. -/
def ActualOriginalTransparentFinalGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ p : GlobalSourcePackage.Inputs,
      GlobalSourcePackage.InputsCalibrated n arity p ∧ Properties n arity p

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalTargets
