module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixTargets
open UniformCertificateCompletion OriginalSameCodeSuffix
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Structural same-code conversion only; this is not yet guarded R = H+. -/
def ActualOriginalSameCodeNonzeroPathPositive : Prop :=
  ∀ edge : Program 4, NonzeroPathPositive edge

/-- The concrete selected tuple discharges the guard propagation, with the
same refined original leaf and unchanged final pipeline. No supplier law or
native-to-arithmetic reflection is admitted as a premise. -/
def ActualOriginalSameCodeFinalPositivePathGuards : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  PositivePathGuards (OuterSelection.data r.base r.window) r.window r.oldStep

/-- Arbitrary source contexts, types and runtime Gamma values use the SAME
final tuple. Original guarded certificates retain the literal suffix code;
the nil alternative is actual same-Gamma Object equality. -/
def ActualOriginalSameCodeFinalObjectSuffix : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ context : Nat,
  ObjectSuffix (OuterSelection.data r.base r.window) r.window r.oldStep
    (GlobalSourcePackage.source r) context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixTargets
