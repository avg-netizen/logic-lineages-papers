module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSelectedStepSpineTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobal
open Source UniformCertificateCompletion OriginalVariableObject
open OriginalApplicationComponentCoherenceGlobalTargets

/-- The entire original Object/global package at ONE supplied calibrated input
selection. This is the same per-tuple conjunction as the earlier frozen Object
global target, with no field weakened or dropped. Its final tuple includes
full calibration, the complete Package, root/function/spine fold laws, every
prior neutral/paired/first-edge law and all original context-specific Object
and variable consumers. -/
def FinalProperties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  let r := OriginalApplicationSidecar.finalInputs p
  let data := OuterSelection.data r.base r.window
  GlobalSourcePackage.InputsCalibrated n arity r ∧
  GlobalSourcePackage.Package n arity
    (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
    (GlobalSourcePackage.lift r) ∧
  OriginalConstructorShape.FullFoldRootFields data r.window ∧
  OriginalFunctionNeutrality.FullFoldMarkPreservation data r.window ∧
  OriginalFullFoldSpine.FullFoldMarkPreservation data r.window ∧
  OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint r) r.window r.oldStep ∧
  PairedComponents data r.window ∧
  OriginalNeutralQuotient.NeutralQuotientEdges data r.window r.oldStep ∧
  OriginalNeutralApplicationEdge.NeutralApplicationEdges data r.window r.oldStep ∧
  OriginalNonLambdaApplication.NonLambdaApplicationEdges data r.window r.oldStep ∧
  OriginalNonLambdaApplicationPath.NonLambdaApplicationPositivePaths data r.window r.oldStep ∧
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    OriginalSourceNeutralApplication.ApplicationInputs data r.window
      (GlobalSourcePackage.computability r) context ∧
    OriginalSourceNeutralApplicationPath.SourcePositivePaths data r.window r.oldStep
      (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context ∧
    OriginalSourceApplicationReconstruction.ApplicationReconstruction data r.window
      (GlobalSourcePackage.computability r) context ∧
    OriginalSourceNeutralApplicationObjectPath.ObjectSourcePositivePaths data r.window r.oldStep
      (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context ∧
    VariableCertificateBottom (GlobalSourcePackage.source r)
      (GlobalSourcePackage.computability r) context ∧
    VariableLeast (GlobalSourcePackage.source r)
      (GlobalSourcePackage.computability r) context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobal
