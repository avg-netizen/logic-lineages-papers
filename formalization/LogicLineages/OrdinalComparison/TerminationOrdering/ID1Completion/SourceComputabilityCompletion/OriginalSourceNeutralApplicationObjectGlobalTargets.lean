module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectGlobalTargets
open Source UniformCertificateCompletion OriginalVariableObject
open OriginalApplicationComponentCoherenceGlobalTargets

/-- ONE original tuple precedes all windows and runtime Gamma values. Its
SAME finalInputs tuple retains the complete prior calibrated Package and
every original root/neutral/variable/paired-component/first-edge law. The
original full fold additionally preserves the spine mark, and the function
case reconstructs the accepted Object application at the first vertex with
the SAME argument Object. No new source refinement, function-child source
certificate, suffix-computability law or finite-type induction is assumed. -/
def ActualOriginalSourceNeutralApplicationObjectGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := OriginalApplicationSidecar.finalInputs p
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
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationObjectGlobalTargets
