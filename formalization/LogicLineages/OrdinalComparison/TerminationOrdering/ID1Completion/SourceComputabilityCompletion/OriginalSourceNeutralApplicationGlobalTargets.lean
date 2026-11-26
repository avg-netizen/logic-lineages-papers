module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationPathTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalTargets
open Source UniformCertificateCompletion OriginalVariableObject
open OriginalApplicationComponentCoherenceGlobalTargets

/-- One original tuple is selected before all contexts, finite source windows
and ambient derivations. Its SAME final tuple retains the full calibrated
Package and every earlier root/neutral/variable/paired-component law, adds the
original non-lambda first-edge laws, and exposes the actual Object inputs and
original source H+ first edge with its unchanged suffix. No finite-type
computability induction or closed all-term accessibility is asserted here. -/
def ActualOriginalSourceNeutralApplicationGlobalSelection : Prop :=
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
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationGlobalTargets
