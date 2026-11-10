module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTargets
open FirstOrder Language Source
open UniformCertificateCompletion OriginalVariableObject OriginalNeutralApplicationEdge
open OriginalApplicationComponentCoherenceGlobalTargets

/-- On the SAME final globally selectable tuple, a neutral actualJ output
has only literal same-type bottom or an original quotient function-step
whose target application uses the requested RAW argument unchanged. No
caller-supplied canonical component, second function fold or idempotence
premise replaces the original input semantics. -/
def ActualOriginalNeutralApplicationEdgeElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  NeutralApplicationEdges (OuterSelection.data r.base r.window) r.window r.oldStep

/-- One original tuple is selected before every window and ambient context.
Its SAME final tuple retains the complete calibrated source package, all
previous root/neutral/variable/paired-component laws and generic neutral
quotient inversion, together with the requested-argument application rule. -/
def ActualOriginalNeutralApplicationEdgeGlobalSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ p : GlobalSourcePackage.Inputs,
    GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let r := OriginalApplicationSidecar.finalInputs p
     GlobalSourcePackage.InputsCalibrated n arity r ∧
     GlobalSourcePackage.Package n arity
       (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r)
       (GlobalSourcePackage.lift r) ∧
     OriginalConstructorShape.FullFoldRootFields (OuterSelection.data r.base r.window) r.window ∧
     OriginalFunctionNeutrality.FullFoldMarkPreservation (OuterSelection.data r.base r.window) r.window ∧
     OriginalNeutralLeaf.NeutralBottom (OriginalNeutralLeaf.endpoint r) r.window r.oldStep ∧
     PairedComponents (OuterSelection.data r.base r.window) r.window ∧
     OriginalNeutralQuotient.NeutralQuotientEdges
       (OuterSelection.data r.base r.window) r.window r.oldStep ∧
     NeutralApplicationEdges (OuterSelection.data r.base r.window) r.window r.oldStep ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationEdgeTargets
