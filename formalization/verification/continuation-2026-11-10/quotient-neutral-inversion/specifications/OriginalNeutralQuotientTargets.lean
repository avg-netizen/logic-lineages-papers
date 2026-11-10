module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open UniformCertificateCompletion OriginalVariableObject OriginalNeutralQuotient
open OriginalApplicationComponentCoherenceGlobalTargets

/-- The SAME final sidecar-refined tuple supplies original neutral quotient
edge inversion. The raw function child yields an actual quotient edge under
the original checker, and both canonical application outputs share the SAME
actual folded argument. No canonical input idempotence premise is present. -/
def ActualOriginalNeutralQuotientEdgeElimination : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let r := OriginalApplicationSidecar.finalInputs p
  NeutralQuotientEdges (OuterSelection.data r.base r.window) r.window r.oldStep

/-- Choose ONE original tuple before every window and ambient context. Its
SAME final tuple retains calibration, full Package and all previously stated
root, neutrality, bottom, variable and paired-component laws while adding
the original neutral quotient-edge eliminator. This does not assert neutral
arrow computability or alignment with arbitrary requested raw arguments. -/
def ActualOriginalNeutralQuotientGlobalSelection : Prop :=
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
     NeutralQuotientEdges (OuterSelection.data r.base r.window) r.window r.oldStep ∧
     ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
       SubtypeClosed (fun tau => tau ∈ S) →
       let context := OrdinaryArithmeticQuotient.contextCode symbols S table
       VariableCertificateBottom (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context ∧
       VariableLeast (GlobalSourcePackage.source r)
         (GlobalSourcePackage.computability r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralQuotientTargets
