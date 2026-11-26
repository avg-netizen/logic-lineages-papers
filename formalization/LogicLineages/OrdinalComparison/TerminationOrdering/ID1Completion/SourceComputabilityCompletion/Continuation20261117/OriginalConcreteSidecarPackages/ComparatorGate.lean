module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSidecarPackages.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSidecarPackages.ComparatorGate
open Continuation20261114 Continuation20261115 Continuation20261116
open Source UniformCertificateCompletion TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem exactConcretePackages : Targets.ConcretePackages ↔
 (∀ (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (W : Program 2),
  GlobalSourcePackage.InputsCalibrated n arity p →
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W →
  let H := OriginalConcreteHeadSignature.signature n arity
  let G := OriginalDecodedContextValidity.contextGuard n
  let T := OriginalTypedDecoder.target H G
  let Q := OriginalCandidates.candidates n arity H
  let E := OriginalConcreteStructuralEdge.edge n arity
  let L := SeededPrimaryPool.primary T Q E
  let D := TransparentCandidate.candidate T
  let q := Membership.inputs p H G L D
  let r := OriginalApplicationSidecar.finalInputs (OriginalSpineGuardLeaf.refineInputs q)
  let data := OuterSelection.data r.base r.window
  (OriginalQuotientSpine.QuotientHasSpineGuard data r.window r.oldStep ∧
    (∀ context : Nat,
      OriginalFunctionChildCertificate.FunctionChildCertificates data r.window r.oldStep
        (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context) ∧
    (∀ context : Nat,
      OriginalSameCodeSuffix.ObjectSuffix data r.window r.oldStep
        (GlobalSourcePackage.source r) context)) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    let src := GlobalSourcePackage.source r
    let comp := GlobalSourcePackage.computability r
    OriginalApplicationComputability.AcceptedOutputNonLambda comp context ∧
      OriginalApplicationComputability.AcceptedApplicationComputable comp context ∧
      OriginalNeutralExpansion.ApplicationSuccessorComputability src comp context ∧
      OriginalNeutralExpansion.NeutralComputabilityExpansion src comp context ∧
      OriginalVariableComputability.VariableComputable src comp context)) := Iff.rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSidecarPackages.ComparatorGate
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSidecarPackages.ComparatorGate
