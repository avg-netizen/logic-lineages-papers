module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalObjectApplicationSpineGlobalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobal
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The complete preceding one-tuple package, with its native calibration,
all-input old-leaf equality, original full Package and every earlier Object,
fold and guarded raw-step law retained literally. -/
def RetainedProperties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity p ∧
    (let q := OriginalSpineGuardLeaf.refineInputs p
     (∀ v : List.Vector Nat 4, evaluate q.oldStep v = evaluate p.oldStep v) ∧
     GlobalSourcePackage.InputsCalibrated n arity q ∧
     OriginalObjectApplicationSpineGlobal.FinalProperties n arity q ∧
     (let r := OriginalApplicationSidecar.finalInputs q
      OriginalSelectedStepSpine.RawStepHasSpineGuard
        (OuterSelection.data r.base r.window) r.oldStep))

/-- New original certificate consumers at the SAME final tuple, shared by
all source contexts and internally bound Gamma values. No computability at
an arrow or whole-source accessibility theorem is asserted here. -/
def CertificateProperties (p : GlobalSourcePackage.Inputs) : Prop :=
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let data := OuterSelection.data r.base r.window
  OriginalQuotientSpine.QuotientHasSpineGuard data r.window r.oldStep ∧
    (∀ context : Nat,
      OriginalFunctionChildCertificate.FunctionChildCertificates data r.window r.oldStep
        (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context) ∧
    (∀ context : Nat,
      OriginalSameCodeSuffix.ObjectSuffix data r.window r.oldStep
        (GlobalSourcePackage.source r) context)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalChildCertificateGlobal
