module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateTargets
open UniformCertificateCompletion OriginalFunctionChildCertificate

/-- Use the SAME once-refined leaf and unchanged finalInputs pipeline as the
accepted Object/global selection. The literal original source and computability
Programs come from that SAME final tuple. No arbitrary source correspondence,
extra activation, positive guard or independently selected tuple is assumed.
This supporting source-certificate construction does not assert suffix
computability, arrow computability or the paper06 all-term theorem. -/
def ActualOriginalFinalFunctionChildCertificate : Prop :=
  ∀ p : GlobalSourcePackage.Inputs,
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  ∀ context : Nat,
  FunctionChildCertificates (OuterSelection.data r.base r.window) r.window r.oldStep
    (GlobalSourcePackage.source r) (GlobalSourcePackage.computability r) context

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateTargets
