module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionTypingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralApplicationSuccessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.GlobalSourcePackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalComputabilityApplication OriginalNeutralExpansion OriginalNeutralExpansionTargets
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion

/-- Every relative arithmetic supplier is discharged at the SAME calibrated
final tuple before type induction, source contexts and internally bound Gamma
values. The original source relation and full finite-type C are unchanged. -/
theorem actualOriginalFinalNeutralComputabilityExpansion :
    ActualOriginalFinalNeutralComputabilityExpansion := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let src := GlobalSourcePackage.source r
  let comp := GlobalSourcePackage.computability r
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  have hpackage := (GlobalSourcePackageProof.actualOriginalGlobalSourcePackageConstruction n arity r hr).2.2
  have hwindow := hpackage.2.2.2 symbols S table hS
  have htout := OriginalNeutralTypeInductionTypingProof.outputTyped n arity p hp symbols S table hS
    (SourcePresentation.sourceBody src context)
  have hshape := OriginalApplicationComputabilityProof.actualOriginalFinalAcceptedOutputNonLambda
    n arity p hp symbols S table hS
  have hsucc := OriginalNeutralApplicationSuccessorProof.actualOriginalFinalApplicationSuccessorComputability
    n arity p hp symbols S table hS
  intro tau alpha Gamma object
  let H := typed comp tau (numeral context) object ⊓
    (OriginalSourceNeutralApplication.nonLambdaObject object ⊓
      computableSuccessors src comp context tau object)
  have hh : Nonempty (Derivation (SourcePresentation.sourceBody src context) (H :: Gamma) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hc⟩ := OriginalNeutralTypeInductionCoreProof.neutral src comp context
    hwindow.1 hwindow.2.2.1 htout hshape hsucc tau alpha (H :: Gamma) object
    (andLeft hh) (andLeft (andRight hh)) (andRight (andRight hh))
  exact ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralTypeInductionProof
