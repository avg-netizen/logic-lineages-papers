module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityShapeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalComputabilityApplication InternalComputabilityDownward
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalApplicationComputability OriginalApplicationComputabilityTargets
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalFinalAcceptedOutputNonLambda :
    ActualOriginalFinalAcceptedOutputNonLambda := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS body alpha Gamma sigma tau function argument out
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let comp := GlobalSourcePackage.computability r
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  let H := domain comp context sigma tau function argument ⊓
    accepted comp sigma tau (numeral context) function argument out
  have hh : Nonempty (Derivation body (H :: Gamma) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have inputs := OriginalSourceNeutralApplicationProof.actualOriginalSourceNeutralApplicationInputs
    n arity q hq symbols S table hS
  have hn : Nonempty (Derivation body (H :: Gamma)
      (OriginalSourceNeutralApplication.nonLambdaObject out)) := by
    apply inputs body alpha (H :: Gamma) sigma tau function argument out
      (OriginalSourceNeutralApplication.nonLambdaObject out) (andLeft hh) (andRight hh)
    intro beta j Delta hj gammaCode fn arg value parameter hr
    rw [OriginalSourceNeutralApplicationSyntaxProof.nonLambdaObjectRename]
    exact OriginalApplicationComputabilityShapeProof.recoveredNonLambda q context sigma tau
      (function.relabel j) (argument.relabel j) (out.relabel j)
      gammaCode fn arg value parameter hr
  obtain ⟨hn⟩ := hn
  exact ⟨Derivation.implicationIntroduction hn⟩

theorem actualOriginalFinalAcceptedApplicationComputable :
    ActualOriginalFinalAcceptedApplicationComputable := by
  intro n arity p hp
  dsimp only
  intro symbols S table hS body alpha Gamma sigma tau function argument out
  let q := OriginalSpineGuardLeaf.refineInputs p
  let r := OriginalApplicationSidecar.finalInputs q
  let data := OuterSelection.data r.base r.window
  let comp := GlobalSourcePackage.computability r
  let context := OrdinaryArithmeticQuotient.contextCode symbols S table
  have hq := OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  have hr := OriginalApplicationComponentCoherenceGlobalInputProof.finalInputsCalibrated n arity q hq
  have hw := GlobalSourceSpineLeastProof.windowEvaluation n r.window hr.2.1 symbols S table hS
  let H := premises comp sigma tau (numeral context) function argument ⊓
    accepted comp sigma tau (numeral context) function argument out
  have hh : Nonempty (Derivation body (H :: Gamma) H) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hm := InternalComputabilityApplicationSourceProof.closedMetadata
    (body := body) (Gamma := H :: Gamma) r.window Outer.arrow context sigma tau hw
    (OuterArithmeticProof.arrowEvaluation sigma tau)
  obtain ⟨hc⟩ := InternalComputabilityApplicationProof.applicationComputability
    (Outer.baseComputability r.oldComp data r.window) r.window Outer.arrow
    (Outer.result r.oldComp data r.window r.oldVertex r.oldResult)
    sigma tau (numeral context) function argument out hm (andLeft hh) (andRight hh)
  exact ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationComputabilityProof
