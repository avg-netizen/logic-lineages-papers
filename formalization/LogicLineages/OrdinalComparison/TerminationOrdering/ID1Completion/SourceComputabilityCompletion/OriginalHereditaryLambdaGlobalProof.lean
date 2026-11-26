module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalPreparationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralComputabilityGlobalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalProof
open UniformCertificateCompletion OriginalHereditaryLambdaGlobal

/-- Rebuild the complete previous per-tuple conjunction at an arbitrary
calibrated original input. No graph or source law is transported by numerical
equality: each is supplied by its accepted generic original constructor. -/
theorem retainedProperties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    OriginalChildCertificateGlobal.RetainedProperties n arity p := by
  let q := OriginalSpineGuardLeaf.refineInputs p
  have hq : GlobalSourcePackage.InputsCalibrated n arity q :=
    OriginalSpineGuardLeafProof.refinedInputsCalibrated n arity p hp
  refine ⟨hp,?_,hq,
    OriginalObjectApplicationSpineGlobalPropertiesProof.properties n arity q hq,
    OriginalSelectedStepSpineProof.actualOriginalFinalRawStepSpineGuard p⟩
  exact OriginalSpineGuardLeafEvaluationProof.actualOriginalSpineGuardLeafRefinementEquality
    n arity p.oldStep hp.2.2.2.2.1

/-- Specialize the unconditional internal wrapper theorem by the literal
AST identity, not by all-input numerical calibration. -/
theorem finalChildElimination (p : GlobalSourcePackage.Inputs) :
    OriginalHereditaryLambda.InternalChildElimination (finalInputs p).oldStep := by
  rw [(OriginalHereditaryLambdaGlobalPreparationProof.pipelineIdentities p).2.2]
  exact OriginalHereditaryLambdaGlobalInternalProof.actualOriginalHereditaryLambdaGlobalInternalClosure
    (endpoint p) p.window p.oldStep

/-- Native preparation and all accepted generic consumers meet at exactly
prepareInputs p. Thus every old source/computability law and the new child
supplier refer to the SAME actual final tuple, selected before all contexts. -/
theorem properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (hp : GlobalSourcePackage.InputsCalibrated n arity p) :
    Properties n arity p := by
  have hprepared := OriginalHereditaryLambdaGlobalPreparationProof.prepareInputsCalibrated
    n arity p hp
  exact ⟨OriginalHereditaryLambdaGlobalPreparationProof.nativePreparation n arity p hp,
    retainedProperties n arity (prepareInputs p) hprepared,
    OriginalChildCertificateGlobalProof.certificateProperties (prepareInputs p),
    OriginalNeutralComputabilityGlobalProof.properties n arity (prepareInputs p) hprepared,
    finalChildElimination p⟩

/-- Select the original input only once. The full prior package and all
original certificate/neutral/variable consumers coexist with effective-leaf
hereditary closure; no ordinary or quotient body-edge oracle is introduced. -/
theorem actualOriginalHereditaryLambdaGlobalSelection :
    OriginalHereditaryLambdaGlobalTargets.ActualOriginalHereditaryLambdaGlobalSelection := by
  intro n arity
  obtain ⟨p,hp⟩ := GlobalSourcePackageProof.actualOriginalGlobalInputSelection n arity
  exact ⟨p,hp,properties n arity p hp⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalProof
