module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootActivationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyPayloadDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootClosureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open UniformCertificateCompletion
open OriginalStructuralClassKeyDefinitions OriginalStructuralClassKeyActiveProof
open OriginalStructuralTraversalKeyConstructorProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem inputActive (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (OriginalLambdaTraversalOutput.premises (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
        (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window out input typ parameter))) :
    Nonempty (Derivation body Delta (Active p H G W input parameter)) :=
  ObservedRootActivationProof.activeFromSource p H G W P input parameter
    (andLeft hp) (andLeft (andLeft (andRight hp)))

theorem outputActive (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (out input typ parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta
      (OriginalLambdaTraversalOutput.premises (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
        (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window out input typ parameter))) :
    Nonempty (Derivation body Delta (Active p H G W out parameter)) := by
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  have hi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window out input typ parameter hp
  have hw := BottomDescentStepProof.windowChange r.window InternalOriginalStepGuard.one input out parameter (andLeft hp)
  exact ObservedRootActivationProof.activeFromSource p H G W P out parameter hw (andLeft hi)

theorem applicationClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    OriginalStructuralKeyPayloadDefinitions.ApplicationLaw (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
      (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window (key p H G W) := by
  intro body alpha Delta input out typ parameter arrow d e fn arg fnOut argOut fValue aValue mark
    hp hfp hap harrow hf hi ho hkf hkfo hka hkao
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  have hfi := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window fnOut fn arrow parameter hfp
  have hai := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window argOut arg d parameter hap
  have hfo := OriginalLambdaTraversalApplicationFieldsProof.fromRaw arrow d e fnOut argOut out
    harrow (andLeft (andRight hfi)) (andLeft (andRight hai)) ho
  have hcf := keyToCore p H G W fn fValue parameter (inputActive p H G W P fnOut fn arrow parameter hfp) hkf
  have hcfo := keyToCore p H G W fnOut fValue parameter (outputActive p H G W P fnOut fn arrow parameter hfp) hkfo
  have hca := keyToCore p H G W arg aValue parameter (inputActive p H G W P argOut arg d parameter hap) hka
  have hcao := keyToCore p H G W argOut aValue parameter (outputActive p H G W P argOut arg d parameter hap) hkao
  exact applicationAtCoreValues p H G W input out d e fn arg fnOut argOut fValue aValue parameter mark
    (inputActive p H G W P out input typ parameter hp)
    (outputActive p H G W P out input typ parameter hp) hf hfo hcf hcfo hca hcao

theorem lambdaClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    OriginalStructuralKeyPayloadDefinitions.LambdaLaw (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
      (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window (key p H G W) := by
  intro body alpha Delta input out typ parameter mark d e child childParameter childOut value
    hp hf hc hki hko
  let r := OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P
  have cp := OriginalLambdaTraversalLambdaOutputProof.childPremises r.base r.window
    input d e child typ parameter childParameter hf (andLeft hp) (andLeft (andRight hp))
  have childPremises := andIntro (andLeft cp) (andIntro (andRight cp) hc)
  have ci := OriginalLambdaTraversalOutputProof.invariantAtInput r.base r.window
    childOut child e childParameter childPremises
  have hctor := OriginalLambdaTraversalInternalLambdaProof.lambdaForward
    (OriginalLambdaTraversalSelection.leaf r.base r.window) input d e child parameter childParameter childOut out
    hf hc (andRight (andRight hp))
  have rebuilt := OriginalLambdaTraversalLambdaOutputProof.outputRebuild r.base r.window
    input out d e child childOut typ parameter childParameter hf (andLeft (andRight hp))
    (andIntro (andLeft ci) (andIntro (andLeft (andRight ci)) (andLeft (andRight (andRight ci))))) hctor
  have hfo := andRight (andRight (andRight rebuilt))
  have hcorei := keyToCore p H G W child value childParameter
    (inputActive p H G W P childOut child e childParameter childPremises) hki
  have hcoreo := keyToCore p H G W childOut value childParameter
    (outputActive p H G W P childOut child e childParameter childPremises) hko
  exact lambdaAtCoreValues p H G W input out d e child childOut value parameter childParameter mark
    (inputActive p H G W P out input typ parameter hp)
    (outputActive p H G W P out input typ parameter hp) hf hfo hcorei hcoreo

theorem otherClosure (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) :
    OriginalStructuralKeyPayloadDefinitions.OtherLaw (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).base
      (OriginalAllPositionStructuralTraversalDefinitions.refined p H G W P).window (key p H G W) := by
  intro body alpha Delta out input typ parameter mark hw hs ht hl
  obtain ⟨law⟩ := ObservedRootLeafProof.actualOriginalStructuralTraversalKeyOtherLeaf
    p H G W P body alpha Delta out input typ parameter mark
  obtain ⟨args⟩ := andIntro hw (andIntro hs (andIntro ht hl))
  exact ⟨Derivation.implicationElimination law args⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootClosureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedRootClosureProof
