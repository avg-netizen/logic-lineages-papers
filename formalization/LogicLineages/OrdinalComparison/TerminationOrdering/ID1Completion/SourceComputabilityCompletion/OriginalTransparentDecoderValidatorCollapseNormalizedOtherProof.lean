module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedOtherProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalBetaTotalityProof (disjunctionElimination)
open InternalControlGraphChoiceProof (excludedMiddle)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTransparentLambdaValidityInternalBottomShapeProof (bottomTag)
open OriginalTransparentLambdaValidityInternalNormalizationSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedBottomProof
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Away from the actual variable tag, the sole old target branch is
preserved. Exact bottom removes Gamma only where its own recurrence pays it. -/
theorem targetNonvariableAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hz : Nonempty (Derivation body Gamma (StepPair contextOnly c z)))
    (hn : Nonempty (Derivation body Gamma (TagIs 0 packed).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter))) := by
  let r := refined p H G W
  let B := BottomRepresentative.bottomGraph (numeral 1) packed
  let A := graph2 (OriginalHereditaryValidity.normalizedData r.base).oldTarget (numeral 1) packed parameter
  let T := graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter
  have hy : Nonempty (Derivation body (B :: Gamma) (A.iff T)) := by
    have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact iffCompose
      (normalizationAtBottom r.base.oldTarget (numeral 1) packed parameter c gamma contextOnly
        (addAssumption hc B) (addAssumption hz B) hb)
      (iffCompose
        (variableBranchOff (transparent p H G W).base.oldTarget (OriginalVariableLeaves.targetVariable G)
          (numeral 1) packed contextOnly (addAssumption hn B))
        (iffReverse (targetBottomAt H G packed parameter contextOnly typ raw c gamma z
          (addAssumption hp B) (addAssumption hc B) (addAssumption hz B) (bottomTag packed hb))))
  have hno : Nonempty (Derivation body (B.not :: Gamma) (A.iff T)) :=
    iffCompose (normalizationOffBottom r.base.oldTarget (numeral 1) packed parameter
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (variableBranchOff (transparent p H G W).base.oldTarget (OriginalVariableLeaves.targetVariable G)
        (numeral 1) packed parameter (addAssumption hn B.not))
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle B)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

/-- Source normalization likewise preserves its exact nonvariable branch,
including both original guards and every rejected malformed bottom. -/
theorem sourceNonvariableAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hz : Nonempty (Derivation body Gamma (StepPair contextOnly c z)))
    (hn : Nonempty (Derivation body Gamma (TagIs 0 packed).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  let r := refined p H G W
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  let B := BottomRepresentative.bottomGraph (numeral 1) packed
  let A := graph2 (OriginalHereditaryValidity.normalizedData r.base).oldSource (numeral 1) packed parameter
  let S := graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter
  have hy : Nonempty (Derivation body (B :: Gamma) (A.iff S)) := by
    have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact iffCompose
      (normalizationAtBottom r.base.oldSource (numeral 1) packed parameter c gamma contextOnly
        (addAssumption hc B) (addAssumption hz B) hb)
      (iffCompose
        (variableBranchOff (transparent p H G W).base.oldSource (OriginalVariableLeaves.sourceVariable p.base.member)
          (numeral 1) packed contextOnly (addAssumption hn B))
        (iffReverse (sourceBottomAt H G M W packed parameter contextOnly typ raw c gamma z
          (addAssumption hp B) (addAssumption hc B) (addAssumption hz B) (bottomTag packed hb))))
  have hno : Nonempty (Derivation body (B.not :: Gamma) (A.iff S)) :=
    iffCompose (normalizationOffBottom r.base.oldSource (numeral 1) packed parameter
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
      (variableBranchOff (transparent p H G W).base.oldSource (OriginalVariableLeaves.sourceVariable p.base.member)
        (numeral 1) packed parameter (addAssumption hn B.not))
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle B)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedOtherProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedOtherProof
