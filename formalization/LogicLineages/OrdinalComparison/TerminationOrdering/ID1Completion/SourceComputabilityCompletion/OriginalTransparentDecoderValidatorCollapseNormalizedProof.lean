module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedOtherProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalBetaTotalityProof (disjunctionElimination)
open InternalControlGraphChoiceProof (excludedMiddle)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof (stepPairRename)
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalTransparentLambdaValidityInternal (TagIs)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalTypedDecoderTransportLogicalProof (iffRename notRename)
open OriginalTransparentDecoderValidatorCollapseNormalizedSupportProof
open OriginalTransparentDecoderValidatorCollapseNormalizedOtherProof
open OriginalTransparentDecoderValidatorCollapseNormalizedVariableProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentDecoderValidatorCollapsePackedImplicationProof (sourceToTarget)
open OriginalTransparentDecoderValidatorCollapse
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original guarded source supplies the original target internally.
No native reconstruction or calibration supplies this implication. -/
theorem sourceConjunctionAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter ⊓
        graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  let S := graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter
  let T := graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter
  have hs : Nonempty (Derivation body (S :: Gamma) S) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ht⟩ := sourceToTarget H G (InternalOriginalUniformContextMembership.contextMember p.base.member)
    W packed parameter hs
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (show Derivation body (S ⊓ T :: Gamma) (S ⊓ T) from Derivation.hypothesis List.mem_cons_self)))
    (Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
      (Derivation.hypothesis List.mem_cons_self) ht))⟩

theorem normalizedTargetAtCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
        (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter))) := by
  let V := TagIs 0 packed
  let A := (graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
    (numeral 1) packed parameter).iff
    (graph2 (transparent p H G W).base.oldTarget (numeral 1) packed parameter)
  have hy : Nonempty (Derivation body (V :: Gamma) A) :=
    targetVariableAt p H G W packed parameter typ raw c gamma
      (addAssumption hp V) (addAssumption hc V) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hno : Nonempty (Derivation body (V.not :: Gamma) A) := by
    have hn : Nonempty (Derivation body (V.not :: Gamma) V.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply programCases InternalPairing.pairing (Fin.cons c (Fin.cons z Fin.elim0)) _
    intro beta j Theta contextOnly hj hz
    have hp' := renameInto (addAssumption hp V.not) j Theta hj
    have hc' := renameInto (addAssumption hc V.not) j Theta hj
    have hn' := renameInto hn j Theta hj
    simp only [stepPairRename] at hp' hc'
    simp only [V,notRename,TagIs,graph1Rename,numeralRename] at hn'
    simp only [consTermRename,emptyRename,zRelabel] at hz
    simp only [A,iffRename,graph2Rename,numeralRename]
    exact targetNonvariableAt p H G W (packed.relabel j) (parameter.relabel j)
      (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) contextOnly hp' hc' hz hn'
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle V)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

theorem normalizedCoupledAtCoordinates (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hc : Nonempty (Derivation body Gamma (StepPair parameter c gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
          (numeral 1) packed parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
          (numeral 1) packed parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter))) := by
  let V := TagIs 0 packed
  let A := (graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
      (numeral 1) packed parameter ⊓
    graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
      (numeral 1) packed parameter).iff
    (graph2 (transparent p H G W).base.oldSource (numeral 1) packed parameter)
  have hy : Nonempty (Derivation body (V :: Gamma) A) :=
    coupledVariableAt p H G W packed parameter typ raw c gamma
      (addAssumption hp V) (addAssumption hc V) ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hno : Nonempty (Derivation body (V.not :: Gamma) A) := by
    have hn : Nonempty (Derivation body (V.not :: Gamma) V.not) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply programCases InternalPairing.pairing (Fin.cons c (Fin.cons z Fin.elim0)) _
    intro beta j Theta contextOnly hj hz
    have hp' := renameInto (addAssumption hp V.not) j Theta hj
    have hc' := renameInto (addAssumption hc V.not) j Theta hj
    have hn' := renameInto hn j Theta hj
    simp only [stepPairRename] at hp' hc'
    simp only [V,notRename,TagIs,graph1Rename,numeralRename] at hn'
    simp only [consTermRename,emptyRename,zRelabel] at hz
    simp only [A,iffRename,conjunctionRename,graph2Rename,numeralRename]
    exact iffCompose
      (andIff (sourceNonvariableAt p H G W (packed.relabel j) (parameter.relabel j)
        (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) contextOnly hp' hc' hz hn')
        (targetNonvariableAt p H G W (packed.relabel j) (parameter.relabel j)
          (typ.relabel j) (raw.relabel j) (c.relabel j) (gamma.relabel j) contextOnly hp' hc' hz hn'))
      (sourceConjunctionAt p H G W (packed.relabel j) (parameter.relabel j))
  obtain ⟨hy⟩ := hy
  obtain ⟨hno⟩ := hno
  exact ⟨disjunctionElimination (excludedMiddle V)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hno)⟩

/-- Unrestricted original normalized target acceptance, with no extra window,
calibration, successful run or syntactic well-formedness assumption. -/
theorem normalizedTargetAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
        (numeral 1) raw parameter).iff
        (graph2 (transparent p H G W).base.oldTarget (numeral 1) raw parameter))) := by
  apply packedCases raw parameter _
  intro beta j Theta typ payload c gamma hj hp hc
  simp only [iffRename,graph2Rename,numeralRename]
  exact normalizedTargetAtCoordinates p H G W (raw.relabel j) (parameter.relabel j)
    typ payload c gamma hp hc

/-- The preserved invariant is the coupled source AND target acceptance.
The source variable branch alone deliberately does not carry G. -/
theorem normalizedCoupledAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldSource
          (numeral 1) raw parameter ⊓
        graph2 (OriginalHereditaryValidity.normalizedData (refined p H G W).base).oldTarget
          (numeral 1) raw parameter).iff
        (graph2 (transparent p H G W).base.oldSource (numeral 1) raw parameter))) := by
  apply packedCases raw parameter _
  intro beta j Theta typ payload c gamma hj hp hc
  simp only [iffRename,conjunctionRename,graph2Rename,numeralRename]
  exact normalizedCoupledAtCoordinates p H G W (raw.relabel j) (parameter.relabel j)
    typ payload c gamma hp hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseNormalizedProof
