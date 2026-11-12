module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalFoldInductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceApplicationInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityClosure
open InternalOriginalUniformDescentSelection (Data)
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open OriginalTransparentDecoderValidatorCollapseInductionBindingProof
open OriginalStructuralKeyActivationSourceApplicationProof
open OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
open OriginalTransparentDecoderValidatorCollapseOpeningProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentLambdaValidity OriginalTransparentDecoderValidatorCollapse
open SourceComputabilityFormulaSupportProof (numeral)
open InternalSquareRootArithmeticSupportProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem applicationAtChildren (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (arrow d e fp ap fn arg packed parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d e fp ap fn arg packed)))
    (hfn : Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource fn parameter)))
    (harg : Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource arg parameter))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource packed parameter)) := by
  apply packedCases packed parameter
  intro beta j Delta _ _ c gamma hj _ hparameter
  rw [acceptanceRename]
  have hc' := renameInto hc j Delta hj
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
  have hf' := renameInto hfn j Delta hj
  have ha' := renameInto harg j Delta hj
  rw [acceptanceRename] at hf' ha'
  apply applicationCoordinatesCases (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fp.relabel j) (ap.relabel j) (fn.relabel j) (arg.relabel j) (packed.relabel j) _ hc'
  intro gamma' k Theta raw middle hk hp ht hb
  rw [acceptanceRename]
  have hc'' := renameInto hc' k Theta hk
  simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc''
  have hf'' := renameInto hf' k Theta hk
  have ha'' := renameInto ha' k Theta hk
  rw [acceptanceRename] at hf'' ha''
  have hparameter' := renameInto hparameter k Theta hk
  rw [OriginalTypedDecoderInternalScalarSyntaxProof.stepPairRename] at hparameter'
  exact sourceApplicationAt p H G W ((packed.relabel j).relabel k)
    ((parameter.relabel j).relabel k) ((e.relabel j).relabel k) raw middle
    ((d.relabel j).relabel k) ((fp.relabel j).relabel k) ((ap.relabel j).relabel k)
    ((arrow.relabel j).relabel k) ((fn.relabel j).relabel k) ((arg.relabel j).relabel k)
    (c.relabel k) (gamma.relabel k) hp ht hb hc'' hparameter' hf'' ha''


/-- Each child uses its own original payload, with all types and parameters
instantiated afresh. The original parent selector aligns both strict bounds. -/
theorem applicationByInduction (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (payload raw parameter : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma
      (belowPayload (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource payload)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (OriginalTransparentLambdaValidityInternal.TagIs 2 raw))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource raw parameter)) := by
  apply applicationTagCases raw parameter _ ht
  intro beta j Delta parentPayload arrow d e fp ap fn arg hj hc hparent hfn harg hfp hap
  rw [acceptanceRename]
  have hind' := renameInto hind j Delta hj
  rw [belowPayloadRename] at hind'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  obtain ⟨he⟩ := valueUnique InternalUnpair.right parentPayload (payload.relabel j)
    (Fin.cons (raw.relabel j) Fin.elim0) hparent hp'
  obtain ⟨hfp⟩ := hfp
  obtain ⟨hap⟩ := hap
  have hfi := belowPayloadApply (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource
    (payload.relabel j) fp fn (parameter.relabel j) hind' ⟨orderRight fp he hfp⟩ hfn
  have hai := belowPayloadApply (sourceValidator (transparent p H G W).base) (transparent p H G W).base.oldSource
    (payload.relabel j) ap arg (parameter.relabel j) hind' ⟨orderRight ap he hap⟩ harg
  exact applicationAtChildren p H G W arrow d e fp ap fn arg (raw.relabel j)
    (parameter.relabel j) hc hfi hai

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceApplicationInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyActivationSourceApplicationInductionProof
