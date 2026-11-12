module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomFreshZeroBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomEndpointProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open UniformCertificateCompletion
theorem atType (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT typ : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam)))
 (hstep : Nonempty (Derivation body Delta (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
 (hext : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)))
 (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)))
 (hes : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s)))
 (het : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))
 (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s))) :
 Nonempty (Derivation body Delta (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) erasedS newParam ⊓ OriginalTransparentDirectBottomDichotomy.Result (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) erasedS erasedT newParam)) := by
 have hi := hext
 have sourceE := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta H G
  M W s erasedS d cutoff gamma extended c oldParam newParam hi hes hp hnp hs
 have bottom := OriginalMixedDirectBottomEndpointProof.endpoint H G M W oldStep s t cert oldParam typ hc ht hstep
 have bottomE := OriginalTransparentDirectBottomFreshZeroBottomProof.eraseBottom t erasedT typ d cutoff bottom het
 have typeE := OriginalPackedApplicationErasureProof.eraseTypeCopy s erasedS typ d cutoff ht hes
 obtain ⟨hd⟩ := OriginalTransparentDirectBottomDichotomyProof.assemble
  (OriginalTransparentMixedDirectBottom.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (OriginalTransparentMixedDirectBottomProof.actualIntroduction H G M W oldStep) body alpha Delta erasedS erasedT newParam typ
 obtain ⟨hprem⟩ := andIntro sourceE (andIntro typeE bottomE)
 exact andIntro sourceE ⟨Derivation.implicationElimination hd hprem⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureCoreProof
