module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomRankedCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultFixedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomRankedErasureProof
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
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
theorem exactRankedErasure : OriginalMixedClosedBottomErasureTargets.ActualRankedErasure := by
 intro H G M W oldStep window body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 let leaf := OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window
 obtain ⟨he⟩ := OriginalMixedClosedBottomErasureProof.exactErasure H G M W oldStep window body alpha (A :: Delta)
  s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 obtain ⟨ha⟩ := h
 have er := (show Nonempty (Derivation body (A :: Delta) _) from ⟨Derivation.implicationElimination he ha⟩)
 have sourceE := andLeft er
 have dichotomy := andRight er
 obtain ⟨hr⟩ := OriginalMixedDirectBottomRankedCollapseProof.exactRankedCollapse H G M W oldStep body alpha (A :: Delta)
  s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 have rankLaw := Derivation.implicationElimination hr ha
 let E : Formula alpha := equal erasedS erasedT
 let C : Formula alpha := OriginalTransparentDirectBottomDichotomy.Witness leaf erasedS erasedT newParam
 let R : Formula alpha := OriginalExistentialRankResultDefinitions.Result leaf erasedS erasedT newParam s t
 have hy : Nonempty (Derivation body (E :: A :: Delta) R) := by
  have eq : Derivation body (E :: A :: Delta) E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨law⟩ := withHyp ⟨rankLaw⟩ E
  have hrank := OriginalExistentialRankResultSyntaxProof.rankIntro s t (numeral 1) (numeral 0)
   ⟨Derivation.implicationElimination law eq⟩
  obtain ⟨pair⟩ := andIntro ⟨eq⟩ hrank
  exact ⟨orLeft pair⟩
 have hn : Nonempty (Derivation body (C :: A :: Delta) R) := by
  have hc : Nonempty (Derivation body (C :: A :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨w⟩ := OriginalTransparentDirectBottomRankWitnessProof.forgetExactCode leaf erasedS erasedT newParam hc
  exact ⟨orRight w⟩
 obtain ⟨hd⟩ := dichotomy
 obtain ⟨hy⟩ := hy
 obtain ⟨hn⟩ := hn
 have result : Nonempty (Derivation body (A :: Delta) R) :=
  ⟨InternalBetaTotalityProof.disjunctionElimination hd (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩
 obtain ⟨result⟩ := andIntro sourceE result
 exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomRankedErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomRankedErasureProof
