module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedErasureProof
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
theorem exactRankedErasure : OriginalTransparentDirectBottomRankedErasureTargets.ActualRankedErasure := by
 intro p H G W P body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 let leaf := (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep
 obtain ⟨he⟩ := OriginalTransparentDirectBottomErasureProof.exactErasure p H G W P body alpha (A :: Delta)
  s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 obtain ⟨ha⟩ := h
 have er := (show Nonempty (Derivation body (A :: Delta) _) from ⟨Derivation.implicationElimination he ha⟩)
 have sourceE := andLeft er
 have dichotomy := andRight er
 obtain ⟨hr⟩ := OriginalTransparentDirectBottomRankedCollapseProof.exactRankedCollapse p H G W P body alpha (A :: Delta)
  s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 have rankLaw := Derivation.implicationElimination hr ha
 let E : Formula alpha := equal erasedS erasedT
 let C : Formula alpha := OriginalTransparentDirectBottomDichotomy.Witness leaf erasedS erasedT newParam
 let R : Formula alpha := OriginalLambdaOriginalRankDefinitions.Result leaf erasedS erasedT newParam s t (numeral 1) (numeral 0)
 have hy : Nonempty (Derivation body (E :: A :: Delta) R) := by
  have eq : Derivation body (E :: A :: Delta) E := Derivation.hypothesis List.mem_cons_self
  obtain ⟨law⟩ := withHyp ⟨rankLaw⟩ E
  obtain ⟨pair⟩ := andIntro ⟨eq⟩ ⟨Derivation.implicationElimination law eq⟩
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedErasureProof
