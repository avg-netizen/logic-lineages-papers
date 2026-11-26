module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureProof
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
theorem resultRename {beta : Type} (leaf : Program 4) (s t parameter : OTerm alpha) (rho : alpha → beta) :
 (OriginalTransparentDirectBottomDichotomy.Result leaf s t parameter).relabel rho =
 OriginalTransparentDirectBottomDichotomy.Result leaf (s.relabel rho) (t.relabel rho) (parameter.relabel rho) := by
 change ((equal s t).relabel rho ⊔ (OriginalTransparentDirectBottomDichotomy.Witness leaf s t parameter).relabel rho) = _
 rw [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,OriginalTransparentDirectBottomDichotomySyntaxProof.witnessRename]
 rfl

theorem exactErasure : OriginalMixedClosedBottomErasureTargets.ActualErasure := by
 intro H G M W oldStep window body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have result : Nonempty (Derivation body (A :: Delta) (graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) erasedS newParam ⊓ OriginalTransparentDirectBottomDichotomy.Result (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) erasedS erasedT newParam)) := by
  apply programCases InternalUnpair.left (Fin.cons s Fin.elim0) _
  intro beta rho Theta typ hrho ht
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,InternalControlGraphSupportProof.emptyRename] at ht
  simp only [InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,resultRename]
  have h' := renameInto h rho Theta hrho
  simp only [A,InternalRecursionGraphStepSyntaxProof.conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,OriginalContextInsertionSyntaxProof.insertRename,GuardedSourceSyntaxProof.numeralRename] at h'
  exact OriginalMixedClosedBottomErasureCoreProof.atType H G M W oldStep window (s.relabel rho) (t.relabel rho) (cert.relabel rho) (oldParam.relabel rho) (newParam.relabel rho) (gamma.relabel rho) (extended.relabel rho) (d.relabel rho) (cutoff.relabel rho) (c.relabel rho) (erasedS.relabel rho) (erasedT.relabel rho) typ
   (andLeft h') (andLeft (andRight h')) (andLeft (andRight (andRight h'))) (andLeft (andRight (andRight (andRight h')))) (andLeft (andRight (andRight (andRight (andRight h'))))) (andLeft (andRight (andRight (andRight (andRight (andRight h')))))) (andLeft (andRight (andRight (andRight (andRight (andRight (andRight h'))))))) (andRight (andRight (andRight (andRight (andRight (andRight (andRight h'))))))) ht
 obtain ⟨result⟩ := result
 exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedBottomErasureProof
