module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceInductionRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportAssemblyProof
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
open OriginalMixedClosedTraceInductionDefinitions
open OriginalMixedClosedTraceInductionSyntaxProof
open OriginalMixedClosedTraceInductionBindingProof
/-- Endpoint extraction only; the complete internal rows are an explicit
proof supplier until the concrete cons step is assembled. -/
theorem fromRows
 (rows : ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4) (window : Program 1)
  (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (path : OTerm alpha),
  Nonempty (Derivation body Delta
   (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
    (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path))) :
 OriginalMixedClosedTraceTargets.ActualClosedRestrictedTransport := by
 intro H G M W oldStep window body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentMixedDirectBottom.source H G M W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (numeral 1) s t cert oldParam ⊓ (graph4 (OriginalMixedDirectBottomTrace.recognizes (OriginalTransparentMixedDirectBottom.source H G M W) (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)) (numeral 1) s t cert oldParam ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have result : Nonempty (Derivation body (A :: Delta)
  (OriginalMixedClosedTraceInductionDefinitions.result
   (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) s t newParam erasedS erasedT)) := by
  apply programCases InternalUnpair.left (Fin.cons cert Fin.elim0) _
  intro beta rho Theta path hrho hp
  simp only [consTermRename,emptyRename] at hp
  rw [OriginalMixedClosedTraceInductionSyntaxProof.resultRename]
  have h' := renameInto h rho Theta hrho
  simp only [A,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,
   OriginalContextInsertionSyntaxProof.insertRename,GuardedSourceSyntaxProof.numeralRename] at h'
  exact atPathApply (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) (OriginalMixedClosedTraceDefinitions.checker H G M W oldStep window) path
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (oldParam.relabel rho) (newParam.relabel rho)
   (gamma.relabel rho) (extended.relabel rho) (d.relabel rho) (cutoff.relabel rho) (c.relabel rho)
   (erasedS.relabel rho) (erasedT.relabel rho) (rows H G M W oldStep window body beta Theta path) (andIntro hp h')
 obtain ⟨result⟩ := result
 exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceTransportAssemblyProof
