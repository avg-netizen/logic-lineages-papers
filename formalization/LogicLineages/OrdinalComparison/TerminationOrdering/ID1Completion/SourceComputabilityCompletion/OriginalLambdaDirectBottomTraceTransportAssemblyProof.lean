module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportAssemblyProof
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
open OriginalLambdaDirectBottomTraceInductionDefinitions
open OriginalLambdaDirectBottomTraceInductionSyntaxProof
open OriginalLambdaDirectBottomTraceInductionBindingProof
/-- Endpoint extraction only; the complete internal rows are an explicit
proof supplier until the concrete cons step is assembled. -/
theorem fromRows
 (rows : ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
  (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (path : OTerm alpha),
  Nonempty (Derivation body Delta
   (AtPath (OriginalTransparentDirectBottomGlobal.source p H G W)
    (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path))) :
 OriginalLambdaDirectBottomTraceTransportTargets.ActualRestrictedTransport := by
 intro p H G W P body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph4 (OriginalLambdaDirectBottomTrace.recognizes (OriginalTransparentDirectBottomGlobal.source p H G W) (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep) (numeral 1) s t cert oldParam ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have result : Nonempty (Derivation body (A :: Delta)
  (OriginalLambdaDirectBottomTraceInductionDefinitions.result
   (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep s t newParam erasedS erasedT)) := by
  apply programCases InternalUnpair.left (Fin.cons cert Fin.elim0) _
  intro beta rho Theta path hrho hp
  simp only [consTermRename,emptyRename] at hp
  rw [OriginalLambdaDirectBottomTraceInductionSyntaxProof.resultRename]
  have h' := renameInto h rho Theta hrho
  simp only [A,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,
   OriginalContextInsertionSyntaxProof.insertRename,GuardedSourceSyntaxProof.numeralRename] at h'
  exact atPathApply (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep path
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (oldParam.relabel rho) (newParam.relabel rho)
   (gamma.relabel rho) (extended.relabel rho) (d.relabel rho) (cutoff.relabel rho) (c.relabel rho)
   (erasedS.relabel rho) (erasedT.relabel rho) (rows p H G W P body beta Theta path) (andIntro hp h')
 obtain ⟨result⟩ := result
 exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTransportAssemblyProof
