module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomErasureCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedNonbottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankValuesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankInversionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseProof
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
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalPackedProof

theorem rankRename {beta : Type} (s t : OTerm alpha) (rho : alpha → beta) :
 (OriginalLambdaOriginalRankDefinitions.PackedRankDrop s t (numeral 1) (numeral 0)).relabel rho =
 OriginalLambdaOriginalRankDefinitions.PackedRankDrop (s.relabel rho) (t.relabel rho) (numeral 1) (numeral 0) := by
 simp only [OriginalLambdaOriginalRankDefinitions.PackedRankDrop,conjunctionRename,graph1Rename,InternalLessThan.strictLess,InternalOriginalOrderSyntaxProof.orderRename,GuardedSourceSyntaxProof.numeralRename]


theorem exactRankedCollapse : OriginalTransparentDirectBottomRankedCollapseTargets.ActualRankedCollapse := by
 intro p H G W P body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 let A : Formula alpha := graph2 (OriginalTransparentDirectBottomGlobal.source p H G W) (numeral 1) s oldParam ⊓ (graph4 (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep (numeral 1) s t cert oldParam ⊓ (graph1 OriginalTransparentDirectBottom.certificateCode cert s ⊓ (OriginalContextInsertion.Insert d cutoff gamma extended ⊓ (graph2 InternalPairing.pairing oldParam c extended ⊓ (graph2 InternalPairing.pairing newParam c gamma ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedS d cutoff s ⊓ (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedT d cutoff t)))))))
 let E : Formula alpha := equal erasedS erasedT
 have h : Nonempty (Derivation body (E :: A :: Delta) A) := ⟨Derivation.hypothesis (by simp)⟩
 have eq : Nonempty (Derivation body (E :: A :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have result : Nonempty (Derivation body (E :: A :: Delta)
   (OriginalLambdaOriginalRankDefinitions.PackedRankDrop s t (numeral 1) (numeral 0))) := by
  apply OriginalTransparentDirectBottomRankQueryProof.coordinates s d cutoff _
  intro beta rho Theta typ raw tag rawE bottomRaw hrho ht hr htag her hbraw
  rw [rankRename]
  have h' := renameInto h rho Theta hrho
  simp only [A,conjunctionRename,graph1Rename,graph2Rename,graph3Rename,graph4Rename,OriginalContextInsertionSyntaxProof.insertRename,GuardedSourceSyntaxProof.numeralRename] at h'
  have eq' := renameInto eq rho Theta hrho
  simp only [E,OriginalTypedDecoderInternalLogicSyntaxProof.equalRename] at eq'
  have hstep := andLeft (andRight h')
  have hc := andLeft (andRight (andRight h'))
  have hes := andLeft (andRight (andRight (andRight (andRight (andRight (andRight h'))))))
  have het := andRight (andRight (andRight (andRight (andRight (andRight (andRight h'))))))
  have bottom := OriginalTransparentDirectBottomFreshZeroEndpointProof.finalEndpoint p H G W P
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (oldParam.relabel rho) typ hc ht hstep
  have bottomE := OriginalTransparentDirectBottomFreshZeroBottomProof.eraseBottom
   (t.relabel rho) (erasedT.relabel rho) typ (d.relabel rho) (cutoff.relabel rho) bottom het
  have rev : Nonempty (Derivation body Theta (equal (erasedT.relabel rho) (erasedS.relabel rho))) := by
   obtain ⟨heq⟩ := eq'
   simpa only [equalEqn] using (show Nonempty (Derivation body Theta (InternalTagArithmeticSyntaxProof.eqn (erasedT.relabel rho) (erasedS.relabel rho))) from ⟨InternalTagArithmeticSupportProof.symm (by simpa only [equalEqn] using heq)⟩)
  have bottomS := outputTransport BottomRepresentative.bottomCode (erasedT.relabel rho) (erasedS.relabel rho)
   (Fin.cons typ Fin.elim0) (by simpa only [equalEqn] using rev) bottomE
  have pairS := reconstructPair (s.relabel rho) typ raw ht hr
  have pairE := erasePackedForward (s.relabel rho) (erasedS.relabel rho) typ raw rawE
   (d.relabel rho) (cutoff.relabel rho) pairS her hes
  have nonbottom := OriginalTransparentDirectBottomRankedNonbottomProof.finalNonbottom p H G W P
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (oldParam.relabel rho) hc hstep
  have zero := OriginalTransparentDirectBottomRankInversionProof.originalTagZero
   (s.relabel rho) (erasedS.relabel rho) typ raw rawE bottomRaw (d.relabel rho) (cutoff.relabel rho) tag
   pairS pairE bottomS hbraw htag her nonbottom
  exact OriginalTransparentDirectBottomRankValuesProof.packedRanks (s.relabel rho) (t.relabel rho) typ raw bottomRaw pairS zero bottom hbraw
 obtain ⟨result⟩ := result
 exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction result)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedCollapseProof
