module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedSubst)
open OriginalContextInsertionSyntaxProof (lengthSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open RankArgumentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeelSupportProof (andIntro)

theorem smallApply (observations bound count index typed typ child : OTerm alpha)
 (h : Nonempty (Derivation body Delta (AllSmall observations bound)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count observations)))
 (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup typed index observations)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child))) :
 Nonempty (Derivation body Delta (InternalLessThan.strictLess child bound)) := by
 have h := actualFiniteUniversalElimination body alpha 5 Delta (smallMatrix observations bound)
   (fun i => emb (![count,index,typed,typ,child] i)) h
 rw [RankArgumentSyntax.smallWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨args⟩ := andIntro hl (andIntro hi (andIntro hv hp))
 exact ⟨Derivation.implicationElimination h args⟩

theorem weightApply {k : Nat} (Q : Program 2) (F : Program (k+1))
 (H : Program 1) (M W : Program 2) (parameter gamma c bound : OTerm alpha) (params : Fin k → OTerm alpha)
 (typ raw packed child typed rank : OTerm alpha)
 (h : Nonempty (Derivation body Delta (LocalWeights Q F H M W parameter gamma c bound params)))
 (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hq : Nonempty (Derivation body Delta (graph2 Q child packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ child)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rank raw)))
 (hb : Nonempty (Derivation body Delta (InternalLessThan.strictLess child bound))) :
 Nonempty (Derivation body Delta (programGraph F rank (Fin.cons typed params))) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (weightMatrix Q F H M W parameter gamma c bound params)
   (fun i => emb (![typ,raw,packed,child,typed,rank] i)) h
 rw [RankArgumentSyntax.weightsWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨args⟩ := andIntro ha (andIntro hp (andIntro hq (andIntro ht (andIntro hr hb))))
 exact ⟨Derivation.implicationElimination h args⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankArgumentLocalProof
