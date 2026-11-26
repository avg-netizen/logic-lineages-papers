module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyObserverWiringProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralTraversalKeyConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalStructuralClassKeyDefinitions OriginalStructuralClassKeyActiveProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open UniformCertificateCompletion
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Two actual paired marks force the SAME key and rank on the second
child. This is original graph functionality, not class covariance. -/
theorem sharedPairValues (R : Program 2) (mark firstKey firstRank secondKey secondRank value parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark firstKey firstRank)))
 (hq : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark secondKey secondRank)))
 (hk : Nonempty (Derivation body Delta (graph2 R secondKey value parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw secondRank value))) :
 Nonempty (Derivation body Delta (graph2 R firstKey value parameter)) ∧
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw firstRank value)) := by
 have hek := valueUnique InternalUnpair.left secondKey firstKey (Fin.cons mark Fin.elim0)
   (pairLeft mark secondKey secondRank hq) (pairLeft mark firstKey firstRank hp)
 have her := valueUnique InternalUnpair.right secondRank firstRank (Fin.cons mark Fin.elim0)
   (pairRight mark secondKey secondRank hq) (pairRight mark firstKey firstRank hp)
 exact ⟨outputTransport R secondKey firstKey (Fin.cons value (Fin.cons parameter Fin.elim0)) hek hk,
   outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw secondRank firstRank (Fin.cons value Fin.elim0) her hr⟩

theorem sharedApplicationRank (input out d e fn arg fnOut argOut fRank aRank rank : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)))
 (hfr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw fRank fn)))
 (hfor : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw fRank fnOut)))
 (har : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw aRank arg)))
 (haor : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw aRank argOut)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out))) :
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)) := by
 apply programCases InternalArithmeticPrograms.addition (Fin.cons fRank (Fin.cons aRank Fin.elim0)) _
 intro beta j Theta sum hj hadd
 rw [graph1Rename]
 simp only [consTermRename,emptyRename] at hadd
 have hi' := renameInto hi j Theta hj
 have ho' := renameInto ho j Theta hj
 rw [graph4Rename] at hi' ho'
 have hfr' := renameInto hfr j Theta hj
 have hfor' := renameInto hfor j Theta hj
 have har' := renameInto har j Theta hj
 have haor' := renameInto haor j Theta hj
 have hr' := renameInto hr j Theta hj
 rw [graph1Rename] at hfr' hfor' har' haor' hr'
 have ri := OriginalFinalGuardedRankConstructorProof.applicationValue
   (input.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
   (fRank.relabel j) (aRank.relabel j) sum hi' hfr' har' hadd
 have ro := OriginalFinalGuardedRankConstructorProof.applicationValue
   (out.relabel j) (d.relabel j) (e.relabel j) (fnOut.relabel j) (argOut.relabel j)
   (fRank.relabel j) (aRank.relabel j) sum ho' hfor' haor' hadd
 have he := valueUnique OriginalRawSyntaxTransport.variableRankPackedRaw sum (rank.relabel j)
   (Fin.cons (out.relabel j) Fin.elim0) ro hr'
 exact outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw sum (rank.relabel j)
   (Fin.cons (input.relabel j) Fin.elim0) he ri

/-- Congruence is applied only AFTER erasure, at one actual shared deleted
parameter. All child key/rank outputs are actual graphs, not a covariance
premise between contexts. -/
theorem applicationAtErased (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out d e fn arg fnOut argOut fKey aKey fRank aRank keyValue rank parameter : OTerm alpha)
 (hai : Nonempty (Derivation body Delta (Active p H G W input parameter)))
 (hao : Nonempty (Derivation body Delta (Active p H G W out parameter)))
 (haf : Nonempty (Derivation body Delta (Active p H G W fn parameter)))
 (hafo : Nonempty (Derivation body Delta (Active p H G W fnOut parameter)))
 (haa : Nonempty (Derivation body Delta (Active p H G W arg parameter)))
 (haao : Nonempty (Derivation body Delta (Active p H G W argOut parameter)))
 (hfi : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields input d e fn arg)))
 (hfo : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.ApplicationFields out d e fnOut argOut)))
 (hi : Nonempty (Derivation body Delta (graph4 application input d e fn arg)))
 (ho : Nonempty (Derivation body Delta (graph4 application out d e fnOut argOut)))
 (hkf : Nonempty (Derivation body Delta (graph2 (key p H G W) fKey fn parameter)))
 (hkfo : Nonempty (Derivation body Delta (graph2 (key p H G W) fKey fnOut parameter)))
 (hka : Nonempty (Derivation body Delta (graph2 (key p H G W) aKey arg parameter)))
 (hkao : Nonempty (Derivation body Delta (graph2 (key p H G W) aKey argOut parameter)))
 (hrf : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw fRank fn)))
 (hrfo : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw fRank fnOut)))
 (hra : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw aRank arg)))
 (hrao : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw aRank argOut)))
 (hk : Nonempty (Derivation body Delta (graph2 (key p H G W) keyValue out parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out))) :
 Nonempty (Derivation body Delta (graph2 (key p H G W) keyValue input parameter)) ∧
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)) := by
 have keyLaw := OriginalStructuralTraversalKeyConstructorProof.applicationAtCoreValues p H G W
   input out d e fn arg fnOut argOut fKey aKey parameter keyValue hai hao hfi hfo
   (keyToCore p H G W fn fKey parameter haf hkf)
   (keyToCore p H G W fnOut fKey parameter hafo hkfo)
   (keyToCore p H G W arg aKey parameter haa hka)
   (keyToCore p H G W argOut aKey parameter haao hkao)
 exact ⟨iffForward keyLaw hk, sharedApplicationRank input out d e fn arg fnOut argOut fRank aRank rank
   hi ho hrf hrfo hra hrao hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
