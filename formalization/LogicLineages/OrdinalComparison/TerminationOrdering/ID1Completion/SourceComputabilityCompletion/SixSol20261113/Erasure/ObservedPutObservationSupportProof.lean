module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverRangeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalTypedDecoderTransportLogicalProof (iffBackward)
open OriginalPositionStructuralKeyObserverWiringProof
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion ObservedPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem commonOutputIff {n : Nat} (program : Program n) (common wanted : OTerm alpha)
    (xs ys : Fin n → OTerm alpha)
    (hx : Nonempty (Derivation body Delta (programGraph program common xs)))
    (hy : Nonempty (Derivation body Delta (programGraph program common ys))) :
    Nonempty (Derivation body Delta ((programGraph program wanted xs).iff (programGraph program wanted ys))) := by
  let A := programGraph program wanted xs
  let B := programGraph program wanted ys
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := outputTransport program common wanted ys
    (valueUnique program common wanted xs (withHyp hx A) ha) (withHyp hy A)
  obtain ⟨backward⟩ := outputTransport program common wanted xs
    (valueUnique program common wanted ys (withHyp hy B) hb) (withHyp hx B)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem atValues (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (input out typ parameter newParam context extended gamma d cutoff erasedInput erasedOut
      keyValue rank oldKey oldRank newKey newRank mark : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalFunctionNeutrality.windowGraph (finalInputs p H G W P).window input parameter ⊓
      (InternalParameterizedCanonicalResultFold.sourcePremises (finalData p H G W P) input typ parameter ⊓
        InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) out input parameter))))
    (hrange : Nonempty (Derivation body Delta (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context extended)))
    (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff extended)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt gamma cutoff extended)))
    (hei : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedInput d cutoff input)))
    (heo : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedOut d cutoff out)))
    (hki : Nonempty (Derivation body Delta (graph2 (key p H G W) oldKey erasedInput newParam)))
    (hri : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw oldRank erasedInput)))
    (hko : Nonempty (Derivation body Delta (graph2 (key p H G W) newKey erasedOut newParam)))
    (hro : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw newRank erasedOut)))
    (hm : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mark oldKey oldRank))) :
    Nonempty (Derivation body Delta
      (((graph2 (key p H G W) keyValue erasedInput newParam).iff
        (graph2 (key p H G W) keyValue erasedOut newParam)) ⊓
        ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedInput).iff
          (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut)))) := by
  let K := key p H G W
  have oldObservation := positionBackward K cutoff input parameter context extended d gamma
    erasedInput newParam oldKey oldRank mark hp hl hd hei hnp hki hri hm
  obtain ⟨rule⟩ := OriginalAllPositionStructuralTraversalProof.actualFinal
    (prepared p H G W) H G W P body alpha Delta out input typ parameter mark cutoff
  obtain ⟨args⟩ := andIntro hf hrange
  have comparison := Nonempty.intro (Derivation.implicationElimination rule args)
  have newObservation := iffBackward comparison oldObservation
  have newPair := positionForward K cutoff out parameter context extended d gamma
    erasedOut newParam newKey newRank mark hp hl hd heo hnp hko hro newObservation
  have shared := OriginalPositionStructuralKeyApplicationCoreProof.sharedPairValues K mark
    oldKey oldRank newKey newRank erasedOut newParam hm newPair hko hro
  exact andIntro
    (commonOutputIff K oldKey keyValue ![erasedInput,newParam] ![erasedOut,newParam] hki shared.1)
    (commonOutputIff OriginalRawSyntaxTransport.variableRankPackedRaw oldRank rank
      (Fin.cons erasedInput Fin.elim0) (Fin.cons erasedOut Fin.elim0) hri shared.2)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationSupportProof
