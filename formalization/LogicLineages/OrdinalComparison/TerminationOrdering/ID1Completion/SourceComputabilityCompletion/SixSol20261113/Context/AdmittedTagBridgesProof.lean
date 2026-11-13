module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTagBridgesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalListCodecSupportProof (consGraphRename)
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof (termAcceptedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ChildContentDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem lambdaCase (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) row)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 1) raw)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.lambdaCases raw _ htag
  intro beta j Theta domain child hj hc
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hparameter' := renameInto hparameter j Theta hj
  have ha' := renameInto ha j Theta hj
  have harity' := renameInto harity j Theta hj
  have he' := renameInto he j Theta hj
  have hscan' := renameInto hscan j Theta hj
  have hm' := renameInto hm j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret'
  exact AdmittedLambdaProof.actual Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) domain child hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc

theorem applicationCase (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) row)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) raw)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  apply OriginalRawSyntaxTransportInternalParserBinaryProof.applicationCases raw _ htag
  intro beta j Theta domain child0 child1 hj hc
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hparameter' := renameInto hparameter j Theta hj
  have ha' := renameInto ha j Theta hj
  have harity' := renameInto harity j Theta hj
  have he' := renameInto he j Theta hj
  have hscan' := renameInto hscan j Theta hj
  have hm' := renameInto hm j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret'
  exact AdmittedApplicationProof.actual Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) domain child0 child1 hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc

theorem ordinaryCase (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) row)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 4) raw)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  apply OriginalRawSyntaxTransportInternalParserUnaryProof.ordinaryCases raw _ htag
  intro beta j Theta head base hj hc
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hparameter' := renameInto hparameter j Theta hj
  have ha' := renameInto ha j Theta hj
  have harity' := renameInto harity j Theta hj
  have he' := renameInto he j Theta hj
  have hscan' := renameInto hscan j Theta hj
  have hm' := renameInto hm j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret'
  exact AdmittedOrdinaryProof.actual Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) head base hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc

theorem numberedCase (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
    (hparameter : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (ha : Nonempty (Derivation body Delta (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W typ raw gamma c)))
    (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) childCount raw)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix childCount z typ raw jobs)))
    (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (observationFromJob Q)) row annotatedPrefix)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z row)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (numeral 1) row)))
    (hret : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) raw)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases raw _ htag
  intro beta j Theta label head encodedType base extraTypes extras hj hc
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hparameter' := renameInto hparameter j Theta hj
  have ha' := renameInto ha j Theta hj
  have harity' := renameInto harity j Theta hj
  have he' := renameInto he j Theta hj
  have hscan' := renameInto hscan j Theta hj
  have hm' := renameInto hm j Theta hj
  have hf' := renameInto hf j Theta hj
  have hs' := renameInto hs j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret'
  exact AdmittedNumberedProof.actual Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) label head encodedType base extraTypes extras hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTagBridgesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTagBridgesProof
