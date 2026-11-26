module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedApplicationProof
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

theorem atArrow (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned domain child0 child1 fnType : OTerm alpha)
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
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain child0 child1)))
    (hfn : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode fnType domain typ)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  have haCount := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.applicationArity (.projection 0) raw domain child0 child1 (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hc
  have hp := AdmittedScanSlotsProof.countTransport childCount (numeral 2) z typ raw jobs annotatedPrefix harity haCount hscan
  apply AdmittedScanSlotsProof.binaryCases (observationFromJob Q) childCount z typ raw jobs annotatedPrefix row first second _ harity haCount hscan hm hf hs
  intro beta j Theta resultTail hj hr ht
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hret' := renameInto hret j Theta hj
  have hfn' := renameInto hfn j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hc' he' hp' hm' hret' hfn'
  exact ChildApplicationProof.actual Q body beta Theta (input.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (child0.relabel j) (child1.relabel j) (fnType.relabel j) (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) resultTail (second.relabel j) (returned.relabel j) hi' hc' hfn' he' hp' hm' hr ht hret'

theorem actual (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned domain child0 child1 : OTerm alpha)
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
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain child0 child1)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  apply programCases InternalListCodec.consCode (Fin.cons domain (Fin.cons typ Fin.elim0)) _
  intro beta j Theta fnType hj hfn
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hfn
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
  have hc' := renameInto hc j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc'
  exact atArrow Q H M W (input.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (childCount.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) (domain.relabel j) (child0.relabel j) (child1.relabel j) fnType hi' hparameter' ha' harity' he' hscan' hm' hf' hs' hret' hc' hfn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedApplicationProof
