module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedScanSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedTypeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLambdaProof
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

theorem actual (Q : Program 2) (H : Program 1) (M W : Program 2) (input typ raw parameter c gamma childCount jobs annotatedPrefix row first second returned domain child : OTerm alpha)
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
    (hc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)))
    : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  have haCount := OriginalRawSyntaxTransportInternalConstructorSelectorsProof.lambdaArity (.projection 0) raw domain child (Fin.cons raw Fin.elim0) (projectionValue 0 (Fin.cons raw Fin.elim0)) hc
  have hp := AdmittedScanSlotsProof.countTransport childCount (numeral 1) z typ raw jobs annotatedPrefix harity haCount hscan
  have hr := AdmittedScanSlotsProof.singleton (observationFromJob Q) childCount z typ raw jobs annotatedPrefix row first harity haCount hscan hm hf
  apply AdmittedTypeProof.lambdaTypeCases H M W raw domain child typ gamma c _ hc ha
  intro beta j Theta codomain hj htype
  rw [graph2Rename]
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hr' := renameInto hr j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename,termAcceptedRename,consGraphRename,programRename,consTermRename,emptyRename] at hi' hc' he' hp' hm' hr' hret'
  exact UnaryLambdaProof.actual Q body beta Theta (input.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (child.relabel j) codomain (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) hi' hc' htype he' hp' hm' hr' hret'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.AdmittedLambdaProof
