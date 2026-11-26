module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem atWitnesses (R D : Program 2) (G : Program 3)
    (seed param rank old deps answers value nodes pair table : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D deps seed param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed answers param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair z))) :
    Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  have hs := ExchangeGraphStage.InternalProof.internalKeep body alpha Delta D G
    nodes seed z old param deps answers value pair z table hf hd hm hg hp (ArgumentEntriesNilExtraction.LeafSupportProof.stageNil D G old param) ht
  have hfinal := ExchangeGraphRecursion.InternalProof.successorValue R D G rank seed param old rank z nodes table
    ho hr (InternalEqualityTestSubtractionProof.subtractSelf rank) (ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero D seed param nodes hf) hs
  exact ExchangeSelectedRecursor.InternalProof.internalSingletonValue body alpha Delta R D G
    seed param rank table pair value hr hfinal ht hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.FinalSupportProof
