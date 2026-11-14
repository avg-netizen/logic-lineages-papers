module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontier.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
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

open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem frontierZero (D : Program 2) (seed param nodes : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z))) :
    Nonempty (Derivation body Delta (graph3 (ExchangeFrontier.bindList D) nodes z seed param)) := by
  have hs : Nonempty (Derivation body Delta (graph2 ExchangeFrontier.singleton nodes seed param)) :=
    binaryValue InternalListCodec.consCode (.projection 0) (InternalAcceptance.constantZero 2) nodes seed z
      (Fin.cons seed (Fin.cons param Fin.elim0)) hc
      (projectionValue 0 (Fin.cons seed (Fin.cons param Fin.elim0)))
      (constantZeroValue (Fin.cons seed (Fin.cons param Fin.elim0)))
  exact recursionZeroValue ExchangeFrontier.singleton (ExchangeFrontier.bindStep D) nodes ![seed,param] hs

theorem mapNil (old : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph z z old)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) ExchangeMapGraph.mapStep
    z (Fin.cons old Fin.elim0) (constantZeroValue (Fin.cons old Fin.elim0))

theorem stageNil (D : Program 2) (G : Program 3) (old param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) z z old param)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 2) (ExchangeGraphStage.step D G)
    z (Fin.cons old (Fin.cons param Fin.elim0)) (constantZeroValue (Fin.cons old (Fin.cons param Fin.elim0)))

theorem atWitnesses (R D : Program 2) (G : Program 3)
    (seed param value rank old nodes pair table : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (graph2 D z seed param)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) seed z param)))
    (hr : Nonempty (Derivation body Delta (graph2 R rank seed param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph R D G) old rank seed param)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes seed z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair seed value)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair z))) :
    Nonempty (Derivation body Delta (graph2 (ExchangeSelectedRecursor.exchange R D G) value seed param)) := by
  have hs := ExchangeGraphStage.InternalProof.internalKeep body alpha Delta D G
    nodes seed z old param z z value pair z table hf hd (mapNil old) hg hp (stageNil D G old param) ht
  have hfinal := ExchangeGraphRecursion.InternalProof.successorValue R D G rank seed param old rank z nodes table
    ho hr (InternalEqualityTestSubtractionProof.subtractSelf rank) (frontierZero D seed param nodes hf) hs
  exact ExchangeSelectedRecursor.InternalProof.internalSingletonValue body alpha Delta R D G
    seed param rank table pair value hr hfinal ht hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesNilExtraction.LeafSupportProof
