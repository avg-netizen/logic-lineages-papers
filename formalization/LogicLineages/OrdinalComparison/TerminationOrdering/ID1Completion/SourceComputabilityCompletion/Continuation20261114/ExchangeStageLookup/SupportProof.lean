module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphStage.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
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
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
theorem actualCons (D : Program 2) (G : Program 3) (frontier node tail old param deps answers value out rest pair table : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode frontier node tail)))
    (hd : Nonempty (Derivation body Delta (graph2 D deps node param)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hg : Nonempty (Derivation body Delta (graph3 G (suc value) node answers param)))
    (ho : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) out frontier old param)))
    (hr : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage D G) rest tail old param)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair node value)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode table pair rest)))
    : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair rest)) := by
  have hs := ExchangeGraphStage.InternalProof.internalKeep body alpha Delta D G
    frontier node tail old param deps answers value pair rest table hf hd hm hg hp hr ht
  have he := valueUnique (ExchangeGraphStage.stage D G) table out ![frontier,old,param] hs ho
  exact outputTransport InternalListCodec.consCode table out ![pair,rest] he ht

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageLookup.SupportProof
