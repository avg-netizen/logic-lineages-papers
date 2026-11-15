module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
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
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem layerSome (node answers param inner : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner node answers))) :
    Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.layer (suc inner) node answers param)) := by
  have hs := unaryValue .succ (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) (suc inner) inner
    (Fin.cons node (Fin.cons answers Fin.elim0))
    (successorValue (Fin.cons inner Fin.elim0)) hi
  exact binaryValue ArgumentEntriesLayer.recombine (.projection 0) (.projection 1)
    (suc inner) node answers (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))) hs
    (projectionValue 0 (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))))
    (projectionValue 1 (Fin.cons node (Fin.cons answers (Fin.cons param Fin.elim0))))

theorem atValues (frontier old param table node found deps answers inner : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)))
    (ha : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hi : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner node answers))) :
    Nonempty (Derivation body Delta (eqn found z).not) := by
  have hs := ExchangeStageCoverage.Proof.coverage body alpha Delta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    frontier node old param deps answers inner table hm hd ha (layerSome node answers param inner hi) ht
  obtain ⟨he⟩ := valueUnique ExchangeMapGraph.lookup found (suc inner) ![table,node] hl hs
  have bad : Derivation body (eqn found z :: Delta) ⊥ :=
    sucNeZeroApply (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.implicationIntroduction bad⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
