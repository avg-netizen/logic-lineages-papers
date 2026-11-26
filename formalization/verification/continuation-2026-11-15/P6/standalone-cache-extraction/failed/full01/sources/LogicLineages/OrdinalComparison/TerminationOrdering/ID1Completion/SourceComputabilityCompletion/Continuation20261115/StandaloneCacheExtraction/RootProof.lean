module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.RootProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open SupportProof

theorem atWitnesses (raw param table value old nodes deps answers inner pair out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner raw answers)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair raw inner)))
    (hout : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair z)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  have hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.rank raw raw param)) :=
    projectionValue 0 ![raw,param]
  have hg := ArgumentEntriesTableDomain.SupportProof.layerSome raw answers param inner hinner
  have hs := ExchangeGraphStage.InternalProof.internalKeep body alpha Delta
    ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer nodes raw z old param deps answers inner pair z out
    hnodes hdeps hanswers hg hpair
    (ArgumentEntriesNilExtraction.LeafSupportProof.stageNil _ _ old param) hout
  have hf := ExchangeGraphRecursion.InternalProof.successorValue
    ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    raw raw param old raw z nodes out hold hr (InternalEqualityTestSubtractionProof.subtractSelf raw)
    (ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero _ raw param nodes hnodes) hs
  have he := ExchangeSelectedRecursor.InternalProof.internalSingletonValue body alpha Delta
    ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    raw param raw out pair inner hr hf hout hpair
  have hl := ExchangeMapGraph.InternalProof.internalFirstHit body alpha Delta out pair z raw inner hout hpair
  have hq := valueUnique ArgumentEntriesRecursor.graph out table ![suc raw,raw,param] hf ht
  exact relationAtValue raw param table value inner he (tableTransport out table raw inner hq hl)

theorem at6 (raw param table value old nodes deps answers inner pair : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner raw answers)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair raw inner)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons pair (Fin.cons z (Fin.elim0))) _
  intro beta j Theta out hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  have hinnerj := renameInto hinner j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hinnerj
  have hpairj := renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hpairj
  exact atWitnesses (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) (inner.relabel j) (pair.relabel j) out htj holdj hnodesj hdepsj hanswersj hinnerj hpairj hx

theorem at5 (raw param table value old nodes deps answers inner : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner raw answers)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases InternalPairing.pairing (Fin.cons raw (Fin.cons inner (Fin.elim0))) _
  intro beta j Theta pair hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  have hinnerj := renameInto hinner j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hinnerj
  exact at6 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) (inner.relabel j) pair htj holdj hnodesj hdepsj hanswersj hinnerj hx

theorem at4 (raw param table value old nodes deps answers : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) (Fin.cons raw (Fin.cons answers (Fin.elim0))) _
  intro beta j Theta inner hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  exact at5 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) inner htj holdj hnodesj hdepsj hanswersj hx

theorem at3 (raw param table value old nodes deps : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old (Fin.elim0))) _
  intro beta j Theta answers hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  exact at4 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) answers htj holdj hnodesj hdepsj hx

theorem at2 (raw param table value old nodes : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases ArgumentEntriesRecursor.dependency (Fin.cons raw (Fin.cons param (Fin.elim0))) _
  intro beta j Theta deps hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  exact at3 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) deps htj holdj hnodesj hx

theorem at1 (raw param table value old : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph old raw raw param)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons raw (Fin.cons z (Fin.elim0))) _
  intro beta j Theta nodes hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  exact at2 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) nodes htj holdj hx

theorem at0 (raw param table value : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 ArgumentEntriesRecursor.graph table (suc raw) raw param)))
    : Nonempty (Derivation body Delta (relation raw param table value)) := by
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons raw (Fin.cons raw (Fin.cons param (Fin.elim0)))) _
  intro beta j Theta old hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  exact at1 (raw.relabel j) (param.relabel j) (table.relabel j) (value.relabel j) old htj hx

theorem rootExtraction : Targets.InternalRootExtraction := by
  intro body alpha Delta raw param table value ht
  have h := at0 raw param table value ht
  constructor
  · intro he
    obtain ⟨hi⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
  · intro hl
    obtain ⟨hi⟩ := andRight h
    obtain ⟨hl⟩ := hl
    exact ⟨Derivation.implicationElimination hi hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.RootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.StandaloneCacheExtraction.RootProof
