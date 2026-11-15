module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.ExtractionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeMapGraph.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.NonzeroProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.RootProof
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

open ExtractionSupportProof
variable (n : Nat)
theorem atWitnesses (raw param rank table value old nodes deps answers inner pair out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) (suc inner) raw answers param)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair raw inner)))
    (hout : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out pair z)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  have hs := ExchangeGraphStage.InternalProof.internalKeep body alpha Delta
    OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n) nodes raw z old param deps answers inner pair z out
    hnodes hdeps hanswers hinner hpair
    (ArgumentEntriesNilExtraction.LeafSupportProof.stageNil _ _ old param) hout
  have hf := ExchangeGraphRecursion.InternalProof.successorValue OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)
    rank raw param old rank z nodes out hold hr (InternalEqualityTestSubtractionProof.subtractSelf rank)
    (ArgumentEntriesNilExtraction.LeafSupportProof.frontierZero _ raw param nodes hnodes) hs
  have he := ExchangeSelectedRecursor.InternalProof.internalSingletonValue body alpha Delta
    OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n) raw param rank out pair inner hr hf hout hpair
  have hl := ExchangeMapGraph.InternalProof.internalFirstHit body alpha Delta out pair z raw inner hout hpair
  have hq := valueUnique (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) out table ![suc rank,raw,param] hf ht
  exact relationAtValue n raw param table value inner he (tableTransport out table raw inner hq hl)

theorem atPair (raw param rank table value old nodes deps answers inner pair : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) (suc inner) raw answers param)))
    (hpair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pair raw inner)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons pair (Fin.cons z Fin.elim0)) _
  intro beta j Theta out hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := InternalGraphCompositionFunctionalityProof.renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := InternalGraphCompositionFunctionalityProof.renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  have hinnerj := InternalGraphCompositionFunctionalityProof.renameInto hinner j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hinnerj
  have hpairj := InternalGraphCompositionFunctionalityProof.renameInto hpair j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hpairj
  exact atWitnesses n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) (inner.relabel j) (pair.relabel j) out hrj htj holdj hnodesj hdepsj hanswersj hinnerj hpairj hx

theorem atSome (raw param rank table value old nodes deps answers inner : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) (suc inner) raw answers param)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases InternalPairing.pairing (Fin.cons raw (Fin.cons inner Fin.elim0)) _
  intro beta j Theta pair hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := InternalGraphCompositionFunctionalityProof.renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := InternalGraphCompositionFunctionalityProof.renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  have hinnerj := InternalGraphCompositionFunctionalityProof.renameInto hinner j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hinnerj
  exact atPair n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) (inner.relabel j) pair hrj htj holdj hnodesj hdepsj hanswersj hinnerj hx

theorem atOutput (raw param rank table value old nodes deps answers output : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (houtput : Nonempty (Derivation body Delta (graph3 (OriginalCodeBoundsRecursion.layer n) output raw answers param)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  have hn : Nonempty (Derivation body Delta (eqn output z).not) :=
    OriginalCodeBoundsRecursion.NonzeroProof.internalLayerNonzero n body alpha Delta raw answers param output houtput
  apply zeroSuccessorCases Delta output _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta inner hj he
    rw [relationRename]
    have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
    have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
    have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
    have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
    have hdepsj := InternalGraphCompositionFunctionalityProof.renameInto hdeps j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
    have hanswersj := InternalGraphCompositionFunctionalityProof.renameInto hanswers j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
    have houtputj := InternalGraphCompositionFunctionalityProof.renameInto houtput j Theta hj
    simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at houtputj
    have hinner := outputTransport (OriginalCodeBoundsRecursion.layer n) (output.relabel j) (suc inner) ![raw.relabel j,answers.relabel j,param.relabel j] he houtputj
    exact atSome n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) inner hrj htj holdj hnodesj hdepsj hanswersj hinner

theorem at4 (raw param rank table value old nodes deps answers : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases (OriginalCodeBoundsRecursion.layer n) (Fin.cons raw (Fin.cons answers (Fin.cons param Fin.elim0))) _
  intro beta j Theta output hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := InternalGraphCompositionFunctionalityProof.renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  have hanswersj := InternalGraphCompositionFunctionalityProof.renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hanswersj
  exact atOutput n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) (answers.relabel j) output hrj htj holdj hnodesj hdepsj hanswersj hx

theorem at3 (raw param rank table value old nodes deps : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    (hdeps : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.dependency deps raw param)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases ExchangeMapGraph.mapGraph (Fin.cons deps (Fin.cons old Fin.elim0)) _
  intro beta j Theta answers hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  have hdepsj := InternalGraphCompositionFunctionalityProof.renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hdepsj
  exact at4 n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) (deps.relabel j) answers hrj htj holdj hnodesj hdepsj hx

theorem at2 (raw param rank table value old nodes : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    (hnodes : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode nodes raw z)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases OriginalCodeBoundsRecursion.dependency (Fin.cons raw (Fin.cons param Fin.elim0)) _
  intro beta j Theta deps hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  have hnodesj := InternalGraphCompositionFunctionalityProof.renameInto hnodes j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hnodesj
  exact at3 n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) (nodes.relabel j) deps hrj htj holdj hnodesj hx

theorem at1 (raw param rank table value old : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    (hold : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) old rank raw param)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases InternalListCodec.consCode (Fin.cons raw (Fin.cons z Fin.elim0)) _
  intro beta j Theta nodes hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  have holdj := InternalGraphCompositionFunctionalityProof.renameInto hold j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at holdj
  exact at2 n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) (old.relabel j) nodes hrj htj holdj hx

theorem at0 (raw param rank table value : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 OriginalCodeBoundsRecursion.rank rank raw param)))
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) table (suc rank) raw param)))
    : Nonempty (Derivation body Delta (relation n raw param table value)) := by
  apply programCases (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) (Fin.cons rank (Fin.cons raw (Fin.cons param Fin.elim0))) _
  intro beta j Theta old hj hx
  rw [relationRename]
  simp only [consTermRename,emptyRename,zRelabel,sucRelabel] at hx
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at hrj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,sucRelabel,zRelabel] at htj
  exact at1 n (raw.relabel j) (param.relabel j) (rank.relabel j) (table.relabel j) (value.relabel j) old hrj htj hx

theorem rootExtraction : ExtractionTargets.InternalRootExtraction := by
  intro n body alpha Delta raw param rank table value hr ht
  have h := at0 n raw param rank table value hr ht
  constructor
  · intro he
    obtain ⟨hi⟩ := andLeft h
    obtain ⟨he⟩ := he
    exact ⟨Derivation.implicationElimination hi he⟩
  · intro hl
    obtain ⟨hi⟩ := andRight h
    obtain ⟨hl⟩ := hl
    exact ⟨Derivation.implicationElimination hi hl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.RootProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsEquation.RootProof
