module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.StageProof
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

theorem at3 (frontier old param table node found deps answers inner : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    (hinner : Nonempty (Derivation body Delta (graph2 (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer]) inner node answers)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  exact SupportProof.atValues frontier old param table node found deps answers inner ht hm hl hdeps hanswers hinner

theorem at2 (frontier old param table node found deps answers : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)))
    (hanswers : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps old)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases ((.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer])) (Fin.cons node (Fin.cons answers (Fin.elim0))) _
  intro beta j Theta inner hj hx
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdepsj
  have hanswersj := renameInto hanswers j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hanswersj
  exact at3 (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) (deps.relabel j) (answers.relabel j) inner htj hmj hlj hdepsj hanswersj hx

theorem at1 (frontier old param table node found deps : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    (hdeps : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps node param)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases (ExchangeMapGraph.mapGraph) (Fin.cons deps (Fin.cons old (Fin.elim0))) _
  intro beta j Theta answers hj hx
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  have hdepsj := renameInto hdeps j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hdepsj
  exact at2 (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) (deps.relabel j) answers htj hmj hlj hdepsj hx

theorem at0 (frontier old param table node found : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph3 (ExchangeGraphStage.stage ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer) table frontier old param)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) frontier node)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup found table node)))
    : Nonempty (Derivation body Delta (eqn found z).not) := by
  apply programCases (ArgumentEntriesRecursor.dependency) (Fin.cons node (Fin.cons param (Fin.elim0))) _
  intro beta j Theta deps hj hx
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at htj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hlj
  exact at1 (frontier.relabel j) (old.relabel j) (param.relabel j) (table.relabel j) (node.relabel j) (found.relabel j) deps htj hmj hlj hx

theorem stageDomain : Targets.InternalStageDomain := by
  intro body alpha Delta frontier old param table node found ht hm hl
  exact at0 frontier old param table node found ht hm hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.StageProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.StageProof
