module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeStageCoverage.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Proof
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

theorem stageValue : Targets.InternalStageValue := by
  intro body alpha Delta frontier old param table node deps answers value ht hm hd ha hl
  apply programCases (.composition ArgumentEntriesLayer.step ![ArgumentEntriesLayer.raw,ArgumentEntriesLayer.tailAnswer])
    (Fin.cons node (Fin.cons answers Fin.elim0)) _
  intro beta j Theta inner hj hi
  simp only [graph3Rename,sucRelabel]
  simp only [consTermRename,emptyRename] at hi
  have htj := renameInto ht j Theta hj
  rw [graph3Rename] at htj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hdj := renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have haj := renameInto ha j Theta hj
  rw [graph2Rename] at haj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,sucRelabel] at hlj
  have hg := ArgumentEntriesTableDomain.SupportProof.layerSome (node.relabel j) (answers.relabel j) (param.relabel j) inner hi
  have hs := ExchangeStageCoverage.Proof.coverage body beta Theta ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    (frontier.relabel j) (node.relabel j) (old.relabel j) (param.relabel j) (deps.relabel j) (answers.relabel j) inner (table.relabel j)
    hmj hdj haj hg htj
  have he := valueUnique ExchangeMapGraph.lookup (suc inner) (suc (value.relabel j))
    (Fin.cons (table.relabel j) (Fin.cons (node.relabel j) Fin.elim0)) hs hlj
  exact outputTransport ArgumentEntriesRecursor.layer (suc inner) (suc (value.relabel j))
    (Fin.cons (node.relabel j) (Fin.cons (answers.relabel j) (Fin.cons (param.relabel j) Fin.elim0))) he hg

theorem successorValue : Targets.InternalSuccessorValue := by
  intro body alpha Delta index seed param depth frontier old table node deps answers value hd hf ho ht hm hdeps ha hl
  have hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.rank seed seed param)) :=
    projectionValue 0 (Fin.cons seed (Fin.cons param Fin.elim0))
  have hs := (ExchangeGraphRecursion.InternalProof.internalSuccessor body alpha Delta
    ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    index seed param old seed depth frontier table ho hr hd hf).mp ht
  exact stageValue body alpha Delta frontier old param table node deps answers value hs hm hdeps ha hl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesValueRecurrence.Proof
