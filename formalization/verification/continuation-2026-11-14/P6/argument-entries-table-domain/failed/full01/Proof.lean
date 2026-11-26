module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.StageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Proof
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

theorem successorDomain : Targets.InternalSuccessorDomain := by
  intro body alpha Delta index seed param depth frontier table node found hd hf ht hm hl
  apply programCases ArgumentEntriesRecursor.graph (Fin.cons index (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old hj ho
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at ho
  have hdj := renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hfj := renameInto hf j Theta hj
  rw [graph3Rename] at hfj
  have htj := renameInto ht j Theta hj
  simp only [graph3Rename,sucRelabel] at htj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  have hr : Nonempty (Derivation body Theta (graph2 ArgumentEntriesRecursor.rank (seed.relabel j) (seed.relabel j) (param.relabel j))) :=
    projectionValue 0 (Fin.cons (seed.relabel j) (Fin.cons (param.relabel j) Fin.elim0))
  have hs := (ExchangeGraphRecursion.InternalProof.internalSuccessor body beta Theta
    ArgumentEntriesRecursor.rank ArgumentEntriesRecursor.dependency ArgumentEntriesRecursor.layer
    (index.relabel j) (seed.relabel j) (param.relabel j) old (seed.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j)
    ho hr hdj hfj).mp htj
  exact StageProof.stageDomain body beta Theta (frontier.relabel j) old (param.relabel j)
    (table.relabel j) (node.relabel j) (found.relabel j) hs hmj hlj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Proof
