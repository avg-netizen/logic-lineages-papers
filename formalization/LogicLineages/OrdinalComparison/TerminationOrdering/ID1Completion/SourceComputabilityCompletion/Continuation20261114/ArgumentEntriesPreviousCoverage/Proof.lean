module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesTableDomain.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeFrontierCoverage.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Proof
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

open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
theorem previousCoverage : Targets.InternalPreviousCoverage := by
  intro body alpha Delta index seed param depth frontier table node deps child found hs hf ht hn hd hc hl
  apply programCases (ExchangeFrontier.bindList ArgumentEntriesRecursor.dependency)
    (Fin.cons (suc depth) (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta next hj hnext
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename,sucRelabel] at hnext
  have hsj := renameInto hs j Theta hj
  simp only [graph2Rename,sucRelabel] at hsj
  have hfj := renameInto hf j Theta hj
  rw [graph3Rename] at hfj
  have htj := renameInto ht j Theta hj
  simp only [graph3Rename,sucRelabel] at htj
  have hnj := renameInto hn j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hnj
  have hdj := renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hcj
  have hlj := renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  have hm := ExchangeFrontierCoverage.Proof.successorCoverage body beta Theta ArgumentEntriesRecursor.dependency
    (depth.relabel j) (seed.relabel j) (param.relabel j) (frontier.relabel j) (node.relabel j)
    (deps.relabel j) (child.relabel j) next hfj hnj hdj hcj hnext
  exact ArgumentEntriesTableDomain.Proof.successorDomain body beta Theta
    (index.relabel j) (seed.relabel j) (param.relabel j) (suc (depth.relabel j)) next (table.relabel j)
    (child.relabel j) (found.relabel j) hsj hnext htj hm hlj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesPreviousCoverage.Proof
