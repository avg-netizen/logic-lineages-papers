module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainStageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSupportProof
open InternalPositiveUnfoldingSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem successorDomain : DomainTargets.InternalSuccessorDomain := by
  intro n body alpha Delta index seed param seedRank depth frontier table node found hr hd hf ht hm hl
  apply programCases (ExchangeGraphRecursion.graph OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)) (Fin.cons index (Fin.cons seed (Fin.cons param Fin.elim0))) _
  intro beta j Theta old hj ho
  change Nonempty (Derivation body Theta ((eqn found z).relabel j).not)
  rw [eqnRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at ho
  have hdj := InternalGraphCompositionFunctionalityProof.renameInto hd j Theta hj
  rw [graph2Rename] at hdj
  have hfj := InternalGraphCompositionFunctionalityProof.renameInto hf j Theta hj
  rw [graph3Rename] at hfj
  have htj := InternalGraphCompositionFunctionalityProof.renameInto ht j Theta hj
  simp only [graph3Rename,sucRelabel] at htj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hlj := InternalGraphCompositionFunctionalityProof.renameInto hl j Theta hj
  rw [graph2Rename] at hlj
  have hrj := InternalGraphCompositionFunctionalityProof.renameInto hr j Theta hj
  rw [graph2Rename] at hrj
  have hs := (ExchangeGraphRecursion.InternalProof.internalSuccessor body beta Theta
    OriginalCodeBoundsRecursion.rank OriginalCodeBoundsRecursion.dependency (OriginalCodeBoundsRecursion.layer n)
    (index.relabel j) (seed.relabel j) (param.relabel j) old (seedRank.relabel j) (depth.relabel j) (frontier.relabel j) (table.relabel j)
    ho hrj hdj hfj).mp htj
  exact DomainStageProof.stageDomain n body beta Theta (frontier.relabel j) old (param.relabel j)
    (table.relabel j) (node.relabel j) (found.relabel j) hs hmj hlj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsCacheCoherence.DomainProof
