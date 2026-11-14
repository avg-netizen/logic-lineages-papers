module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InductionDefinitions.Induction InductionSyntaxProof InductionStepProof
open PrimaryIteration.RecursionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem successorWithPrevious (E : Program 3) (elapsed pool initial parameter out next initialRemaining remaining previous : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E elapsed)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out (suc elapsed) pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out)))
    (hp : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) previous elapsed pool initial parameter)))
    : Nonempty (Derivation body Delta (budget (suc elapsed) initialRemaining remaining out next)) := by
  apply programCases (PrimaryUncoveredCount.count) (Fin.cons pool (Fin.cons previous Fin.elim0)) _
  intro beta j Theta value hj hv
  simp only [budgetRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hv
  have hrow' := renameInto hrow j Theta hj
  simp only [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  simp only [graph4Rename,sucRelabel] at hi'
  have he' := renameInto he j Theta hj
  simp only [graph3Rename] at he'
  have hinit' := renameInto hinit j Theta hj
  simp only [graph2Rename] at hinit'
  have hrem' := renameInto hrem j Theta hj
  simp only [graph2Rename] at hrem'
  have hp' := renameInto hp j Theta hj
  simp only [graph4Rename] at hp'
  have hstep := successorRecover E (elapsed.relabel j) (previous.relabel j) (out.relabel j)
    (pool.relabel j) (initial.relabel j) (parameter.relabel j) hp' hi'
  exact successorKnown E (elapsed.relabel j) (pool.relabel j) (initial.relabel j) (parameter.relabel j) (out.relabel j) (next.relabel j) (initialRemaining.relabel j) (remaining.relabel j) (previous.relabel j) value hrow' hp' hstep he' hinit' hrem' hv

theorem successorCore (E : Program 3) (elapsed pool initial parameter out next initialRemaining remaining : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (AtCount E elapsed)))
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out (suc elapsed) pool initial parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter)))
    (hinit : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count initialRemaining pool initial)))
    (hrem : Nonempty (Derivation body Delta (graph2 PrimaryUncoveredCount.count remaining pool out)))
    : Nonempty (Derivation body Delta (budget (suc elapsed) initialRemaining remaining out next)) := by
  apply programCases (PrimaryIteration.iterate E) (Fin.cons elapsed (Fin.cons pool (Fin.cons initial (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta value hj hv
  simp only [budgetRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hv
  have hrow' := renameInto hrow j Theta hj
  simp only [atCountRename] at hrow'
  have hi' := renameInto hi j Theta hj
  simp only [graph4Rename,sucRelabel] at hi'
  have he' := renameInto he j Theta hj
  simp only [graph3Rename] at he'
  have hinit' := renameInto hinit j Theta hj
  simp only [graph2Rename] at hinit'
  have hrem' := renameInto hrem j Theta hj
  simp only [graph2Rename] at hrem'
  exact successorWithPrevious E (elapsed.relabel j) (pool.relabel j) (initial.relabel j) (parameter.relabel j) (out.relabel j) (next.relabel j) (initialRemaining.relabel j) (remaining.relabel j) value hrow' hi' he' hinit' hrem' hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.InductionCoreProof
