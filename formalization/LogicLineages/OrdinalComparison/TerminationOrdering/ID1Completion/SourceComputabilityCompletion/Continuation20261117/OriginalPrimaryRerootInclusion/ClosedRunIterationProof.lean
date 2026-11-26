module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryStability.InductionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bound (E : Program 3) (count pool initial parameter out carrier first : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out count pool initial parameter)))
    (hinc : Nonempty (Derivation body Delta (PrimaryMonotonicity.included initial carrier)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) first pool carrier parameter)))
    (hclosed : Nonempty (Derivation body Delta (PrimaryMonotonicity.included first carrier))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included out carrier)) := by
  apply programCases (PrimaryIteration.iterate E)
    (Fin.cons count (Fin.cons pool (Fin.cons carrier (Fin.cons parameter Fin.elim0)))) _
  intro beta j Theta comparison hj hcomparison
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hcomparison
  have hi' := renameInto hi j Theta hj
  rw [graph4Rename] at hi'
  have hinc' := renameInto hinc j Theta hj
  rw [includedRename] at hinc'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hclosed' := renameInto hclosed j Theta hj
  rw [includedRename] at hclosed'
  have hmono := PrimaryMonotonicity.InductionProof.iterationMonotonicity E body beta Theta
    (count.relabel j) (pool.relabel j) (initial.relabel j) (carrier.relabel j) (parameter.relabel j)
    (out.relabel j) comparison hinc' hi' hcomparison
  have hstable := PrimaryStability.InductionProof.iterationStability E body beta Theta
    (count.relabel j) (pool.relabel j) (carrier.relabel j) (first.relabel j) (parameter.relabel j)
    comparison he' hclosed' hcomparison
  exact PrimaryStability.InclusionProof.transitive (out.relabel j) comparison (carrier.relabel j) hmono hstable

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunIterationProof
