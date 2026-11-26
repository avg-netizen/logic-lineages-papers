module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunSingletonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryUniverseClosure.RunGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunProof
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

theorem bound (E : Program 3) (count pool seed parameter out carrier first : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) out count pool seed parameter)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) carrier seed)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) first pool carrier parameter)))
    (hclosed : Nonempty (Derivation body Delta (PrimaryMonotonicity.included first carrier))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included out carrier)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hsingle
  rw [includedRename]
  simp only [consTermRename,emptyRename,zRelabel] at hsingle
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hm'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hclosed' := renameInto hclosed j Theta hj
  rw [includedRename] at hclosed'
  have hi := OriginalPrimaryUniverseClosure.RunGraphProof.recover E (count.relabel j) (pool.relabel j)
    (seed.relabel j) (parameter.relabel j) (out.relabel j) singleton hsingle hr'
  have hinc := ClosedRunSingletonProof.included singleton (seed.relabel j) (carrier.relabel j) hsingle hm'
  exact ClosedRunIterationProof.bound E (count.relabel j) (pool.relabel j) singleton (parameter.relabel j)
    (out.relabel j) (carrier.relabel j) (first.relabel j) hi hinc he' hclosed'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunProof
