module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.IterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.SingletonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.RunGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.RunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {R : Program 1}
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SyntaxProof
theorem preserved (R : Program 1) (E : Program 3) (count pool seed parameter out carrier : OrdinaryArithmetic.Term alpha)
 (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) out count pool seed parameter)))
 (hseedpool : Nonempty (Derivation body Delta (graph1 R carrier seed)))
 (hback : Nonempty (Derivation body Delta (forwardClosed R E carrier parameter))) :
 Nonempty (Derivation body Delta (allAccepted R carrier out)) := by
 change Nonempty (Derivation body Delta (allAcceptedAt R pool carrier seed out))
 apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
 intro beta j Theta singleton hj hs
 rw [allAcceptedRename]
 simp only [consTermRename,emptyRename,zRelabel] at hs
 have hr' := renameInto hr j Theta hj
 rw [graph4Rename] at hr'
 have hseedpool' := renameInto hseedpool j Theta hj
 simp only [graph1Rename] at hseedpool'
 have hb : Nonempty (Derivation body Delta (forwardClosedAt R E pool carrier parameter)) := hback
 have hback' := renameInto hb j Theta hj
 rw [backClosedRename] at hback'
 have hi := OriginalPrimaryReverseMembership.RunGraphProof.recover E (count.relabel j) (pool.relabel j) (seed.relabel j)
   (parameter.relabel j) (out.relabel j) singleton hs hr'
 have hsingle := SingletonProof.preserved (pool.relabel j) (carrier.relabel j) (seed.relabel j) singleton hs hseedpool'
 exact IterationProof.preserved E (count.relabel j) (pool.relabel j) singleton (parameter.relabel j)
   (out.relabel j) (carrier.relabel j) (seed.relabel j) hi hsingle hback'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.RunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryVariableRankPreservation.RunProof
