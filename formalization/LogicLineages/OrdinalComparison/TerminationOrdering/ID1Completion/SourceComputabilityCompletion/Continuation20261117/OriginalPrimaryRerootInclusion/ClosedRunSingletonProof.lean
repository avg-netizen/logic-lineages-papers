module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCommonCandidatePool.MembershipProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunSingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
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

theorem included (singleton seed carrier : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton seed z)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) carrier seed))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included singleton carrier)) := by
  apply introduce singleton carrier
  intro beta j Theta candidate hj hc
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,zRelabel] at hs'
  have hm' := renameInto hm j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hm'
  obtain ⟨he⟩ := PrimaryCarrierBound.RunProof.singletonMember (singleton.relabel j) (seed.relabel j) candidate hs' hc
  exact OriginalCommonCandidatePool.MembershipProof.candidateTransport (carrier.relabel j)
    (seed.relabel j) candidate ⟨symm he⟩ hm'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunSingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.ClosedRunSingletonProof
