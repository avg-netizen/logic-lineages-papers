module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.InvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryCarrierBound.RunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SingletonProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open SyntaxProof
open InternalTagArithmeticSupportProof (symm)
theorem preserved (pool carrier seed singleton : OrdinaryArithmetic.Term alpha)
 (hs : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton seed z)))
 (hp : Nonempty (Derivation body Delta (graph2 contains (numeral 1) pool seed))) :
 Nonempty (Derivation body Delta (allAccepted pool carrier seed singleton)) := by
 apply InvariantProof.introduce pool carrier seed singleton
 intro beta j Theta x hj hm
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,zRelabel] at hs'
 have hp' := renameInto hp j Theta hj
 simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
 have he := PrimaryCarrierBound.RunProof.singletonMember (singleton.relabel j) (seed.relabel j) x hs' hm
 have hpx := PrimaryCarrierBound.RunProof.poolMember (pool.relabel j) (seed.relabel j) x hp' he
 let A := graph2 contains (numeral 1) (carrier.relabel j) x
 obtain ⟨he⟩ := withHyp he A
 obtain ⟨hc⟩ := PrimaryCarrierBound.RunProof.poolMember (carrier.relabel j) x (seed.relabel j)
   ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨symm he⟩
 exact andIntro hpx ⟨Derivation.implicationIntroduction hc⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryReverseMembership.SingletonProof
