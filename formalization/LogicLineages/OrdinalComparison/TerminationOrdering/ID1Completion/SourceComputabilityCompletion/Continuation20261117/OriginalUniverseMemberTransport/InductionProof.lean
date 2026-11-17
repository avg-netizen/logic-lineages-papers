module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.IntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.BranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.InductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalRawListRecursionSyntaxProof InternalGraphCompositionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderTransport (Accepted)
open OriginalUniverseDecoderTransportSyntaxProof (acceptedSubst acceptedRename)
open InternalStrongInduction
open Definitions InductionDefinitions

open BindingProof IntroductionProof SyntaxProof
open InternalGraphCompositionFunctionalityProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem allRaw (H : Program 1) (M N W : Program 2) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw H M N W raw)) := by
  apply rawInduction H M N W raw
  intro beta Theta r hind
  apply atRawIntroFrom H M N W r
  intro gamma j Xi arguments typ context c hj hi ha
  have hind' := renameInto hind j Xi hj
  rw [belowRawRename] at hind'
  exact BranchProof.step H M N W arguments (r.relabel j) typ context c hind' hi ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.InductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalUniverseMemberTransport.InductionProof
