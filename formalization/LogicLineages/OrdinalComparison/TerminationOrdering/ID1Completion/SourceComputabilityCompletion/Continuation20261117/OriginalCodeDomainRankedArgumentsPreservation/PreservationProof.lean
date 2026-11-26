module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthAgreementProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.EntryFactsTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.OptionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open OriginalArgumentPermutationClosure.CountAgreement OriginalArgumentPermutationClosure.CountAgreementSyntaxProof
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem invariantTransfer (H : Program 1) (M W : Program 2) (count left right gamma context : OTerm alpha)
    (he : Nonempty (Derivation body Delta (agreement left right)))
    (hi : Nonempty (Derivation body Delta (invariant H M W count left gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count right gamma context)) := by
  apply programCases OriginalContextInsertion.length ![right] _
  intro beta j Theta rc hj hr
  have hx : (fun i => (![right] i).relabel j) = ![right.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hr
  rw [invariantRename]
  have he' := renameInto he j Theta hj
  rw [agreementRename] at he'
  have hi' := renameInto hi j Theta hj
  rw [invariantRename] at hi'
  obtain ⟨hc⟩ := LengthAgreementProof.agreementLength (left.relabel j) (right.relabel j)
    (count.relabel j) rc he' (andLeft hi') hr
  have hl := outputTransport OriginalContextInsertion.length rc (count.relabel j) ![right.relabel j] ⟨symm hc⟩ hr
  have hg := EntryFactsTransferProof.transferAll H M W (left.relabel j) (right.relabel j)
    (gamma.relabel j) (context.relabel j) he' (andRight hi')
  exact andIntro hl hg

theorem withLists (n : Nat) (H : Program 1) (M W : Program 2)
    (count types base target left right gamma context : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) base)))
    (ht : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target)))
    (hg : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types base gamma context)))
    (hl : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc left) base z)))
    (hr : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc right) target z)))
    (hp : Nonempty (Derivation body Delta (graph2 ArgumentCountComparison.permutation (suc z) left right))) :
    Nonempty (Derivation body Delta (Accepted H M W true types target gamma context)) := by
  have hd := andIntro hb (andIntro hl hg)
  have hi := TypedSpineInvariantProof.source n H M W base count types left gamma context hd ha
  have he := OriginalArgumentPermutationClosure.AllQueryProof.permutationAgreement left right hp
  exact TypedSpineInvariantProof.target n H M W target count types right gamma context
    (andIntro ht (andIntro hr hg)) (invariantTransfer H M W count left right gamma context he hi)

theorem preserved : Targets.InternalCodeDomainArgumentsPreserved := by
  intro n arity M W body alpha Delta count types base target gamma context hb ht hg ha hp
  let H := Continuation20261116.OriginalConcreteHeadSignature.signature n arity
  apply OriginalArgumentPermutationClosure.OptionProof.bothCases base target _ hp
  intro beta j Theta left right hj hl hr hperm
  have hb' := renameInto hb j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hb' ht'
  have hg' := renameInto hg j Theta hj
  rw [graph1Rename] at hg'
  have ha' := renameInto ha j Theta hj
  change Nonempty (Derivation body Theta ((Accepted H M W true types base gamma context).relabel j)) at ha'
  rw [acceptedRename] at ha'
  change Nonempty (Derivation body Theta ((Accepted H M W true types target gamma context).relabel j))
  rw [acceptedRename]
  exact withLists n H M W (count.relabel j) (types.relabel j) (base.relabel j) (target.relabel j)
    left right (gamma.relabel j) (context.relabel j) hb' ht' hg' ha' hl hr hperm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.PreservationProof
