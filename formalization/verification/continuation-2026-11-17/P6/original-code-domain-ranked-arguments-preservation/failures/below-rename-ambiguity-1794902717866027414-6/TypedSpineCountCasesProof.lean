module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineSuccessorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCountCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  apply zeroSuccessorCases Delta count _
  · have hz : Nonempty (Derivation body (eqn count z :: Delta) (eqn count z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hgt0 := headTransport Continuation20261116.OriginalConcreteHeadSignature.groundList types count z Fin.elim0 hz (withHyp hgt _)
    have ht0 := valueUnique Continuation20261116.OriginalConcreteHeadSignature.groundList types z ![z] hgt0
      Continuation20261117.OriginalSignatureStructure.GroundSupportProof.zeroValue
    have ha0 := headTransport (OriginalUniverseDecoder.argumentsCheck H M W) (suc z) types z ![raw,gamma,context]
      ht0 (withHyp ha _)
    exact TypedSpineConsZeroProof.sourceImpossible H M W raw typ head tail gamma context _ (withHyp hc _) ha0
  · intro beta j Theta c hj heq
    have hc' := renameInto hc j Theta hj
    rw [graph3Rename] at hc'
    have hp' := renameInto hp j Theta hj
    have hl' := renameInto hl j Theta hj
    rw [graph2Rename] at hp' hl'
    have hg' := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hg'
    have he' := renameInto he j Theta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at he'
    have hgt' := renameInto hgt j Theta hj
    rw [graph1Rename] at hgt'
    have hgs := headTransport Continuation20261116.OriginalConcreteHeadSignature.groundList (types.relabel j)
      (count.relabel j) (suc c) Fin.elim0 heq hgt'
    have ih' := renameInto ih j Theta hj
    rw [belowRawRename] at ih'
    have ha' := renameInto ha j Theta hj
    rw [acceptedRename] at ha'
    rw [invariantRename]
    have hs := TypedSpineSuccessorProof.source n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
      (tail.relabel j) c (types.relabel j) (entry.relabel j) (entries.relabel j) (tailEntries.relabel j)
      (gamma.relabel j) (context.relabel j) hc' hp' hl' hg' he' hgs ih' ha'
    obtain ⟨heq⟩ := heq
    exact andIntro (outputTransport OriginalContextInsertion.length (suc c) (count.relabel j)
      ![entries.relabel j] ⟨symm heq⟩ (andLeft hs)) (andRight hs)

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entry entries tailEntries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing entry typ head)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode entries entry tailEntries)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc tailEntries) tail z)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply zeroSuccessorCases Delta count _
  · have hz : Nonempty (Derivation body (eqn count z :: Delta) (eqn count z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl0 := outputTransport OriginalContextInsertion.length count z ![entries] hz (andLeft (withHyp ha _))
    exact TypedSpineConsZeroProof.lengthImpossible entries entry tailEntries _ (withHyp hl _) hl0
  · intro beta j Theta c hj heq
    have hc' := renameInto hc j Theta hj
    rw [graph3Rename] at hc'
    have hp' := renameInto hp j Theta hj
    have hl' := renameInto hl j Theta hj
    rw [graph2Rename] at hp' hl'
    have hg' := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hg'
    have he' := renameInto he j Theta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at he'
    have hgt' := renameInto hgt j Theta hj
    rw [graph1Rename] at hgt'
    have hgs := headTransport Continuation20261116.OriginalConcreteHeadSignature.groundList (types.relabel j)
      (count.relabel j) (suc c) Fin.elim0 heq hgt'
    have ih' := renameInto ih j Theta hj
    rw [belowRawRename] at ih'
    have ha' := renameInto ha j Theta hj
    rw [invariantRename] at ha'
    rw [acceptedRename]
    have has := andIntro (outputTransport OriginalContextInsertion.length (count.relabel j) (suc c)
      ![entries.relabel j] heq (andLeft ha')) (andRight ha')
    exact TypedSpineSuccessorProof.target n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
      (tail.relabel j) c (types.relabel j) (entry.relabel j) (entries.relabel j) (tailEntries.relabel j)
      (gamma.relabel j) (context.relabel j) hc' hp' hl' hg' he' hgs ih' has
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCountCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCountCasesProof
