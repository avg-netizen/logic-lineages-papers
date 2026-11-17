module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineExtractedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.ExtractionConsCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineTailProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel)
open OriginalRawSyntaxTransport OriginalUniverseDecoderTransport OriginalUniverseDecoderTransportSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115
open TypedSpineInvariant TypedSpineInvariantSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

theorem sourceAtValue (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (tailValue : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail z)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  have hn := ExtractionConsSupportProof.tailPositive raw typ head tail entries tailValue hc hex ht
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj heq
    have hc' := renameInto hc j Theta hj
    rw [graph3Rename] at hc'
    have hex' := renameInto hex j Theta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hex'
    have hg' := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hg'
    have hgt' := renameInto hgt j Theta hj
    rw [graph1Rename] at hgt'
    have ih' := renameInto ih j Theta hj
    rw [belowRawRename] at ih'
    have ha' := renameInto ha j Theta hj
    rw [acceptedRename] at ha'
    rw [invariantRename]
    have ht' := renameInto ht j Theta hj
    simp only [graph2Rename,zRelabel] at ht'
    have hte := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc tailEntries)
      ![tail.relabel j,z] heq ht'
    exact TypedSpineExtractedProof.source n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
      (tail.relabel j) (count.relabel j) (types.relabel j) (entries.relabel j) tailEntries
      (gamma.relabel j) (context.relabel j) hc' hex' hg' hte hgt' ih' ha'

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  apply programCases ArgumentEntriesRecursor.extract ![tail,z] _
  intro beta j Theta tailValue hj ht
  have hx : (fun i => (![tail,z] i).relabel j) = ![tail.relabel j,z] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ht
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hex'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have hgt' := renameInto hgt j Theta hj
  rw [graph1Rename] at hgt'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [acceptedRename] at ha'
  rw [invariantRename]
  exact sourceAtValue n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) (entries.relabel j)
    (gamma.relabel j) (context.relabel j) hc' hex' hg' hgt' ih' tailValue ht ha'

theorem targetAtValue (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (tailValue : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail z)))
    (ha : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  have hn := ExtractionConsSupportProof.tailPositive raw typ head tail entries tailValue hc hex ht
  apply zeroSuccessorCases Delta tailValue _
  · obtain ⟨hn⟩ := hn
    exact ⟨Derivation.explosion (Derivation.implicationElimination (InternalBetaTotalityProof.addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self))⟩
  · intro beta j Theta tailEntries hj heq
    have hc' := renameInto hc j Theta hj
    rw [graph3Rename] at hc'
    have hex' := renameInto hex j Theta hj
    simp only [graph2Rename,sucRelabel,zRelabel] at hex'
    have hg' := renameInto hg j Theta hj
    simp only [graph1Rename,sucRelabel,zRelabel] at hg'
    have hgt' := renameInto hgt j Theta hj
    rw [graph1Rename] at hgt'
    have ih' := renameInto ih j Theta hj
    rw [belowRawRename] at ih'
    have ha' := renameInto ha j Theta hj
    rw [invariantRename] at ha'
    rw [acceptedRename]
    have ht' := renameInto ht j Theta hj
    simp only [graph2Rename,zRelabel] at ht'
    have hte := outputTransport ArgumentEntriesRecursor.extract (tailValue.relabel j) (suc tailEntries)
      ![tail.relabel j,z] heq ht'
    exact TypedSpineExtractedProof.target n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
      (tail.relabel j) (count.relabel j) (types.relabel j) (entries.relabel j) tailEntries
      (gamma.relabel j) (context.relabel j) hc' hex' hg' hte hgt' ih' ha'

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw typ head tail count types entries gamma context : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 consConstructor raw typ head tail)))
    (hex : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw z)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) tail)))
    (hgt : Nonempty (Derivation body Delta
      (graph1 Continuation20261116.OriginalConcreteHeadSignature.groundList types count)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw)))
    (ha : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  apply programCases ArgumentEntriesRecursor.extract ![tail,z] _
  intro beta j Theta tailValue hj ht
  have hx : (fun i => (![tail,z] i).relabel j) = ![tail.relabel j,z] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at ht
  have hc' := renameInto hc j Theta hj
  rw [graph3Rename] at hc'
  have hex' := renameInto hex j Theta hj
  simp only [graph2Rename,sucRelabel,zRelabel] at hex'
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at hg'
  have hgt' := renameInto hgt j Theta hj
  rw [graph1Rename] at hgt'
  have ih' := renameInto ih j Theta hj
  rw [belowRawRename] at ih'
  have ha' := renameInto ha j Theta hj
  rw [invariantRename] at ha'
  rw [acceptedRename]
  exact targetAtValue n H M W (raw.relabel j) (typ.relabel j) (head.relabel j)
    (tail.relabel j) (count.relabel j) (types.relabel j) (entries.relabel j)
    (gamma.relabel j) (context.relabel j) hc' hex' hg' hgt' ih' tailValue ht ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineTailProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineTailProof
