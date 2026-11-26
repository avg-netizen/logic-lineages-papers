module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsTaggedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open EntryBounds
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115

theorem atAllowed (n : Nat) (raw param entries value tag payload first second head : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted (Fold.entryWeight n)) value entries)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw)))
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) value raw)) := by
  let psi := graph1 (OriginalCodeBoundsRecursion.bounds n) value raw
  have other : ∀ k : Nat, k ≠ 6 → k ≠ 7 → Nonempty (Derivation body Delta ((eqn tag (numeral k)).imp psi)) := by
    intro k h6 h7
    have htag := OriginalEnumerationMembership.GuardPairProof.tagLiteral raw tag payload k (withHyp hp (eqn tag (numeral k)))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := EntryNonSpineProof.impossible k h6 h7 raw param entries psi htag (withHyp he _)
    exact ⟨Derivation.implicationIntroduction d⟩
  have hnil : Nonempty (Derivation body Delta (((eqn tag (numeral 6)) ⊓ eqn payload z).imp psi)) := by
    let clause := (eqn tag (numeral 6)) ⊓ eqn payload z
    have hh : Nonempty (Derivation body (clause :: Delta) clause) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hc := OriginalEnumerationMembership.GuardPairProof.nil raw tag payload (withHyp hp clause) (andLeft hh) (andRight hh)
    obtain ⟨d⟩ := EntryBoundsNilProof.nil n raw param entries value hc (withHyp hg clause) (withHyp he clause) (withHyp hf clause)
    exact ⟨Derivation.implicationIntroduction d⟩
  have hcons : Nonempty (Derivation body Delta ((eqn tag (numeral 7)).imp psi)) := by
    have htag := OriginalEnumerationMembership.GuardPairProof.tagLiteral raw tag payload 7 (withHyp hp (eqn tag (numeral 7)))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := EntryBoundsTaggedProof.consTag n raw param entries value htag (withHyp hg _) (withHyp he _) (withHyp hf _) (withHyp ih _)
    exact ⟨Derivation.implicationIntroduction d⟩
  exact OriginalEnumerationMembership.GuardChoiceProof.eliminate n tag payload first second head psi ha
    (other 0 (by decide) (by decide)) (other 1 (by decide) (by decide))
    (other 2 (by decide) (by decide)) (other 3 (by decide) (by decide))
    (other 4 (by decide) (by decide)) (other 5 (by decide) (by decide)) hnil hcons
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsDispatchProof
