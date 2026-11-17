module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardPairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.EntryNonSpineProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineCaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem eliminate (n : Nat) (raw param entries tag payload first second head : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (ha : Nonempty (Derivation body Delta
      (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (hnil : Nonempty (Derivation body Delta
      (((eqn tag (numeral 6)) ⊓ eqn payload z).imp psi)))
    (hcons : Nonempty (Derivation body Delta ((eqn tag (numeral 7)).imp psi))) :
    Nonempty (Derivation body Delta psi) := by
  have other : ∀ k : Nat, k ≠ 6 → k ≠ 7 →
      Nonempty (Derivation body Delta ((eqn tag (numeral k)).imp psi)) := by
    intro k h6 h7
    have ht := SpineAuxiliary.GuardPairProof.tagLiteral raw tag payload k
      (withHyp hp (eqn tag (numeral k))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := SpineAuxiliary.EntryNonSpineProof.impossible k h6 h7 raw param entries psi ht (withHyp he _)
    exact ⟨Derivation.implicationIntroduction d⟩
  exact SpineAuxiliary.GuardChoiceProof.eliminate n tag payload first second head psi ha
    (other 0 (by decide) (by decide)) (other 1 (by decide) (by decide))
    (other 2 (by decide) (by decide)) (other 3 (by decide) (by decide))
    (other 4 (by decide) (by decide)) (other 5 (by decide) (by decide)) hnil hcons
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineCaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineCaseProof
