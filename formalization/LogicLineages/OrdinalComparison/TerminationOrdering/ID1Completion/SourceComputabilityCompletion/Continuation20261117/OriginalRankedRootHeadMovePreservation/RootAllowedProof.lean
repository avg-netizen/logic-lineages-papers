module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.HeadClassValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardObservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardChoiceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootAllowedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm trans)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115
open Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineAuxiliary.GuardChoiceProof (orConclusion andFirst)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem exclude (actual k : Nat) (hne : actual ≠ k) (tag : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (eqn tag (numeral actual)))) :
    Nonempty (Derivation body Delta ((eqn tag (numeral k)).imp psi)) := by
  obtain ⟨hn⟩ := OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe
    (body := body) (Delta := eqn tag (numeral k) :: Delta) actual k hne
  rw [equalEqn] at hn
  obtain ⟨ht⟩ := withHyp ht (eqn tag (numeral k))
  have he := trans (symm ht) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (Derivation.implicationElimination hn he))⟩

theorem ordinary (n : Nat) (tag payload first second head : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (eqn tag (numeral 4))))
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) first)) := by
  let psi := graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (suc z) first
  have h4 : Nonempty (Derivation body Delta ((eqn tag (numeral 4) ⊓ psi).imp psi)) :=
    ⟨Derivation.implicationIntroduction (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  have hd : Nonempty (Derivation body Delta ((OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head).imp psi)) :=
    orConclusion (orConclusion (exclude 4 0 (by decide) tag psi ht) (exclude 4 3 (by decide) tag psi ht))
      (orConclusion (andFirst (exclude 4 1 (by decide) tag psi ht))
        (orConclusion (andFirst (orConclusion (exclude 4 2 (by decide) tag psi ht) (exclude 4 7 (by decide) tag psi ht)))
          (orConclusion h4 (orConclusion (andFirst (exclude 4 5 (by decide) tag psi ht))
            (andFirst (exclude 4 6 (by decide) tag psi ht))))))
  exact ⟨Derivation.implicationElimination (Classical.choice hd) (Classical.choice ha)⟩

theorem numbered (n : Nat) (tag payload first second head : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (eqn tag (numeral 5))))
    (ha : Nonempty (Derivation body Delta (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓
      graph1 (OriginalCodeValidityGuard.check n) (suc z) first)) := by
  let psi := graph1 (OriginalHeadDecoderValidity.check n) (suc z) head ⊓ graph1 (OriginalCodeValidityGuard.check n) (suc z) first
  have h5 : Nonempty (Derivation body Delta ((eqn tag (numeral 5) ⊓
      (psi ⊓ graph1 (OriginalCodeValidityGuard.check n) (suc z) second)).imp psi)) :=
    ⟨Derivation.implicationIntroduction (Derivation.conjunctionLeft
      (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)))⟩
  have hd : Nonempty (Derivation body Delta ((OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head).imp psi)) :=
    orConclusion (orConclusion (exclude 5 0 (by decide) tag psi ht) (exclude 5 3 (by decide) tag psi ht))
      (orConclusion (andFirst (exclude 5 1 (by decide) tag psi ht))
        (orConclusion (andFirst (orConclusion (exclude 5 2 (by decide) tag psi ht) (exclude 5 7 (by decide) tag psi ht)))
          (orConclusion (andFirst (exclude 5 4 (by decide) tag psi ht))
            (orConclusion h5 (andFirst (exclude 5 6 (by decide) tag psi ht))))))
  exact ⟨Derivation.implicationElimination (Classical.choice hd) (Classical.choice ha)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootAllowedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRankedRootHeadMovePreservation.RootAllowedProof
