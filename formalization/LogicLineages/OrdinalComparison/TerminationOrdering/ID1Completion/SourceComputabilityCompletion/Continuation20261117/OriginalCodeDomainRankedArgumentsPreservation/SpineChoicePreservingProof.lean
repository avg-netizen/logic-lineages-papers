module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineCaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114 Continuation20261115
open SpineAuxiliary.GuardChoiceProof (orConclusion andFirst)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem orAndConclusion {A B C psi : Formula alpha}
    (ha : Nonempty (Derivation body Delta ((A ⊓ C).imp psi)))
    (hb : Nonempty (Derivation body Delta ((B ⊓ C).imp psi))) :
    Nonempty (Derivation body Delta (((A ⊔ B) ⊓ C).imp psi)) := by
  let F := (A ⊔ B) ⊓ C
  have hcase (X : Formula alpha) (hx : Nonempty (Derivation body Delta ((X ⊓ C).imp psi))) :
      Nonempty (Derivation body (F :: Delta) (X.imp psi)) := by
    have hf : Nonempty (Derivation body (X :: F :: Delta) F) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    obtain ⟨hxc⟩ := andIntro (show Nonempty (Derivation body (X :: F :: Delta) X) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩) (andRight hf)
    obtain ⟨hx⟩ := withHyp (withHyp hx F) X
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hx hxc)⟩
  have hf : Nonempty (Derivation body (F :: Delta) F) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hab⟩ := andLeft hf
  exact ⟨Derivation.implicationIntroduction
    (InternalBetaTotalityProof.disjunctionElimination hab (Classical.choice (hcase A ha)) (Classical.choice (hcase B hb)))⟩

theorem eliminate (n : Nat) (raw param entries tag payload first second head : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (ha : Nonempty (Derivation body Delta
      (OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head)))
    (hnil : Nonempty (Derivation body Delta
      (((eqn tag (numeral 6)) ⊓ eqn payload z).imp psi)))
    (hcons : Nonempty (Derivation body Delta
      ((eqn tag (numeral 7) ⊓ (graph1 (OriginalCodeValidityGuard.check n) (suc z) first ⊓
        graph1 (OriginalCodeValidityGuard.check n) (suc z) second)).imp psi))) :
    Nonempty (Derivation body Delta psi) := by
  have other : ∀ k : Nat, k ≠ 6 → k ≠ 7 →
      Nonempty (Derivation body Delta ((eqn tag (numeral k)).imp psi)) := by
    intro k h6 h7
    have ht := SpineAuxiliary.GuardPairProof.tagLiteral raw tag payload k
      (withHyp hp (eqn tag (numeral k))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := SpineAuxiliary.EntryNonSpineProof.impossible k h6 h7 raw param entries psi ht (withHyp he _)
    exact ⟨Derivation.implicationIntroduction d⟩
  have hd : Nonempty (Derivation body Delta
      ((OriginalCodeValidityConstructors.Targets.allowed n tag payload first second head).imp psi)) :=
    orConclusion (orConclusion (other 0 (by decide) (by decide)) (other 3 (by decide) (by decide)))
      (orConclusion (andFirst (other 1 (by decide) (by decide)))
        (orConclusion (orAndConclusion (andFirst (other 2 (by decide) (by decide))) hcons)
          (orConclusion (andFirst (other 4 (by decide) (by decide)))
            (orConclusion (andFirst (other 5 (by decide) (by decide))) hnil))))
  exact ⟨Derivation.implicationElimination (Classical.choice hd) (Classical.choice ha)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.SpineChoicePreservingProof
