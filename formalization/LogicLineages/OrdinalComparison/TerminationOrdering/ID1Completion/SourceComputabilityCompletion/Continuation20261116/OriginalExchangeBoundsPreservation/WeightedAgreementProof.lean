module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open WeightedAgreement WeightedAgreementSyntaxProof WeightedAgreementBindingProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalTagArithmeticSyntaxProof (eqn)
open Continuation20261115.OriginalArgumentPermutationClosure.CountAgreement

theorem step (weight : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw weight raw))) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) := by
  apply atRawIntro weight raw
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let f := WeightedAgreement.fields weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2)
  let Theta : List (Formula (alpha ⊕ Fin 3)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := WeightedAgreementCoreProof.atRaw weight (raw.relabel Sum.inl) (x 0) (x 1) (x 2)
    (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf)) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (weight : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw weight raw)) :=
  rawInduction weight raw (fun _ _ r ih => step weight r ih)

theorem agreementFold (weight : Program 1) (left right ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (agreement left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls left)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right))) :
    Nonempty (Derivation body Delta (eqn ls rs)) :=
  atRawApply weight left right ls rs (allRaw weight left) (andIntro ha (andIntro hl hr))

theorem permutationFold (weight : Program 1) (left right ls rs : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 Continuation20261114.ArgumentCountComparison.permutation
      (SourceComputabilityFormulaSupportProof.numeral 1) left right)))
    (hl : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) ls left)))
    (hr : Nonempty (Derivation body Delta (graph1 (Fold.weighted weight) rs right))) :
    Nonempty (Derivation body Delta (eqn ls rs)) :=
  agreementFold weight left right ls rs
    (Continuation20261115.OriginalArgumentPermutationClosure.AllQueryProof.permutationAgreement left right ha) hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.WeightedAgreementProof
