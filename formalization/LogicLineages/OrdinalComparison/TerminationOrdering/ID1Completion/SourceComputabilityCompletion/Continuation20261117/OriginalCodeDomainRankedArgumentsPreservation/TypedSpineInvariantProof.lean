module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TypedSpineInvariant TypedSpineInvariantSyntaxProof TypedSpineInvariantBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem step (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw))) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) := by
  apply atRawIntro n H M W raw
  let x : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  let R := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
  let D := domain n R (x 0) (x 1) (x 2)
  let A := Accepted H M W true (x 1) R (x 3) (x 4)
  let I := invariant H M W (x 0) (x 2) (x 3) (x 4)
  let Theta := D :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  have hd : Nonempty (Derivation body Theta D) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih Sum.inl Theta
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  have hs : Nonempty (Derivation body Theta (A.imp I)) := by
    obtain ⟨h⟩ := TypedSpineCoreProof.source n H M W R (x 0) (x 1) (x 2) (x 3) (x 4)
      (withHyp hd A) (withHyp ihj A) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  have ht : Nonempty (Derivation body Theta (I.imp A)) := by
    obtain ⟨h⟩ := TypedSpineCoreProof.target n H M W R (x 0) (x 1) (x 2) (x 3) (x 4)
      (withHyp hd I) (withHyp ihj I) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨h⟩ := andIntro hs ht
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) :=
  rawInduction n H M W raw (fun _ _ r ih => step n H M W r ih)

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw count types entries)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (invariant H M W count entries gamma context)) := by
  obtain ⟨hr⟩ := atRawApply n H M W raw count types entries gamma context (allRaw n H M W raw)
  obtain ⟨hd⟩ := hd
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination hr hd)) ha⟩

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw count types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw count types entries)))
    (hi : Nonempty (Derivation body Delta (invariant H M W count entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  obtain ⟨hr⟩ := atRawApply n H M W raw count types entries gamma context (allRaw n H M W raw)
  obtain ⟨hd⟩ := hd
  obtain ⟨hi⟩ := hi
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight (Derivation.implicationElimination hr hd)) hi⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineInvariantProof
