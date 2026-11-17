module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalUniverseDecoderTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SpineInvariant SpineInvariantSyntaxProof SpineInvariantBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem step (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H M W raw))) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) := by
  apply atRawIntro n H M W raw
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  let R := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let D := domain n R (x 1)
  let A := Accepted H M W true (x 0) R (x 2) (x 3)
  let I := EntryFacts.allGood H M W (x 1) (x 2) (x 3)
  let Theta := D :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hd : Nonempty (Derivation body Theta D) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih Sum.inl Theta
    (fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowRawRename] at ihj
  have hs : Nonempty (Derivation body Theta (A.imp I)) := by
    obtain ⟨h⟩ := SpineCoreProof.source n H M W R (x 0) (x 1) (x 2) (x 3)
      (withHyp hd A) (withHyp ihj A) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  let P := Plain H (x 0) R (x 2) ⊓ I
  have ht : Nonempty (Derivation body Theta (P.imp A)) := by
    obtain ⟨h⟩ := SpineCoreProof.target n H M W R (x 0) (x 1) (x 2) (x 3)
      (withHyp hd P) (withHyp ihj P) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨h⟩ := andIntro hs ht
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allRaw (n : Nat) (H : Program 1) (M W : Program 2) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n H M W raw)) :=
  rawInduction n H M W raw (fun _ _ r ih => step n H M W r ih)

theorem source (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw entries)))
    (ha : Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context))) :
    Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context)) := by
  obtain ⟨hr⟩ := atRawApply n H M W raw types entries gamma context (allRaw n H M W raw)
  obtain ⟨hd⟩ := hd
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft (Derivation.implicationElimination hr hd)) ha⟩

theorem target (n : Nat) (H : Program 1) (M W : Program 2)
    (raw types entries gamma context : OTerm alpha)
    (hd : Nonempty (Derivation body Delta (domain n raw entries)))
    (hp : Nonempty (Derivation body Delta (Plain H types raw gamma)))
    (hi : Nonempty (Derivation body Delta (EntryFacts.allGood H M W entries gamma context))) :
    Nonempty (Derivation body Delta (Accepted H M W true types raw gamma context)) := by
  obtain ⟨hr⟩ := atRawApply n H M W raw types entries gamma context (allRaw n H M W raw)
  obtain ⟨hd⟩ := hd
  obtain ⟨hi⟩ := InternalApplicationStepPeelSupportProof.andIntro hp hi
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight (Derivation.implicationElimination hr hd)) hi⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalFilteredHeadMoveUniverse.SpineInvariantProof
