module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryProof
open Continuation20261116 Continuation20261116.OriginalExchangeBoundsPreservation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Entry EntrySyntaxProof EntryBindingProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open Continuation20261114 Continuation20261115

theorem step (n : Nat) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n raw))) :
    Nonempty (Derivation body Delta (AtRaw n raw)) := by
  apply atRawIntro n raw
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  let f := Entry.fields n (raw.relabel Sum.inl) (x 0) (x 1) (x 2)
  let Theta : List (Formula (alpha ⊕ Fin 3)) := f :: Delta.map (fun q => q.relabel Sum.inl)
  have hf : Nonempty (Derivation body Theta f) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hi : ∀ q ∈ Delta, q.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
    intro q hq; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ihj := InternalGraphCompositionFunctionalityProof.renameInto ih Sum.inl Theta hi
  rw [belowRawRename] at ihj
  obtain ⟨d⟩ := EntryCoreProof.atRaw n (raw.relabel Sum.inl) (x 0) (x 1) (x 2)
    (andLeft hf) (andLeft (andRight hf)) (andRight (andRight hf)) ihj
  exact ⟨Derivation.implicationIntroduction d⟩

theorem allRaw (n : Nat) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n raw)) :=
  rawInduction n raw (fun _ _ r ih => step n r ih)

theorem actualRankCode (n : Nat) (raw param entries value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (hf : Nonempty (Derivation body Delta (graph1 (Fold.weighted rankWeight) value entries))) :
    Nonempty (Derivation body Delta (graph1 rawRankCode value raw)) :=
  atRawApply n raw param entries value (allRaw n raw) (andIntro hg (andIntro he hf))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.EntryProof
