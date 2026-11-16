module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.DispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.RawStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Induction
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atMode (n : Nat) (arity : Fin n → Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (AtMode n arity H arguments raw)) := by
  apply InductionBindingProof.atModeIntro n arity H arguments raw
  let Theta : List (Formula (alpha ⊕ Fin 11)) := Delta.map (fun q => q.relabel Sum.inl)
  let raw' : OTerm (alpha ⊕ Fin 11) := raw.relabel Sum.inl
  let xs : Fin 11 → OTerm (alpha ⊕ Fin 11) := fun i => .var (.inr i)
  let A := observations n arity H arguments raw' xs
  have hi : Nonempty (Derivation body Theta (BelowRaw n arity H raw')) := by
    have h := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 11) Theta
      (fun q hq => List.mem_map.mpr ⟨q,hq,rfl⟩)
    rwa [InductionSyntaxProof.belowRawRename] at h
  have ha : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := DispatchProof.observed n arity H arguments raw' xs (withHyp hi A) ha
  exact ⟨Derivation.implicationIntroduction d⟩

theorem step (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity H raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity H raw)) :=
  andIntro (atMode n arity H false raw ih) (atMode n arity H true raw ih)

theorem allRaw (n : Nat) (arity : Fin n → Nat) (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n arity H raw)) :=
  InductionBindingProof.rawInduction n arity H raw (fun _ _ r h => step n arity H r h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.RawStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalUniverseFieldsCoverage.RawStepProof
