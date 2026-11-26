module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.DispatchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.RawStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Induction DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem observed (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (xs : Fin 6 → OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw)))
    (ho : Nonempty (Derivation body Delta (observations n H arguments raw xs))) :
    Nonempty (Derivation body Delta (result arguments (xs 3) (xs 5))) := by
  let f : Frame n H arguments body alpha Delta := {
    raw := raw, typ := xs 0, gamma := xs 1, pair := xs 2, size := xs 3, label := xs 4, depth := xs 5
    guard := andLeft (andLeft (andLeft (andLeft ho)))
    typed := andRight (andLeft (andLeft (andLeft ho)))
    bounds := andRight (andLeft (andLeft ho))
    paired := andRight (andLeft ho)
    measured := andRight ho
    ih := ih }
  exact DispatchProof.atFrame f

theorem atMode (n : Nat) (H : Program 1) (arguments : Bool) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw))) :
    Nonempty (Derivation body Delta (AtMode n H arguments raw)) := by
  apply InductionBindingProof.atModeIntro n H arguments raw
  let Theta : List (Formula (alpha ⊕ Fin 6)) := Delta.map (fun q => q.relabel Sum.inl)
  let raw' : OTerm (alpha ⊕ Fin 6) := raw.relabel Sum.inl
  let xs : Fin 6 → OTerm (alpha ⊕ Fin 6) := fun i => .var (.inr i)
  let A := observations n H arguments raw' xs
  have hi : Nonempty (Derivation body Theta (BelowRaw n H raw')) := by
    have h := renameInto ih (Sum.inl : alpha → alpha ⊕ Fin 6) Theta
      (fun q hq => List.mem_map.mpr ⟨q,hq,rfl⟩)
    rwa [InductionSyntaxProof.belowRawRename] at h
  have ha : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := observed n H arguments raw' xs (withHyp hi A) ha
  exact ⟨Derivation.implicationIntroduction d⟩

theorem step (n : Nat) (H : Program 1) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n H raw))) :
    Nonempty (Derivation body Delta (AtRaw n H raw)) :=
  andIntro (atMode n H false raw ih) (atMode n H true raw ih)

theorem allRaw (n : Nat) (H : Program 1) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n H raw)) :=
  InductionBindingProof.rawInduction n H raw (fun _ _ r h => step n H r h)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.RawStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.RawStepProof
