module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ExchangeStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Induction InductionSyntaxProof MatrixSyntaxProof InductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem modeStep (n : Nat) (arity : Fin n → Nat) (arguments : Bool) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity raw))) :
    Nonempty (Derivation body Delta (AtMode n arity arguments raw)) := by
  apply atModeIntro n arity arguments raw
  let x : Fin 8 → OTerm (alpha ⊕ Fin 8) := fun i => .var (.inr i)
  let R := raw.relabel (Sum.inl : alpha → alpha ⊕ Fin 8)
  let D := environment n (x 3) (x 4) (x 5) (x 6) ⊓ edge n arity R (x 1) (x 7) (x 6)
  let A := accepted n arity arguments (x 0) R (x 2) (x 3) ⊓ plain n arity arguments (x 0) (x 1) (x 2)
  let Theta := D :: Delta.map (fun q => q.relabel (Sum.inl : alpha → alpha ⊕ Fin 8))
  have hd : Nonempty (Derivation body Theta D) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ha : Nonempty (Derivation body (A :: Theta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ihj := renameInto ih Sum.inl (A :: Theta)
    (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)))
  rw [belowRawRename] at ihj
  have hd' := withHyp hd A
  obtain ⟨h⟩ := ExchangeStepProof.preserved n arity arguments R (x 1) (x 7) (x 6)
    (x 0) (x 2) (x 3) (x 4) (x 5) (andLeft hd') (andRight hd') ihj (andLeft ha) (andRight ha)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem step (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  andIntro (modeStep n arity false raw ih) (modeStep n arity true raw ih)

theorem allRaw (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) :=
  rawInduction n arity raw (fun _ _ r ih => step n arity r ih)

theorem preserved (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (source target node window typ gamma context symbols types : OTerm alpha)
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity source target node window)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ source gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ target gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ target gamma context)) := by
  obtain ⟨h⟩ := atModeApply n arity arguments source typ target gamma context symbols types window node
    (atRawMode n arity arguments source (allRaw n arity source))
  obtain ⟨he⟩ := andIntro henv hedge
  obtain ⟨ht⟩ := andIntro ha hp
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h he) ht⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.InductionProof
