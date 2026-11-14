module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.FilterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Induction InductionSyntaxProof InductionBindingProof CoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem inductionStep (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw n arity raw))) :
    Nonempty (Derivation body Delta (AtRaw n arity raw)) := by
  apply atRawIntro n arity raw
  let symbols : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let types : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields n arity (raw.relabel Sum.inl) symbols candidate types out value
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 5)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have hh : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core n arity (raw.relabel Sum.inl) symbols candidate types out value (withHyp hb' A)
    ⟨Derivation.conjunctionRight hh⟩ ⟨Derivation.conjunctionLeft hh⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem internalFilter : Targets.InternalFilter := by
  intro n arity body alpha Delta raw out needle symbols types value hf hw
  have h := atRawApply n arity raw symbols needle types out value
    (rawInduction n arity raw (fun _ _ r hb => inductionStep n arity r hb)) (andIntro hf hw)
  exact ⟨StepSupportProof.forward raw symbols needle types out value h,
    StepSupportProof.backward raw symbols needle types out value h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.FilterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.FilterProof
