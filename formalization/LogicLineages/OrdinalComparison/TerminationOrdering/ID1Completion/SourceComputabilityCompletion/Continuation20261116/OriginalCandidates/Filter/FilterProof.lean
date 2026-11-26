module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.FilterProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Induction InductionSyntaxProof InductionBindingProof CoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem inductionStep (H : Program 1) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw H raw))) :
    Nonempty (Derivation body Delta (AtRaw H raw)) := by
  apply atRawIntro H raw
  let symbols : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let types : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields H (raw.relabel Sum.inl) symbols candidate types out value
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 5)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have hh : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core H (raw.relabel Sum.inl) symbols candidate types out value (withHyp hb' A)
    ⟨Derivation.conjunctionRight hh⟩ ⟨Derivation.conjunctionLeft hh⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem internalFilter : Targets.InternalFilter := by
  intro H body alpha Delta raw out needle symbols types value hf hw
  have h := atRawApply H raw symbols needle types out value
    (rawInduction H raw (fun _ _ r hb => inductionStep H r hb)) (andIntro hf hw)
  exact ⟨StepSupportProof.forward raw symbols needle types out value h,
    StepSupportProof.backward raw symbols needle types out value h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.FilterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalCandidates.Filter.FilterProof
