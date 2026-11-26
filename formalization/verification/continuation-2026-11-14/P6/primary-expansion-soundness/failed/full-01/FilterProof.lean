module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)

open TwoSol20261113.CalibratedPrimary.Membership
open Filter FilterSyntaxProof FilterBindingProof FilterCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem inductionStep (E : Program 3) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw))) :
    Nonempty (Derivation body Delta (AtRaw E raw)) := by
  apply atRawIntro E raw
  let reached : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields E (raw.relabel Sum.inl) reached candidate parameter out
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 4)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have hh : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core E (raw.relabel Sum.inl) reached candidate parameter out (withHyp hb' A)
    ⟨Derivation.conjunctionRight hh⟩
    ⟨Derivation.conjunctionLeft hh⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem filterSoundness : Targets.FilterSoundness := by
  intro E body alpha Delta pool reached parameter filtered candidate hf hm
  exact atRawApply E pool reached candidate parameter filtered
    (rawInduction E pool (fun _ _ r hb => inductionStep E r hb)) (andIntro hf hm)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.FilterProof
