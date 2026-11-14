module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyProof
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
open Any AnySyntaxProof AnyBindingProof AnyCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem inductionStep (E : Program 3) (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw E raw))) :
    Nonempty (Derivation body Delta (AtRaw E raw)) := by
  apply atRawIntro E raw
  let candidate : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := fields E (raw.relabel Sum.inl) candidate parameter
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 2)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  obtain ⟨h⟩ := core E (raw.relabel Sum.inl) candidate parameter (withHyp hb' A)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem anyWitness : Targets.AnyWitness := by
  intro E body alpha Delta reached candidate parameter ha
  exact atRawApply E reached candidate parameter
    (rawInduction E reached (fun _ _ r hb => inductionStep E r hb)) ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AnyProof
