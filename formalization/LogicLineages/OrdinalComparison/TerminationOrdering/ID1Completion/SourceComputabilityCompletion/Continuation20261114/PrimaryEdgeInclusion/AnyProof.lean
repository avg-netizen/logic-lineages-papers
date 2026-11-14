module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyProof
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
  let source : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let candidate : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields E (raw.relabel Sum.inl) source candidate parameter
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 3)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have ha : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph2 contains (suc z) (raw.relabel Sum.inl) source)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hm : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph3 E (suc z) source candidate parameter)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨h⟩ := core E (raw.relabel Sum.inl) source candidate parameter (withHyp hb' A) hm ha
  exact ⟨Derivation.implicationIntroduction h⟩

theorem anyIntroduction : Targets.AnyIntroduction := by
  intro E body alpha Delta reached source candidate parameter hm he
  exact atRawApply E reached source candidate parameter
    (rawInduction E reached (fun _ _ r hb => inductionStep E r hb)) (andIntro hm he)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AnyProof
