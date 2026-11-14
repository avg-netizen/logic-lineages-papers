module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationValidityStackAppend (append)
open TwoSol20261113.CalibratedPrimary.Membership
open Append AppendSyntaxProof AppendBindingProof AppendCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem inductionStep (raw : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let suffix : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let needle : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields (raw.relabel Sum.inl) suffix out needle
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 3)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have ha : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph2 append out (raw.relabel Sum.inl) suffix)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hm : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl))
      (graph2 contains (suc z) out needle)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨h⟩ := core (raw.relabel Sum.inl) suffix out needle (withHyp hb' A) ha hm
  exact ⟨Derivation.implicationIntroduction h⟩

theorem appendPreservation (raw suffix out needle : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 append out raw suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (suc z) out needle))) :
    Nonempty (Derivation body Delta (result raw suffix needle)) :=
  atRawApply raw suffix out needle
    (rawInduction raw (fun _ _ r hb => inductionStep r hb)) (andIntro ha hm)

theorem appendSoundness : Targets.AppendSoundness := by
  intro body alpha Delta left right out needle ha hm
  exact appendPreservation left right out needle ha hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansionSoundness.AppendProof
