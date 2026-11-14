module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open CompareDefinitions.Compare CompareSyntaxProof CompareBindingProof CompareCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem inductionStep (raw : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let left : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let right : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let leftCount : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let rightCount : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let candidate : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields (raw.relabel Sum.inl) left right leftCount rightCount candidate
  have hrow' := renameInto hrow (Sum.inl : alpha → alpha ⊕ Fin 5)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hrow'
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core (raw.relabel Sum.inl) left right leftCount rightCount candidate (withHyp hrow' A)
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight h)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight h)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem comparison (raw left right leftCount rightCount candidate : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (PrimaryMonotonicity.included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right))) :
    Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) :=
  atRawApply raw left right leftCount rightCount candidate
    (rawInduction raw (fun _ _ raw hrow => inductionStep raw hrow)) (andIntro hi (andIntro hl hr))

theorem internalAntitone : Targets.InternalAntitone := by
  intro body alpha Delta pool left right leftCount rightCount hi hl hr
  obtain ⟨h⟩ := comparison pool left right leftCount rightCount z hi hl hr
  exact ⟨Derivation.conjunctionLeft h⟩

theorem internalStrictDecrease : Targets.InternalStrictDecrease := by
  intro body alpha Delta pool left right leftCount rightCount candidate hi hl hr hp hn hm
  obtain ⟨h⟩ := comparison pool left right leftCount rightCount candidate hi hl hr
  obtain ⟨hnew⟩ := andIntro hp (andIntro hn hm)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h) hnew⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.CompareProof
