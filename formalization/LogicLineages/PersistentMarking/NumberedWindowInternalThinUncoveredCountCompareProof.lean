module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountMemberProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareCoreProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open ID1Completion.InternalCalculus (Formula Derivation instantiate weaken)
open ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraph (equal)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof
open LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalScratchInclusionThinProof (included includedRename includedSubst)
open NumberedWindowInternalSparseScratchMembership (scratchMember)

open NumberedWindowInternalThinUncoveredCountCompareDefinitions.Compare NumberedWindowInternalThinUncoveredCountCompareSyntaxProof NumberedWindowInternalThinUncoveredCountCompareBindingProof NumberedWindowInternalThinUncoveredCountCompareCoreProof
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem inductionStep (raw : OrdinaryArithmetic.Term alpha)
    (hrow : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let left : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 0)
  let right : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 1)
  let leftCount : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 2)
  let rightCount : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 3)
  let candidate : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 4)
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

theorem comparison (raw left right leftCount rightCount candidate : OrdinaryArithmetic.Term alpha)
    (hi : Nonempty (Derivation body Delta (included left right)))
    (hl : Nonempty (Derivation body Delta (graph2 count leftCount raw left)))
    (hr : Nonempty (Derivation body Delta (graph2 count rightCount raw right))) :
    Nonempty (Derivation body Delta (result raw left right leftCount rightCount candidate)) :=
  atRawApply raw left right leftCount rightCount candidate
    (rawInduction raw (fun _ _ raw hrow => inductionStep raw hrow)) (andIntro hi (andIntro hl hr))

theorem internalAntitone : NumberedWindowInternalThinUncoveredCountTargets.InternalAntitone := by
  intro body alpha Delta pool left right leftCount rightCount hi hl hr
  obtain ⟨h⟩ := comparison pool left right leftCount rightCount z hi hl hr
  exact ⟨Derivation.conjunctionLeft h⟩

theorem internalStrictDecrease : NumberedWindowInternalThinUncoveredCountTargets.InternalStrictDecrease := by
  intro body alpha Delta pool left right leftCount rightCount candidate hi hl hr hp hn hm
  obtain ⟨h⟩ := comparison pool left right leftCount rightCount candidate hi hl hr
  obtain ⟨hnew⟩ := andIntro hp (andIntro hn hm)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h) hnew⟩

#print axioms internalAntitone
#print axioms internalStrictDecrease
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountCompareProof
