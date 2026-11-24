module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculusDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceIntroductionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundCoreProof
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundProof
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open FirstOrder FirstOrder.Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators (Positive)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCalculus (Derivation Formula)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraph
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
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion
open NumberedWindowInternalThinUncoveredCount
open NumberedWindowInternalThinUncoveredCountOrderProof
open NumberedWindowInternalSparseScratchMembership (scratchMember)

open NumberedWindowInternalThinUncoveredCountBoundDefinitions.Bound NumberedWindowInternalThinUncoveredCountBoundSyntaxProof NumberedWindowInternalThinUncoveredCountBoundBindingProof NumberedWindowInternalThinUncoveredCountBoundCoreProof
open OriginalContextInsertion
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem inductionStep (raw : OrdinaryArithmetic.Term alpha)
    (hb : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (AtRaw raw)) := by
  apply atRawIntro raw
  let reached : OrdinaryArithmetic.Term (alpha ⊕ Fin 3) := .var (.inr 0)
  let remaining : OrdinaryArithmetic.Term (alpha ⊕ Fin 3) := .var (.inr 1)
  let size : OrdinaryArithmetic.Term (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields (raw.relabel Sum.inl) reached remaining size
  have hb' := renameInto hb (Sum.inl : alpha → alpha ⊕ Fin 3)
    (Delta.map (fun p => p.relabel Sum.inl)) (by intro p hp; exact List.mem_map.mpr ⟨p,hp,rfl⟩)
  rw [belowRawRename] at hb'
  have h : Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A :=
    Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := core (raw.relabel Sum.inl) reached remaining size (withHyp hb' A)
    ⟨Derivation.conjunctionLeft h⟩ ⟨Derivation.conjunctionRight h⟩
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Actual original numeric-list length bounds the count, with no
semantic list or host membership hypothesis. -/
theorem internalBound (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (pool reached remaining size : OrdinaryArithmetic.Term alpha)
    (ho : Nonempty (Derivation body Delta (graph2 count remaining pool reached)))
    (hl : Nonempty (Derivation body Delta (lengthGraph size pool))) :
    Nonempty (Derivation body Delta (bounded remaining size)) :=
  atRawApply pool reached remaining size
    (rawInduction pool (fun _ _ raw hb => inductionStep raw hb)) (andIntro ho hl)

/-- The round fuel really is the very same literal original list length. -/
theorem exact_PhysicalPoolLength :
    NumberedWindowInternalSparseDirectedRounds.poolLength = OriginalContextInsertion.length := rfl

theorem exact_PhysicalUncoveredCountBound (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (pool reached remaining size : OrdinaryArithmetic.Term alpha)
    (ho : Nonempty (Derivation body Delta (graph2 count remaining pool reached)))
    (hl : Nonempty (Derivation body Delta
      (programGraph NumberedWindowInternalSparseDirectedRounds.poolLength size ![pool]))) :
    Nonempty (Derivation body Delta (bounded remaining size)) := by
  rw [exact_PhysicalPoolLength] at hl
  exact internalBound body alpha Delta pool reached remaining size ho hl

#print axioms exact_PhysicalPoolLength
#print axioms exact_PhysicalUncoveredCountBound
#print axioms internalBound
end LogicLineages.PersistentMarking.NumberedWindowInternalThinUncoveredCountBoundProof
