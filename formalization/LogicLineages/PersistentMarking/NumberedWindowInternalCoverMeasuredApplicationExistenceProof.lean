module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof (auxiliaryTermRename)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof (exact_FullyMeasuredClassApplication)
open NumberedWindowInternalCoverMeasuredApplicationExistenceTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)}

theorem exact_MeasuredApplicationExists : ExactMeasuredApplicationExists := by
  intro V TV M M0 B T base s body α Γ ctx dom cod fn arg P W Xm syn ty function argument
  have formed := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ
    ctx dom cod fn arg syn ty function argument
  obtain ⟨report⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V Xm s body α Γ
    ctx cod (auxiliaryTerm dom cod fn arg) formed
  exact ⟨Derivation.conjunctionRight report⟩

/-- Eliminate the right application's existential least before applying the
already checked class law. No chosen witness escapes its original binder. -/
private theorem availableClassLeast
    (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    {α : Type} (Γ : List (Formula α)) (ctx dom cod f g x arg m : OTerm α) :
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let Xm := guardedExchange P.cover s
      (thinPairedExchange (measuredExchange (selectedMeasure P.R) (directedX base P.V)))
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) f x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx (rawCons dom cod) g x)) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod f arg) m)) →
    Nonempty (Derivation body Γ (hasLeast P.cover Xm W s ctx cod (auxiliaryTerm dom cod g arg))) →
    Nonempty (Derivation body Γ (leastGraph P.cover Xm W s ctx cod (auxiliaryTerm dom cod g arg) m)) := by
  intro P W Xm syn ty argument lf lg af hg
  apply casesLeast P.cover Xm W s ctx cod (auxiliaryTerm dom cod g arg) _ hg
  intro β j Δ m' keep ag
  rw [leastRename,auxiliaryTermRename]
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  have lf' := renameInto lf j Δ keep
  have lg' := renameInto lg j Δ keep
  rw [leastRename,rawConsRename] at lf' lg'
  have af' := renameInto af j Δ keep
  rw [leastRename,auxiliaryTermRename] at af'
  rw [auxiliaryTermRename] at ag
  exact exact_FullyMeasuredClassApplication V TV M M0 B T base s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j)
    (x.relabel j) (arg.relabel j) (m.relabel j) m' syn' ty' argument' lf' lg' af' ag

theorem exact_MeasuredClassApplicationExists : ExactMeasuredClassApplicationExists := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g x arg goal P W Xm a b
    syn ty functionF functionG argument lf lg finish
  have ha := exact_MeasuredApplicationExists V TV M M0 B T base s body α Γ
    ctx dom cod f arg syn ty functionF argument
  have hb := exact_MeasuredApplicationExists V TV M M0 B T base s body α Γ
    ctx dom cod g arg syn ty functionG argument
  apply casesLeast P.cover Xm W s ctx cod a goal ha
  intro β j Δ m keep la
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  have lf' := renameInto lf j Δ keep
  have lg' := renameInto lg j Δ keep
  rw [leastRename,rawConsRename] at lf' lg'
  have hb' := renameInto hb j Δ keep
  rw [hasRename,auxiliaryTermRename] at hb'
  have la' : Nonempty (Derivation body Δ
      (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j)
        (auxiliaryTerm (dom.relabel j) (cod.relabel j) (f.relabel j) (arg.relabel j)) m)) := by
    rw [← auxiliaryTermRename]
    exact la
  have lb := availableClassLeast (body := body) V TV M M0 B T base s Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j)
    (x.relabel j) (arg.relabel j) m syn' ty' argument' lf' lg' la' hb'
  rw [← auxiliaryTermRename] at lb
  exact finish β j Δ m keep la lb

#print axioms exact_MeasuredApplicationExists
#print axioms exact_MeasuredClassApplicationExists
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationExistenceProof
