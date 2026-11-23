module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedAuxMeasureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSharedRecursionTargets (sharedMeasure)
open NumberedWindowInternalCoverSharedAuxMeasureProof (exact_OpenCoverSharedAuxMeasureParent)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets (ActualAuxCoverDomainInputs)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesProof (exact_OpenCoverAuxLeastAtKnownScopes)
open NumberedWindowInternalCoverAuxLeastFromSeedLeastsTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem seedsRename {β : Type} (V M : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    {ctx dom cod fn arg fx ax : OTerm α}
    (i : ActualAuxSeedInputs V M X W s body Γ ctx dom cod fn arg fx ax)
    (j : α → β) (Δ : List (Formula β)) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ) :
    ActualAuxSeedInputs V M X W s body Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (fn.relabel j) (arg.relabel j) (fx.relabel j) (ax.relabel j) := by
  constructor
  · simpa only [windowRename,appAuxRename] using renameInto i.parsed j Δ keep
  · simpa only [leastRename,rawConsRename] using renameInto i.functionLeast j Δ keep
  · simpa only [leastRename] using renameInto i.argumentLeast j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto i.functionValid j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto i.argumentValid j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel,appAuxRename] using renameInto i.parentValid j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto i.domainMember j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto i.codomainMember j Δ keep

private theorem withParentMeasure (V M : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx dom cod fn arg fx ax p : OTerm α)
    (i : ActualAuxSeedInputs V M X W s body Γ ctx dom cod fn arg fx ax)
    (measured : Nonempty (Derivation body Γ (unary (sharedMeasure M) p (auxiliaryTerm dom cod fn arg)))) :
    Nonempty (Derivation body Γ (hasLeast (selectedCover V (sharedMeasure M)) X W s ctx cod
      (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverSharedAuxMeasureParent M body α Γ dom cod fn arg p _ measured
  intro β j Δ old mf ma df da bf ba keep row
  rw [hasRename,appAuxRename]
  have i' := seedsRename V M X W s i j Δ keep
  have paid : ActualAuxCoverDomainInputs V (sharedMeasure M) X W s body Δ (ctx.relabel j) (dom.relabel j)
      (cod.relabel j) (fn.relabel j) (arg.relabel j) (fx.relabel j) (ax.relabel j) (p.relabel j)
      mf ma df bf da ba :=
    ⟨i'.parsed,i'.functionLeast,i'.argumentLeast,i'.functionValid,i'.argumentValid,row.fnData.selected,
      row.argData.selected,row.fnData.coordinates,row.argData.coordinates,i'.parentValid,row.selectedParent,
      row.parentBounds,i'.domainMember,i'.codomainMember⟩
  exact exact_OpenCoverAuxLeastAtKnownScopes V (sharedMeasure M) X W s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) (fx.relabel j) (ax.relabel j)
    (p.relabel j) mf ma df bf da ba paid

theorem exact_OpenCoverAuxLeastFromSeedLeasts : ExactOpenCoverAuxLeastFromSeedLeasts := by
  intro V M X W s body α Γ ctx dom cod fn arg fx ax i
  apply programCases (sharedMeasure M) ![auxiliaryTerm dom cod fn arg] _
  intro β j Δ p keep measured
  rw [unaryInputsRename,appAuxRename] at measured
  rw [hasRename,appAuxRename]
  exact withParentMeasure V M X W s (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j)
    (arg.relabel j) (fx.relabel j) (ax.relabel j) p (seedsRename V M X W s i j Δ keep) measured

#print axioms seedsRename
#print axioms exact_OpenCoverAuxLeastFromSeedLeasts
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastFromSeedLeastsProof
