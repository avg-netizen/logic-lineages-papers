module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof (boundsRename)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (typesTerm measurePair)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α β : Type} {Γ : List (Formula α)} {Δ : List (Formula β)}

theorem inputsRename (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    {ctx dom cod fn arg fx ax p mf ma df bf da ba : OTerm α}
    (i : ActualAuxCoverDomainInputs V N X W s body Γ ctx dom cod fn arg fx ax p mf ma df bf da ba)
    (j : α → β) (keep : ∀ q ∈ Γ, q.relabel j ∈ Δ) :
    ActualAuxCoverDomainInputs V N X W s body Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j)
      (fn.relabel j) (arg.relabel j) (fx.relabel j) (ax.relabel j) (p.relabel j) (mf.relabel j)
      (ma.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j) := by
  constructor
  · simpa only [windowRename,appAuxRename] using renameInto i.contextAtParent j Δ keep
  · simpa only [leastRename,rawConsRename] using renameInto i.functionLeast j Δ keep
  · simpa only [leastRename] using renameInto i.argumentLeast j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto i.functionValid j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel] using renameInto i.argumentValid j Δ keep
  · simpa only [unaryRename] using renameInto i.functionMeasure j Δ keep
  · simpa only [unaryRename] using renameInto i.argumentMeasure j Δ keep
  · simpa only [measurePair,programRename,binaryInputsRename] using renameInto i.functionPair j Δ keep
  · simpa only [measurePair,programRename,binaryInputsRename] using renameInto i.argumentPair j Δ keep
  · simpa only [unaryRename,sucRelabel,zRelabel,appAuxRename] using renameInto i.parentValid j Δ keep
  · simpa only [unaryRename,appAuxRename] using renameInto i.parentMeasure j Δ keep
  · simpa only [boundsRename] using renameInto i.parentBounds j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto i.domainMember j Δ keep
  · simpa only [graphRename,typesTerm,numeralRename] using renameInto i.codomainMember j Δ keep

#print axioms inputsRename
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof
