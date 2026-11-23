module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesParsedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedSeedGrammarTargets (SeedGrammar)
open NumberedWindowInternalCoverSelectedSeedGrammarProof (exact_OpenCoverSelectedSeedGrammar seedGrammarRename)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof (inputsRename)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesParsedProof (fromBothSeedScopes)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withFunctionScope (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx dom cod fn arg fx ax p mf ma df bf da ba fState fTerms fArgs : OTerm α)
    (i : ActualAuxCoverDomainInputs V N X W s body Γ ctx dom cod fn arg fx ax p mf ma df bf da ba)
    (f : SeedGrammar s body Γ fn df bf fState fTerms fArgs) :
    Nonempty (Derivation body Γ (hasLeast (selectedCover V N) X W s ctx cod (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenCoverSelectedSeedGrammar V N X W s body α Γ ctx dom arg ax ma da ba _
    i.argumentLeast i.argumentValid i.argumentMeasure i.argumentPair
  intro β j Δ aState aTerms aArgs keep a
  rw [hasRename,appAuxRename]
  have i' := inputsRename V N X W s i j keep
  have f' := seedGrammarRename s fn df bf fState fTerms fArgs f j Δ keep
  exact fromBothSeedScopes V N X W s (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j)
    (arg.relabel j) (fx.relabel j) (ax.relabel j) (p.relabel j) (mf.relabel j) (ma.relabel j)
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j) (fState.relabel j) (fTerms.relabel j)
    (fArgs.relabel j) aState aTerms aArgs i' f' a

theorem exact_OpenCoverAuxLeastAtKnownScopes : ExactOpenCoverAuxLeastAtKnownScopes := by
  intro V N X W s body α Γ ctx dom cod fn arg fx ax p mf ma df bf da ba i
  apply exact_OpenCoverSelectedSeedGrammar V N X W s body α Γ ctx (rawCons dom cod) fn fx mf df bf _
    i.functionLeast i.functionValid i.functionMeasure i.functionPair
  intro β j Δ fState fTerms fArgs keep f
  rw [hasRename,appAuxRename]
  have i' := inputsRename V N X W s i j keep
  exact withFunctionScope V N X W s (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j)
    (arg.relabel j) (fx.relabel j) (ax.relabel j) (p.relabel j) (mf.relabel j) (ma.relabel j)
    (df.relabel j) (bf.relabel j) (da.relabel j) (ba.relabel j) fState fTerms fArgs i' f

#print axioms exact_OpenCoverAuxLeastAtKnownScopes
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesProof
