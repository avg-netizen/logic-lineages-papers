module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedParsedScratchDomainProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedSeedGrammarProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesParsedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationSyntaxProof (appAuxRename)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchTargets (selectedCover)
open NumberedWindowInternalCoverSelectedSeedGrammarTargets (SeedGrammar)
open NumberedWindowInternalCoverSelectedSeedGrammarProof (seedGrammarRename)
open NumberedWindowInternalCoverAuxOwnBoundsAssemblyProof (fromActualBounds)
open NumberedWindowInternalCoverCombinedRestrictedParsedScratchDomainProof (leastAtActualContext)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesRenameProof (inputsRename)
open NumberedWindowInternalCoverAuxLeastAtKnownScopesTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem fromBothSeedScopes (V N : Program 1) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx dom cod fn arg fx ax p mf ma df bf da ba fState fTerms fArgs aState aTerms aArgs : OTerm α)
    (i : ActualAuxCoverDomainInputs V N X W s body Γ ctx dom cod fn arg fx ax p mf ma df bf da ba)
    (f : SeedGrammar s body Γ fn df bf fState fTerms fArgs)
    (a : SeedGrammar s body Γ arg da ba aState aTerms aArgs) :
    Nonempty (Derivation body Γ (hasLeast (selectedCover V N) X W s ctx cod (auxiliaryTerm dom cod fn arg))) := by
  let C := selectedCover V N
  apply programCases (scratchVertices C s) ![auxiliaryTerm dom cod fn arg] _
  intro β j Δ vertices keep held
  rw [unaryInputsRename,appAuxRename] at held
  rw [hasRename,appAuxRename]
  have i' := inputsRename V N X W s i j keep
  have f' := seedGrammarRename s fn df bf fState fTerms fArgs f j Δ keep
  have a' := seedGrammarRename s arg da ba aState aTerms aArgs a j Δ keep
  have member := fromActualBounds V N s (p.relabel j) (df.relabel j) (bf.relabel j) (da.relabel j)
    (ba.relabel j) (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j) (aState.relabel j)
    (aTerms.relabel j) (aArgs.relabel j) vertices (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    ⟨f'.actual,f'.member⟩ ⟨a'.actual,a'.member⟩ i'.parentBounds i'.domainMember i'.codomainMember
    i'.parentValid i'.parentMeasure held
  exact leastAtActualContext C W X s (ctx.relabel j) (cod.relabel j)
    (auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)) vertices
    i'.contextAtParent held member

#print axioms fromBothSeedScopes
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxLeastAtKnownScopesParsedProof
