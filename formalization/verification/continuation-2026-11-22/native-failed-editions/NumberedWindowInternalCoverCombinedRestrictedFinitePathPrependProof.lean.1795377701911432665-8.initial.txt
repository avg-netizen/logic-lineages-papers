module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathEliminationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathPrependProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalSparsePositiveHeadDecompositionTargets (positiveAt)
open NumberedWindowInternalSparsePositiveHeadDecompositionFinishSyntaxProof (positiveRename)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)
open NumberedWindowInternalSparsePositiveTransitivityTransportProof (moveSource)
open NumberedWindowInternalSparsePositiveTransitivityFormulaProof (provide suppliedCases)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets (thinHopData thinProvided)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
open NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof (thinProvidedCases hopDataRename)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof (introduceSuppliedPath suppliedPathRename)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof (alignSameRawMidpoint)
open NumberedWindowInternalCoverCombinedRestrictedFinitePathEliminationProof (suppliedPathCases)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem singletonToSuppliedPath (ctx cod src wr dst : OTerm α)
    (one : Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr dst))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  apply thinProvidedCases C X W s raw ctx cod src wr dst _ one
  intro β j Δ left right _ paid
  rw [suppliedPathRename]
  obtain ⟨data⟩ := paid
  obtain ⟨path⟩ := provide raw (packedLeastProgram C X W s) (ctx.relabel j) (cod.relabel j) left right
    (singletonCertificate right (src.relabel j) (wr.relabel j) (dst.relabel j))
    ⟨Derivation.conjunctionRight data⟩
  exact introduceSuppliedPath C X W s raw _ _ _ _ left right
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionLeft data) path⟩

private theorem fromPositives (ctx cod src dst a b b' c code1 code2 : OTerm α)
    (source : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod src a)))
    (target : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod dst c)))
    (same : Nonempty (Derivation body Γ (eqn b' b)))
    (first : Nonempty (Derivation body Γ (positiveAt raw (packedLeastProgram C X W s) ctx cod a code1 b)))
    (tail : Nonempty (Derivation body Γ (positiveAt raw (packedLeastProgram C X W s) ctx cod b' code2 c))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  let least := packedLeastProgram C X W s
  obtain ⟨first⟩ := first
  obtain ⟨source⟩ := source
  obtain ⟨target⟩ := target
  obtain ⟨tail⟩ := moveSource raw least ctx cod b' b code2 c same tail
  obtain ⟨law⟩ := exact_OpenPositiveTransitivity body raw least α ctx cod a code1 b code2 c
  have supplied := Derivation.implicationElimination (weakenClosed law Γ)
    (Derivation.conjunctionIntroduction first tail)
  exact introduceSuppliedPath C X W s raw ctx cod src dst a c
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction source target) supplied⟩

private theorem prependData (ctx cod src wr mid dst a b b' c : OTerm α)
    (head : Nonempty (Derivation body Γ (thinHopData C X W s raw ctx cod src wr mid a b)))
    (tail : Nonempty (Derivation body Γ (pathData C X W s raw ctx cod mid dst b' c))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  obtain ⟨head⟩ := head
  obtain ⟨tail⟩ := tail
  let least := packedLeastProgram C X W s
  let code := singletonCertificate b src wr mid
  have headLeast := Derivation.conjunctionLeft head
  have tailLeast := Derivation.conjunctionLeft tail
  have eq := alignSameRawMidpoint C X W s ctx cod mid b' b
    ⟨Derivation.conjunctionLeft tailLeast⟩ ⟨Derivation.conjunctionRight headLeast⟩
  have first : Nonempty (Derivation body Γ (positiveAt raw least ctx cod a code b)) :=
    ⟨Derivation.conjunctionRight head⟩
  have source : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod src a)) :=
    ⟨Derivation.conjunctionLeft headLeast⟩
  have target : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod dst c)) :=
    ⟨Derivation.conjunctionRight tailLeast⟩
  apply suppliedCases raw least ctx cod b' c (suppliedPath C X W s raw ctx cod src dst)
    ⟨Derivation.conjunctionRight tail⟩
  intro β j Δ code2 keep actualTail
  rw [suppliedPathRename]
  have first' := renameInto first j Δ keep
  have source' := renameInto source j Δ keep
  have target' := renameInto target j Δ keep
  have eq' := renameInto eq j Δ keep
  rw [positiveRename] at first'
  rw [leastRename] at source' target'
  rw [eqnRelabel] at eq'
  exact fromPositives C X W s raw _ _ _ _ _ _ _ _ _ code2 source' target' eq' first' actualTail

theorem prependThinProvided (ctx cod src wr mid dst : OTerm α)
    (head : Nonempty (Derivation body Γ (thinProvided C X W s raw ctx cod src wr mid)))
    (tail : Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod mid dst))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  apply thinProvidedCases C X W s raw ctx cod src wr mid _ head
  intro β j Δ a b keep first
  rw [suppliedPathRename]
  have tail' := renameInto tail j Δ keep
  rw [suppliedPathRename] at tail'
  apply suppliedPathCases C X W s raw (ctx.relabel j) (cod.relabel j) (mid.relabel j)
    (dst.relabel j) _ tail'
  intro γ k Θ b' c keep' rest
  rw [suppliedPathRename]
  have first' := renameInto first k Θ keep'
  rw [hopDataRename] at first'
  exact prependData C X W s raw _ _ _ _ _ _ _ _ _ _ first' rest

#print axioms singletonToSuppliedPath
#print axioms prependThinProvided
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFinitePathPrependProof
