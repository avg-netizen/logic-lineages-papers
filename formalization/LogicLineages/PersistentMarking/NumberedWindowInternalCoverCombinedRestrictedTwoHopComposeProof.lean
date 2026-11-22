module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveTransitivityTransportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseAddressSingletonTargets (singletonCertificate)
open NumberedWindowInternalCoverCombinedRestrictedSingletonTargets (thinHopData thinProvided)
open NumberedWindowInternalCoverCombinedRestrictedSingletonBindingProof (thinProvidedRename)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopEliminationProof (thinProvidedCases hopDataRename)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopOuterProof
  (introduceSuppliedPath suppliedPathRename)
open NumberedWindowInternalSparsePositiveTransitivityChecks (exact_OpenPositiveTransitivity)
open NumberedWindowInternalSparsePositiveTransitivityTransportProof (moveSource)
open NumberedWindowInternalCoverCombinedRestrictedTwoHopTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings) (raw : Program 5)

theorem alignSameRawMidpoint (ctx cod mid a b : OTerm α)
    (ha : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod mid a)))
    (hb : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod mid b))) :
    Nonempty (Derivation body Γ (eqn a b)) := by
  obtain ⟨same⟩ := valueUnique (packedLeastProgram C X W s) (suc a) (suc b) ![ctx,cod,mid] ha hb
  exact ⟨cancelSuc same⟩

private theorem combineData (ctx cod src first mid second dst a b b' c : OTerm α)
    (one : Nonempty (Derivation body Γ (thinHopData C X W s raw ctx cod src first mid a b)))
    (two : Nonempty (Derivation body Γ (thinHopData C X W s raw ctx cod mid second dst b' c))) :
    Nonempty (Derivation body Γ (suppliedPath C X W s raw ctx cod src dst)) := by
  obtain ⟨one⟩ := one
  obtain ⟨two⟩ := two
  let least := packedLeastProgram C X W s
  let code1 := singletonCertificate b src first mid
  let code2 := singletonCertificate c mid second dst
  have oneLeast := Derivation.conjunctionLeft one
  have twoLeast := Derivation.conjunctionLeft two
  have same := alignSameRawMidpoint C X W s ctx cod mid b' b
    ⟨Derivation.conjunctionLeft twoLeast⟩ ⟨Derivation.conjunctionRight oneLeast⟩
  obtain ⟨advanced⟩ := moveSource raw least ctx cod b' b code2 c same
    ⟨Derivation.conjunctionRight two⟩
  obtain ⟨law⟩ := exact_OpenPositiveTransitivity body raw least α ctx cod a code1 b code2 c
  have path := Derivation.implicationElimination (weakenClosed law Γ)
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight one) advanced)
  exact introduceSuppliedPath C X W s raw ctx cod src dst a c ⟨Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft oneLeast) (Derivation.conjunctionRight twoLeast))
    path⟩

theorem exact_OpenCoverThinTwoHop : ExactOpenCoverThinTwoHop := by
  intro C X W s raw body α Γ ctx cod src first mid second dst one two
  apply thinProvidedCases C X W s raw ctx cod src first mid _ one
  intro β j Δ a b keep leftReport
  rw [suppliedPathRename]
  have right := renameInto two j Δ keep
  rw [thinProvidedRename] at right
  apply thinProvidedCases C X W s raw (ctx.relabel j) (cod.relabel j) (mid.relabel j)
    (second.relabel j) (dst.relabel j) _ right
  intro γ k Θ b' c keep' rightReport
  rw [suppliedPathRename]
  have left := renameInto leftReport k Θ keep'
  rw [hopDataRename] at left
  exact combineData C X W s raw _ _ _ _ _ _ _ _ _ _ _ left rightReport

#print axioms alignSameRawMidpoint
#print axioms exact_OpenCoverThinTwoHop
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTwoHopComposeProof
