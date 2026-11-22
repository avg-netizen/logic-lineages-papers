module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenChecks

open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverScratchOpenTargets
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (optionFromCallback callbackFromOption)
open NumberedWindowInternalSparseCoverScratchOpenBranchProof (scratchZero scratchSuccessor sameScratchOutput)

theorem exact_CoverOptionGraph : ExactCoverOptionGraph := by
  intro C s body α Γ value seed
  let callback := callbackAt C s value seed
  let option := unary (coverOption C s) value seed
  have source : Derivation body (callback :: Γ) callback := Derivation.hypothesis List.mem_cons_self
  have original : Derivation body (option :: Γ) option := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := optionFromCallback C s value seed ⟨source⟩
  obtain ⟨backward⟩ := callbackFromOption C s value seed ⟨original⟩
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward)⟩

theorem exact_ScratchCallbackZero : ExactScratchCallbackZero := by
  intro C s body α Γ seed
  let callback := callbackAt C s z seed
  have source : Derivation body (callback :: Γ) callback := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := scratchZero C s seed (optionFromCallback C s z seed ⟨source⟩)
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_ScratchCallbackSuccessor : ExactScratchCallbackSuccessor := by
  intro C s body α Γ value seed
  let callback := callbackAt C s (suc value) seed
  have source : Derivation body (callback :: Γ) callback := Derivation.hypothesis List.mem_cons_self
  obtain ⟨result⟩ := scratchSuccessor C s value seed
    (optionFromCallback C s (suc value) seed ⟨source⟩)
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_SameCoverOptionOutput : ExactSameCoverOptionOutput := by
  intro C s body α Γ tag left right leftVertices rightVertices
  let options := unary (coverOption C s) tag left ⊓ unary (coverOption C s) tag right
  let vertices :=
    unary (scratchVertices C s) leftVertices left ⊓ unary (scratchVertices C s) rightVertices right
  have supplied : Derivation body ((options ⊓ vertices) :: Γ) (options ⊓ vertices) :=
    Derivation.hypothesis List.mem_cons_self
  have callbacks := Derivation.conjunctionLeft supplied
  have runs := Derivation.conjunctionRight supplied
  obtain ⟨same⟩ := sameScratchOutput C s tag left right leftVertices rightVertices
    ⟨Derivation.conjunctionLeft callbacks⟩ ⟨Derivation.conjunctionRight callbacks⟩
    ⟨Derivation.conjunctionLeft runs⟩ ⟨Derivation.conjunctionRight runs⟩
  exact ⟨Derivation.implicationIntroduction same⟩

theorem exact_SameCallbackOutput : ExactSameCallbackOutput := by
  intro C s body α Γ tag left right leftVertices rightVertices
  let callbacks := callbackAt C s tag left ⊓ callbackAt C s tag right
  let vertices :=
    unary (scratchVertices C s) leftVertices left ⊓ unary (scratchVertices C s) rightVertices right
  let Δ := (callbacks ⊓ vertices) :: Γ
  have supplied : Derivation body Δ (callbacks ⊓ vertices) := Derivation.hypothesis List.mem_cons_self
  have options := Derivation.conjunctionLeft supplied
  have runs := Derivation.conjunctionRight supplied
  obtain ⟨first⟩ := optionFromCallback C s tag left ⟨Derivation.conjunctionLeft options⟩
  obtain ⟨second⟩ := optionFromCallback C s tag right ⟨Derivation.conjunctionRight options⟩
  obtain ⟨same⟩ := exact_SameCoverOptionOutput C s body α Δ tag left right leftVertices rightVertices
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination same
    (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction first second) runs))⟩

#print axioms exact_CoverOptionGraph
#print axioms exact_ScratchCallbackZero
#print axioms exact_ScratchCallbackSuccessor
#print axioms exact_SameCoverOptionOutput
#print axioms exact_SameCallbackOutput

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenChecks
