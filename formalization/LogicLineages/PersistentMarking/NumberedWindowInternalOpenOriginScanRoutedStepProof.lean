module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanBranchesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginCountRouteProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedRowCasesTargets (Reports)
open NumberedWindowInternalOpenOriginScanIntroTargets (D)
open NumberedWindowInternalOpenOriginScanBranchesProof (exact_OpenOriginScanBranches)
open NumberedWindowInternalOriginCountRouteProof (exact_OpenChosenOriginCountRoute)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalOpenOriginScanRoutedStepTargets

private theorem reportsWithHyp {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    {r : Program 3} {removed row decoded target dom cert : OrdinaryArithmetic.Term α}
    (old : Reports r B Γ removed row decoded target dom cert) (h : Formula α) :
    Reports r B (h :: Γ) removed row decoded target dom cert :=
  ⟨withHyp old.parsed h, withHyp old.targetField h, withHyp old.dominatorField h,
    withHyp old.certificateField h, withHyp old.original h⟩

/-- Actual count and append reports discharge the membership routing for
the two original callbacks without making an external branch choice. -/
theorem exact_OpenOriginScanRoutedStep : ExactOpenOriginScanRoutedStep := by
  intro r B α Γ removed decoded row target dom cert rawLeft rawRight scratchLeft scratchRight
    joined tailLeft tailRight outLeft outRight old parseL parseR count joinedCons leftOK rightOK stepL stepR
  let L := memberGraph scratchLeft dom
  let R := L.not ⊓ memberGraph scratchRight dom
  let goal := loopAccept r outLeft rawLeft ⊓ loopAccept r outRight rawRight
  obtain ⟨oldReport⟩ := old.original
  obtain ⟨route⟩ := exact_OpenChosenOriginCountRoute B α Γ decoded scratchLeft scratchRight joined dom
    count joinedCons ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight oldReport)⟩
  have branches (hyp : Formula α) :=
    exact_OpenOriginScanBranches r B α (hyp :: Γ) removed decoded row target dom cert
      rawLeft rawRight scratchLeft scratchRight tailLeft tailRight outLeft outRight
      (reportsWithHyp old hyp) (withHyp parseL hyp) (withHyp parseR hyp)
      (withHyp leftOK hyp) (withHyp rightOK hyp) (withHyp stepL hyp) (withHyp stepR hyp)
  have caseL : Nonempty (Derivation B Γ (L.imp goal)) := by
    have own : D B (L :: Γ) L := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨_, _, ⟨left⟩, ⟨right⟩⟩ := (branches L).1 own
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction left right)⟩
  have caseR : Nonempty (Derivation B Γ (R.imp goal)) := by
    have own : Derivation B (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
    obtain ⟨_, _, ⟨left⟩, ⟨right⟩⟩ := (branches R).2
      ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction left right)⟩
  obtain ⟨caseL⟩ := caseL
  obtain ⟨caseR⟩ := caseR
  exact ⟨disjunctionElimination route caseL caseR⟩

#print axioms exact_OpenOriginScanRoutedStep

end LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanRoutedStepProof
