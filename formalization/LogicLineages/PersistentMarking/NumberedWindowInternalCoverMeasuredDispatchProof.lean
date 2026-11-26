module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchOrdinaryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchNumberedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadDispatchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchProof
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeBase)
open NumberedWindowInternalCoverOrdinaryMeasureTargets (ordinaryMeasureBase)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasureBase)
open NumberedWindowInternalCoverHeadDispatchTargets (RemainingWithoutHeads)
open NumberedWindowInternalCoverHeadDispatchProof (exact_OpenCoverHeadFittedDispatch)
open NumberedWindowInternalCoverMeasuredDispatchOrdinaryProof (exact_OpenMeasuredOrdinaryFacts)
open NumberedWindowInternalCoverMeasuredDispatchNumberedProof (exact_OpenMeasuredNumberedFacts)
open NumberedWindowInternalCoverMeasuredDispatchTargets

theorem exact_OpenCoverMeasuredDispatch : ExactOpenCoverMeasuredDispatch := by
  intro V TV M A B T s body α Γ raw p vertices ctx result P remain physical
  have needed : RemainingWithoutHeads P s body := {
    lambdaBody := remain.lambdaBody
    ordinary := fun _ _ q m out x y h a goal row =>
      exact_OpenMeasuredOrdinaryFacts V TV M A B T s q m out x y h a goal remain row
    numbered := fun _ _ q m out x y h t k l r goal row =>
      exact_OpenMeasuredNumberedFacts V TV M A B T s q m out x y h t k l r goal remain row
  }
  exact exact_OpenCoverHeadFittedDispatch V TV (ordinaryMeasureBase (numberedMeasureBase M A) A)
    (numberedTypeBase s B) T s body α Γ raw p vertices ctx result needed physical

#print axioms exact_OpenCoverMeasuredDispatch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchProof
