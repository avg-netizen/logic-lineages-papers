module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchLeavesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchProof
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Obligations)
open NumberedWindowInternalCoverRefinedInductionDispatchProof (exact_OpenCoverRefinedInductionDispatch)
open NumberedWindowInternalCoverFittedInductionDispatchLeavesProof (exact_OpenFittedNamedFacts exact_OpenFittedTypeOnlyFacts)
open NumberedWindowInternalCoverFittedInductionDispatchAuxTypesProof (exact_OpenFittedAuxTypes)
open NumberedWindowInternalCoverFittedInductionDispatchTargets

theorem exact_OpenCoverFittedInductionDispatch : ExactOpenCoverFittedInductionDispatch := by
  intro V TV M B TW s body α Γ raw p vertices ctx result P remaining physical
  have needed : Obligations P s body := {
    named := fun b _ _ q m out x y t i goal row =>
      exact_OpenFittedNamedFacts V TV M B TW s b q m out x y t i goal row
    lambdaBody := remaining.lambdaBody
    typeLeaf := fun _ _ q m out x y t goal row =>
      exact_OpenFittedTypeOnlyFacts V TV M B TW s q m out x y t goal row
    ordinary := remaining.ordinary
    numbered := remaining.numbered
    auxTypes := fun _ _ q m out x y dom cod fn arg row =>
      exact_OpenFittedAuxTypes V TV M B TW s q m out x y dom cod fn arg row
  }
  exact exact_OpenCoverRefinedInductionDispatch V TV (fittedMeasureBase M) (fittedWindowBase s B)
    (refitGuard s TW) s body α Γ raw p vertices ctx result needed physical

#print axioms exact_OpenCoverFittedInductionDispatch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedInductionDispatchProof
