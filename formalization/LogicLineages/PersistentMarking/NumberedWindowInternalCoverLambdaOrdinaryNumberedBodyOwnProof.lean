module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowShapeProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaOrdinaryNumberedBodyOwnProof
open NumberedWindowInternalCoverHeadWindowTargets (headPrior)
open NumberedWindowInternalCoverHeadWindowShapeProof (exact_OpenCoverHeadShape)
open NumberedWindowInternalCoverRestrictedListWindowShapeProof (lambdaRejectHeadKey)
open NumberedWindowInternalCoverLambdaNonRecursiveOwnProof (exact_OpenCoverLambdaNonRecursiveOwnScratch)
open NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets

theorem exact_OpenCoverLambdaOrdinaryBodyOwnScratch : ExactOpenCoverLambdaOrdinaryBodyOwnScratch := by
  intro V TV M A B T s body α Γ dom h a p vertices ctx result row
  exact exact_OpenCoverLambdaNonRecursiveOwnScratch V TV M A B T s body α Γ dom (headPrior false h [a])
    p vertices ctx result row (lambdaRejectHeadKey false h [a])
    (exact_OpenCoverHeadShape false body α Γ h [a] rfl).notAux

theorem exact_OpenCoverLambdaNumberedBodyOwnScratch : ExactOpenCoverLambdaNumberedBodyOwnScratch := by
  intro V TV M A B T s body α Γ dom h ty k l r p vertices ctx result row
  exact exact_OpenCoverLambdaNonRecursiveOwnScratch V TV M A B T s body α Γ dom (headPrior true h [ty,k,l,r])
    p vertices ctx result row (lambdaRejectHeadKey true h [ty,k,l,r])
    (exact_OpenCoverHeadShape true body α Γ h [ty,k,l,r] rfl).notAux

#print axioms exact_OpenCoverLambdaOrdinaryBodyOwnScratch
#print axioms exact_OpenCoverLambdaNumberedBodyOwnScratch

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaOrdinaryNumberedBodyOwnProof
