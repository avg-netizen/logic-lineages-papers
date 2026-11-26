module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalShapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalBaseCutProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaBaseProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalCoverTypeLeafIntrinsicTargets (onRaw)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaLexicalShapeProof (actualLambdaLexicalShape)
open NumberedWindowInternalCoverLambdaLexicalBaseCutProof (liftRawReport)
open NumberedWindowInternalCoverRestrictedListWindowTargets
  (ordinaryListAllowed numberedListAllowed keepWhenListAllowed)
open NumberedWindowInternalCoverMixedLeafArgumentTargets (mixedLeafHead)
open NumberedWindowInternalCoverRestrictedLambdaFragmentTargets (lambdaFragmentBase)
open NumberedWindowInternalCoverCombinedRestrictedTargets

theorem exact_OpenCoverCombinedRestrictedLambdaBase : ExactOpenCoverCombinedRestrictedLambdaBase := by
  intro s B body α Γ ctx dom q out actual
  let raw := lambdaTerm dom q
  let xs : Fin 2 → OTerm α := ![ctx,raw]
  let G := mixedLeafHead s
  let base := lambdaFragmentBase B
  let remainder := branch (onRaw (header 5 5)) base (keepWhenListAllowed (numberedListAllowed G) base)
  have shape := actualLambdaLexicalShape (body := body) (Γ := Γ) dom q
  have no4 := liftRawReport (header 4 2) ctx raw z shape.ordinaryZero
  have no5 := liftRawReport (header 5 5) ctx raw z shape.numberedZero
  have first := zeroBranchElim (onRaw (header 4 2)) remainder
    (keepWhenListAllowed (ordinaryListAllowed G) base) (suc out) xs no4 actual
  exact zeroBranchElim (onRaw (header 5 5)) base (keepWhenListAllowed (numberedListAllowed G) base)
    (suc out) xs no5 first

#print axioms exact_OpenCoverCombinedRestrictedLambdaBase

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaBaseProof
