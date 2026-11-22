module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaGuardProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverLambdaControlProof (exact_OpenCoverLambdaPositiveControl)
open NumberedWindowInternalCoverRestrictedLambdaFragmentBaseProof (exact_OpenCoverRestrictedLambdaFragmentBase)
open NumberedWindowInternalCoverCombinedRestrictedLambdaBaseProof (exact_OpenCoverCombinedRestrictedLambdaBase)
open NumberedWindowInternalCoverCombinedRestrictedTargets

theorem exact_OpenCoverCombinedRestrictedLambdaGuard : ExactOpenCoverCombinedRestrictedLambdaGuard := by
  intro s B T body α Γ ctx dom q result actual
  let Z : Formula α := unary fragmentGuard (suc z) q
  apply exact_OpenCoverLambdaPositiveControl s (combinedCallback s B) T body α Γ ctx dom q result Z actual
  intro β j Δ v _ found
  have kept := exact_OpenCoverCombinedRestrictedLambdaBase s B body β Δ
    (ctx.relabel j) (dom.relabel j) (q.relabel j) v found
  simp only [Z,unaryRename,sucRelabel,zRelabel]
  exact exact_OpenCoverRestrictedLambdaFragmentBase B body β Δ
    (ctx.relabel j) (dom.relabel j) (q.relabel j) v kept

#print axioms exact_OpenCoverCombinedRestrictedLambdaGuard

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedLambdaGuardProof
