module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowBaseReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowReportsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (z zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase)
open NumberedWindowInternalCoverArgumentGuardTargets (argumentReject)
open NumberedWindowInternalCoverRestrictedListWindowStepProof (selectedActualHeadBase)
open NumberedWindowInternalCoverRestrictedListWindowBaseReportsProof
  (actualRestrictedOrdinaryBase actualRestrictedNumberedBase)
open NumberedWindowInternalCoverRestrictedListWindowTargets

theorem exact_OpenCoverRestrictedOrdinaryListReport : ExactOpenCoverRestrictedOrdinaryListReport := by
  intro s G B T body α Γ ctx h a result actual
  let A := precedingBase s (lambdaLexicalBase s (restrictedListBase G B) T)
  let Q := unary (argumentReject G) z a
  apply selectedActualHeadBase A (refitGuard s T) false ctx h result [a] rfl Q actual
  intro β j Δ _ base
  simp only [Q,unaryRename,zRelabel]
  exact actualRestrictedOrdinaryBase s G B T (ctx.relabel j) (h.relabel j) (a.relabel j) (result.relabel j) base

theorem exact_OpenCoverRestrictedNumberedListReports : ExactOpenCoverRestrictedNumberedListReports := by
  intro s G B T body α Γ ctx h ty k l r result actual
  let A := precedingBase s (lambdaLexicalBase s (restrictedListBase G B) T)
  let J := argumentReject G
  let Q := unary J z l ⊓ unary J z r
  have both : Nonempty (Derivation body Γ Q) := by
    apply selectedActualHeadBase A (refitGuard s T) true ctx h result [ty,k,l,r] rfl Q actual
    intro β j Δ _ base
    obtain ⟨⟨l'⟩,⟨r'⟩⟩ := actualRestrictedNumberedBase s G B T
      (ctx.relabel j) (h.relabel j) (ty.relabel j) (k.relabel j) (l.relabel j) (r.relabel j) (result.relabel j) base
    simp only [Q,conjunctionRename,unaryRename,zRelabel]
    exact ⟨Derivation.conjunctionIntroduction l' r'⟩
  obtain ⟨both⟩ := both
  exact ⟨⟨Derivation.conjunctionLeft both⟩,⟨Derivation.conjunctionRight both⟩⟩

#print axioms exact_OpenCoverRestrictedOrdinaryListReport
#print axioms exact_OpenCoverRestrictedNumberedListReports

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRestrictedListWindowReportsProof
