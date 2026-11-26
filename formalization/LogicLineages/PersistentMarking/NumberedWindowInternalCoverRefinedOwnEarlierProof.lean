module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOwnEarlierLocalProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedLambdaOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxOwnScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureOpenDataProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedSyntax)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverLocalOwnContinuationTargets (refinedCover)
open NumberedWindowInternalCoverLambdaSyntaxRowLiteralReportsProof (literalReports)
open NumberedWindowInternalAuxMeasureOpenDataProof (bothChildBounds)
open NumberedWindowInternalCoverRefinedLambdaSyntaxProof (exact_OpenCoverRefinedLambdaSyntaxParent)
open NumberedWindowInternalCoverRefinedAuxSyntaxProof (exact_OpenCoverRefinedAuxSyntaxParent)
open NumberedWindowInternalCoverRefinedLambdaOwnScratchProof (exact_OpenCoverRefinedLambdaOwnScratch)
open NumberedWindowInternalCoverRefinedAuxOwnScratchProof (exact_OpenCoverRefinedAuxOwnScratch)
open NumberedWindowInternalCoverOwnEarlierLocalProof (exact_OpenCoverOwnEarlierLocalIH)
open NumberedWindowInternalCoverOwnEarlierTargets

theorem exact_OpenCoverRefinedLambdaOwnEarlier : ExactOpenCoverRefinedLambdaOwnEarlier := by
  intro V TV M W s body α Γ p vertices ctx bodyTy ty q parent earlier typed member
  let Q := refinedSyntax V TV
  let C := refinedCover V TV M
  let key := NumberedWindowInternalCoverLambdaLayerTargets.lambdaTerm ty q
  have order := (literalReports (body := body) (Γ := Γ) ty q z).earlier
  obtain ⟨bits⟩ := exact_OpenCoverRefinedLambdaSyntaxParent V TV body α Γ ty q parent.valid
  have ih := exact_OpenCoverOwnEarlierLocalIH Q W C s body α Γ ctx bodyTy q key
    earlier order ⟨Derivation.conjunctionRight bits⟩
  exact exact_OpenCoverRefinedLambdaOwnScratch V TV M W s body α Γ p vertices ctx bodyTy ty q
    parent typed ih member

theorem exact_OpenCoverRefinedAuxOwnEarlier : ExactOpenCoverRefinedAuxOwnEarlier := by
  intro V TV M B TW s body α Γ p vertices ctx dom cod fn arg parent earlier typed domain codomain
  let Q := refinedSyntax V TV
  let C := refinedCover V TV M
  let W := strictAuxWindow B TW
  let key := NumberedWindowInternalSparseRawFunctionFrameTargets.auxiliaryTerm dom cod fn arg
  have order := bothChildBounds (body := body) (Γ := Γ) dom cod fn arg
  obtain ⟨bits⟩ := exact_OpenCoverRefinedAuxSyntaxParent V TV body α Γ dom cod fn arg parent.valid
  have fnIH := exact_OpenCoverOwnEarlierLocalIH Q W C s body α Γ ctx (rawCons dom cod) fn key
    earlier order.1 ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight bits)⟩
  have argIH := exact_OpenCoverOwnEarlierLocalIH Q W C s body α Γ ctx dom arg key
    earlier order.2 ⟨Derivation.conjunctionRight (Derivation.conjunctionRight bits)⟩
  exact exact_OpenCoverRefinedAuxOwnScratch V TV M B TW s body α Γ p vertices ctx dom cod fn arg
    parent typed fnIH argIH domain codomain

#print axioms exact_OpenCoverRefinedLambdaOwnEarlier
#print axioms exact_OpenCoverRefinedAuxOwnEarlier

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedOwnEarlierProof
