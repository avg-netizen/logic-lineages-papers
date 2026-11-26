module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnCoordinatesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowLiteralProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalCoverSelectedGrammarLambdaOwnTermPartProof (lambdaRename)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntax)
open NumberedWindowInternalCoverLambdaSelectedRowLiteralProof (exact_OpenCoverLambdaSelectedRow)
open NumberedWindowInternalCoverLambdaSelectedMeasureChildProof (exact_OpenCoverLambdaSelectedMeasure)
open NumberedWindowInternalCoverLambdaDerivedOwnInputSyntaxProof (inputsRename)
open NumberedWindowInternalCoverLambdaDerivedOwnCoordinatesProof (fromCoordinates)
open NumberedWindowInternalCoverLambdaDerivedOwnTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withChildValid (V T M : Program 1) (W : Program 3) (s : Settings)
    (p vertices ctx bodyTy ty q : OTerm α)
    (paid : Inputs V T M W s body Γ p vertices ctx bodyTy ty q)
    (childValid : Nonempty (Derivation body Γ (unary (lambdaSyntax V T) (suc z) q))) :
    Nonempty (Derivation body Γ (memberGraph vertices (lambdaTerm ty q))) := by
  apply exact_OpenCoverLambdaSelectedMeasure M body α Γ ty q p _ paid.measured
  intro β j Δ old mc d width keep row
  rw [graphRename,lambdaRename]
  have paid' := inputsRename V T M W s p vertices ctx bodyTy ty q j keep paid
  have valid' := moveReport j Δ keep (lambdaSyntax V T) (suc z) q childValid
  simp only [sucRelabel,zRelabel] at valid'
  obtain ⟨data⟩ := row.recovered
  exact fromCoordinates V T M W s (p.relabel j) mc d width (vertices.relabel j)
    (ctx.relabel j) (bodyTy.relabel j) (ty.relabel j) (q.relabel j) paid' valid'
    row.child row.childPair ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight data)⟩

theorem exact_OpenCoverLambdaDerivedOwn : ExactOpenCoverLambdaDerivedOwn := by
  intro V T M W s body α Γ p vertices ctx bodyTy ty q paid
  apply exact_OpenCoverLambdaSelectedRow V T body α Γ ty q _ paid.valid
  intro β j Δ old keep row
  rw [graphRename,lambdaRename]
  have paid' := inputsRename V T M W s p vertices ctx bodyTy ty q j keep paid
  obtain ⟨data⟩ := row.recovered
  exact withChildValid V T M W s (p.relabel j) (vertices.relabel j) (ctx.relabel j)
    (bodyTy.relabel j) (ty.relabel j) (q.relabel j) paid'
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight data)⟩

#print axioms exact_OpenCoverLambdaDerivedOwn

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaDerivedOwnScratchProof
