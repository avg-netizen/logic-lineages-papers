module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaNonRecursiveOwnTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverLambdaBoundCoherenceTargets (lexicalFittedPrograms)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverStrictAuxForwardTargets (ChildWindowForward)

/-- The supplied result survives the transfer, with its equality to
the actual stored codomain proved in the object calculus. -/
def ExactOpenCoverLambdaWindowForwardAuxResult : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx dom cod fp ap result : OTerm α),
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc fp))) →
    Nonempty (Derivation body Γ (unary termShape z (suc fp))) →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc ap))) →
    Nonempty (Derivation body Γ (unary termShape z (suc ap))) →
    ChildWindowForward (numberedTypeWindow s B T) (lambdaLexicalWindow s B T) body Γ ctx result
      (auxiliaryTerm dom cod (suc fp) (suc ap))

def ExactOpenCoverLambdaAuxBodyOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom adom acod fp ap p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (lambdaTerm dom (auxiliaryTerm adom acod (suc fp) (suc ap))) p vertices ctx result →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc fp))) →
    Nonempty (Derivation body Γ (unary termShape z (suc fp))) →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc ap))) →
    Nonempty (Derivation body Γ (unary termShape z (suc ap))) →
    Nonempty (Derivation body Γ
      (memberGraph vertices (lambdaTerm dom (auxiliaryTerm adom acod (suc fp) (suc ap)))))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaAuxBodyOwnTargets
