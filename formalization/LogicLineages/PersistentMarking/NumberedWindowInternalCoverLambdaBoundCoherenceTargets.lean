module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLexicalWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredDispatchTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverNamedLeavesTargets (namedTerm)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverNumberedMeasureSelectedTargets (numberedMeasuredPrograms)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalBase lambdaLexicalWindow)

abbrev lexicalFittedPrograms (s : Settings) (V TV M A : Program 1) (B : Program 2) (T : Program 1) : Programs :=
  numberedMeasuredPrograms s V TV M A (lambdaLexicalBase s B T) T

/-- Install an actual ordinary-base successor in the actual strict
selected window, when this same key physically rejects tag six. -/
def ExactOpenCoverInstallNonAuxWindow : Prop :=
  ∀ (A : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx prior result : OTerm α),
    Nonempty (Derivation body Γ (unary termShape z (suc prior))) →
    Nonempty (Derivation body Γ (programGraph A (suc result) ![ctx,suc prior])) →
    Nonempty (Derivation body Γ (windowGraph (strictAuxWindow A T) ctx result (suc prior)))

/-- Physical same-output coherence only for literal bound tag one. -/
def ExactOpenCoverLambdaBoundCoherence : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx ty i result : OTerm α),
    Nonempty (Derivation body Γ (windowGraph (numberedTypeWindow s B T) ctx result (namedTerm 1 ty i))) →
    Nonempty (Derivation body Γ (windowGraph (lambdaLexicalWindow s B T) ctx result (namedTerm 1 ty i)))

abbrev boundZeroLambda {α : Type} (dom annotation : OTerm α) :=
  lambdaTerm dom (namedTerm 1 annotation z)

def ExactOpenCoverLambdaBoundZeroOwnScratch : Prop :=
  ∀ (V TV M A : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom annotation p vertices ctx result : OTerm α),
    ParentRow (lexicalFittedPrograms s V TV M A B T) s body Γ
      (boundZeroLambda dom annotation) p vertices ctx result →
    Nonempty (Derivation body Γ (memberGraph vertices (boundZeroLambda dom annotation)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaBoundCoherenceTargets
