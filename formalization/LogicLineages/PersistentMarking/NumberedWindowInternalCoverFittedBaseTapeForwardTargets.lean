module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLocalGraphForwardTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (precedingBase lambdaLexicalBase lambdaLexicalWindow)
open NumberedWindowInternalCoverLocalGraphForwardTargets (TapeForward)

def ExactOpenCoverFittedBaseTapeForward : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx raw : OTerm α),
    Nonempty (Derivation body Γ (unary (header 2 2) z raw)) →
    TapeForward (precedingBase s B) (precedingBase s (lambdaLexicalBase s B T)) body Γ ![ctx,raw]

/-- Actual forward transfer only at an object successor key with both
physical rejection reports. It makes no cross-key, backward, λ-child or
aux-child statement. -/
def ExactOpenCoverLambdaWindowForwardNonRecursive : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx before result : OTerm α),
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc before))) →
    Nonempty (Derivation body Γ (unary termShape z (suc before))) →
    Nonempty (Derivation body Γ (windowGraph (numberedTypeWindow s B T) ctx result (suc before))) →
    Nonempty (Derivation body Γ (windowGraph (lambdaLexicalWindow s B T) ctx result (suc before)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets
