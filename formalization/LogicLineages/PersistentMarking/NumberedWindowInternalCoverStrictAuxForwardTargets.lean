module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverFittedBaseTapeForwardTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (header)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)

def ChildWindowForward {α : Type} (P Q : Program 3) (body : Positive (Fin 1))
    (Γ : List (Formula α)) (ctx ty raw : OTerm α) : Prop :=
  Nonempty (Derivation body Γ (windowGraph P ctx ty raw)) →
  Nonempty (Derivation body Γ (windowGraph Q ctx ty raw))

/-- The two callbacks cover precisely the actual child coordinates at
this strict aux node. They quantify over neither arbitrary keys nor contexts. -/
def ExactOpenCoverStrictAuxForward : Prop :=
  ∀ (P Q : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fn arg : OTerm α),
    ChildWindowForward (strictAuxWindow P T) (strictAuxWindow Q T) body Γ ctx (rawCons dom cod) fn →
    ChildWindowForward (strictAuxWindow P T) (strictAuxWindow Q T) body Γ ctx dom arg →
    ChildWindowForward (strictAuxWindow P T) (strictAuxWindow Q T) body Γ ctx cod
      (auxiliaryTerm dom cod fn arg)

/-- One actual aux layer from the preceding fitted window to the lexical
fitted window, where both child tapes really take the paid nonrecursive cut. -/
def ExactOpenCoverLambdaWindowForwardAuxLayer : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod fp ap : OTerm α),
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc fp))) →
    Nonempty (Derivation body Γ (unary termShape z (suc fp))) →
    Nonempty (Derivation body Γ (unary (header 2 2) z (suc ap))) →
    Nonempty (Derivation body Γ (unary termShape z (suc ap))) →
    ChildWindowForward (numberedTypeWindow s B T) (lambdaLexicalWindow s B T) body Γ ctx cod
      (auxiliaryTerm dom cod (suc fp) (suc ap))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardTargets
