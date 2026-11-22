module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxForwardTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalCoverNumberedTypeWindowTargets (numberedTypeWindow)
open NumberedWindowInternalCoverLambdaLexicalWindowTargets (lambdaLexicalWindow)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentGuard)
open NumberedWindowInternalCoverAuxFragmentInductionSyntaxTargets (forwardBelow)

def ExactOpenCoverAuxFragmentInductionStep : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx raw result : OTerm α),
    Nonempty (Derivation body Γ
      (forwardBelow (numberedTypeWindow s B T) (lambdaLexicalWindow s B T) ctx raw)) →
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) raw)) →
    Nonempty (Derivation body Γ (windowAt (numberedTypeWindow s B T) ctx result raw)) →
    Nonempty (Derivation body Γ (windowAt (lambdaLexicalWindow s B T) ctx result raw))

/-- Only the actual physical guarded fragment, at the same supplied
context, type, and key. No presented host tree or transfer is a premise. -/
def ExactOpenCoverAuxFragmentWindowForward : Prop :=
  ∀ (s : Settings) (B : Program 2) (T : Program 1) (body : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (ctx raw result : OTerm α),
    Nonempty (Derivation body Γ (unary fragmentGuard (suc z) raw)) →
    Nonempty (Derivation body Γ (windowAt (numberedTypeWindow s B T) ctx result raw)) →
    Nonempty (Derivation body Γ (windowAt (lambdaLexicalWindow s B T) ctx result raw))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentInductionTargets
