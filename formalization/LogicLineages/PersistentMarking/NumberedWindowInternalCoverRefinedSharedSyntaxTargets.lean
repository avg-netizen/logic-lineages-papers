module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSharedMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedValidityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalRawListRecursion (lookup)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated currentKey unaryAfter)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (TypeSyntaxCalibrated)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverSelectedValidityTargets (headerAny headersAt layout)
open NumberedWindowInternalCoverSharedRecursionTargets
open NumberedWindowInternalCoverSharedMemoTargets

def headerOnRow : Program 4 := unaryAfter (headerAny layout) currentKey

/-- Header-check the actual current row inside its physical recursion.
Recursive lookups therefore read this same refined table, rather than
invoke the old selected unary program after checking the parent header. -/
def refinedUpdate (V T : Program 1) : Program 4 :=
  conjunction (sharedSyntaxUpdate V T) headerOnRow

def refinedSyntax (V T : Program 1) : Program 1 := selectedMeasure (refinedUpdate V T)

def ExactCoverRefinedSharedSyntaxStep : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
  ∀ (i old : Nat),
    (∀ n, n < i+1 → evaluate lookup ((i-n) ::ᵥ old ::ᵥ nil) = (syntaxBits n).1.toNat) →
    evaluate (refinedUpdate V T) (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = (syntaxBits (i+1)).1.toNat

def ExactCoverRefinedSharedSyntax : Prop :=
  ∀ (V T : Program 1), TermSyntaxCalibrated V → TypeSyntaxCalibrated T →
    TermSyntaxCalibrated (refinedSyntax V T)

def ExactOpenCoverSelectedMemoZero : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)),
    Nonempty (Derivation body Γ (unary (selectedMeasure R) z z))

def ExactOpenCoverRefinedStep : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (prior old : OTerm α),
    ObservedStep (refinedUpdate V T) body Γ prior old (suc z) →
    Nonempty (Derivation body Γ
      (programGraph (sharedSyntaxUpdate V T) (suc z) ![prior,old,z,z])) ∧
    Nonempty (Derivation body Γ (unary (headerAny layout) (suc z) (suc prior)))

def ExactOpenCoverRefinedSharedHeaders : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (raw : OTerm α),
    Nonempty (Derivation body Γ (unary (refinedSyntax V T) (suc z) raw)) →
    Nonempty (Derivation body Γ (headersAt layout raw))

def refinedLambdaChildren {α : Type} (V T : Program 1) (ty q : OTerm α) : Formula α :=
  unary T (suc z) ty ⊓ unary (refinedSyntax V T) (suc z) q

def refinedAuxChildren {α : Type} (V T : Program 1) (dom cod fn arg : OTerm α) : Formula α :=
  (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (unary (refinedSyntax V T) (suc z) fn ⊓ unary (refinedSyntax V T) (suc z) arg)

def ExactOpenCoverRefinedLambdaSyntaxParent : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (ty q : OTerm α),
    Nonempty (Derivation body Γ (unary (refinedSyntax V T) (suc z) (lambdaTerm ty q))) →
    Nonempty (Derivation body Γ (refinedLambdaChildren V T ty q))

def ExactOpenCoverRefinedAuxSyntaxParent : Prop :=
  ∀ (V T : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ (unary (refinedSyntax V T) (suc z) (auxiliaryTerm dom cod fn arg))) →
    Nonempty (Derivation body Γ (refinedAuxChildren V T dom cod fn arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets
