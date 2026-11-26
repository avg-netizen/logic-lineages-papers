module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedSharedSyntaxTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalAuxExchangeMemoOpenTableTargets (tableAt)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxTape)
open NumberedWindowInternalCoverRefinedSharedSyntaxTargets (refinedUpdate refinedSyntax refinedAuxChildren)

def ExactOpenCoverRefinedAuxSyntaxIntroRow : Prop :=
  ∀ (V TV : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg old : OTerm α),
    Nonempty (Derivation body Γ (refinedAuxChildren V TV dom cod fn arg)) →
    Nonempty (Derivation body Γ (tableAt (refinedUpdate V TV) old (memoPrior dom cod fn arg))) →
    Nonempty (Derivation body Γ
      (programGraph (refinedUpdate V TV) (suc z) (auxTape dom cod fn arg old)))

/-- Only the original auxiliary tag of the already selected refined V.
The two actual TV bits and actual same-refined-program child bits remain
physical antecedents, independently of any typed-window guard. -/
def ExactOpenCoverRefinedAuxSyntaxIntro : Prop :=
  ∀ (V TV : Program 1) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (dom cod fn arg : OTerm α),
    Nonempty (Derivation body Γ (refinedAuxChildren V TV dom cod fn arg)) →
    Nonempty (Derivation body Γ (unary (refinedSyntax V TV) (suc z) (auxiliaryTerm dom cod fn arg)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedAuxSyntaxIntroTargets
