module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchReportTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

/-- Actual one cons of the same typed scratch, not a reflected host list. -/
def ExactTypedScratchCons : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code head tail : OTerm α),
    Nonempty (Derivation B Γ (consGraph code head tail)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code)) →
    Nonempty (Derivation B Γ
      (unary i (suc z) head ⊓ unary (typedScratch i) (suc z) tail))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsTargets
