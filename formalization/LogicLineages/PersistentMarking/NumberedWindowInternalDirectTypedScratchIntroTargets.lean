module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchConsTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

def ExactTypedScratchNil : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)),
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) z))

def ExactIntroTypedScratchCons : Prop :=
  ∀ (i : Program 1) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (code head tail : OTerm α),
    Nonempty (Derivation B Γ (consGraph code head tail)) →
    Nonempty (Derivation B Γ (unary i (suc z) head)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) tail)) →
    Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code))

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroTargets
