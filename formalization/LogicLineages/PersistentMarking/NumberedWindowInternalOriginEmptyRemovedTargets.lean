module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapIntroTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTargetMapIntroTargets (D)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)

def ExactOpenScratchNonzeroCases : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (scratch : OTerm α) (goal : Formula α),
    D B Γ ((eqn scratch z).not) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (h t : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      D B Δ (consGraph (scratch.relabel j) h t) →
      D B Δ (goal.relabel j)) → D B Γ goal

def ExactOpenEmptyRemovedScanZero : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows removed : OTerm α),
    D B Γ (unary parser (suc z) removed) →
    D B Γ (loopAccept r rows removed) →
    D B Γ (eqn rows z)

def ExactOpenEmptyRemovedProjectionZero : Prop :=
  ∀ (r : Program 3) (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (rows removed projected : OTerm α),
    D B Γ (unary parser (suc z) removed) →
    D B Γ (loopAccept r rows removed) →
    D B Γ (unary scratchTargets (suc projected) rows) →
    D B Γ (eqn projected z)

end LogicLineages.PersistentMarking.NumberedWindowInternalOriginEmptyRemovedTargets
