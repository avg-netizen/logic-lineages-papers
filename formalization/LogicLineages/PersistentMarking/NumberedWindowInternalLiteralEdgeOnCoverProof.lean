module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeReversalProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinGuardedEdgeCoverProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredThinEdgeReversalProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalThinGuardedEdgeCoverProof (exact_ThinGuardedEdgeCover)
open NumberedWindowInternalMeasuredThinEdgeReversalProof (exact_PairedEdgeReversal)
open NumberedWindowInternalLiteralEnrichedEdgeProof
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof

/-- Both scratch-cover outputs belong to the actual terms on the same
selected edge tape. -/
def KeepsCover (C : Program 3) (s : Settings) (E : Program 4) : Prop :=
  ∀ (B : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty a b va vb : OTerm α),
    D B Γ (acceptEdge E ctx ty a b) →
    D B Γ (unary (scratchVertices C s) va a) →
    D B Γ (unary (scratchVertices C s) vb b) → D B Γ (eqn va vb)

theorem exact_OpenPairedEdgeCover (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings) :
    KeepsCover C s (edge4 (guardedExchange C s (pairedExchange base)) W) := by
  intro B α Γ ctx ty a b va vb edge left right
  obtain ⟨rule⟩ := exact_ThinGuardedEdgeCover C s (pairedExchange base) W B α Γ ctx ty a b va vb
  obtain ⟨edge⟩ := edge
  obtain ⟨left⟩ := left
  obtain ⟨right⟩ := right
  exact ⟨Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction edge (Derivation.conjunctionIntroduction left right))⟩

theorem exact_OpenPairedEdgeReverses (C : Program 3) (base : Program 2) (W : Program 3) (s : Settings) :
    CanReverse (edge4 (guardedExchange C s (pairedExchange base)) W) := by
  intro B α Γ ctx ty a b edge
  obtain ⟨rule⟩ := exact_PairedEdgeReversal C s base W B α Γ ctx ty a b
  obtain ⟨edge⟩ := edge
  exact ⟨Derivation.implicationElimination rule edge⟩

theorem exact_OpenEnrichedEdgeCover (C : Program 3) (s : Settings) (E : Program 4) (O : Program 3)
    (base : KeepsCover C s E) : KeepsCover C s (enrichedEdge E O) := by
  intro B α Γ ctx ty a b va vb h left right
  exact base B α Γ ctx ty a b va vb (exact_OpenEnrichedEdgeBase E O ctx ty a b h) left right

#print axioms exact_OpenPairedEdgeCover
#print axioms exact_OpenPairedEdgeReverses
#print axioms exact_OpenEnrichedEdgeCover
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEdgeOnCoverProof
