module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionEqualityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem inputs (P : Program 6) (raw : OTerm alpha) (xs ys : Fin 6 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (programGraph P raw xs)))
    (he : ∀ i, Nonempty (Derivation body Delta (eqn (ys i) (xs i)))) :
    Nonempty (Derivation body Delta (programGraph P raw ys)) := by
  unfold programGraph at hc ⊢
  apply graphInputTransport body alpha 6 Delta _ raw xs ys _ hc
  intro i
  rw [InternalSourceInversionSupportProof.onEquality]
  obtain ⟨h⟩ := he i
  exact ⟨symm h⟩


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixTransportProof
