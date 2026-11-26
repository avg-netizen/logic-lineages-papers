module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixInputProof
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

theorem normalize (P : Program 6) (extrasSide : Bool)
    (right label f g recorded base dest extraTypes extras otherExtras : OTerm alpha)
    (hrc : Nonempty (Derivation body Delta (programGraph P right ![label,g,recorded,dest,extraTypes,otherExtras])))
    (hhead : Nonempty (Derivation body Delta (eqn f g)))
    (hsibling : Nonempty (Derivation body Delta (eqn (if extrasSide then base else extras) (if extrasSide then dest else otherExtras)))) :
    Nonempty (Derivation body Delta (programGraph P right
      ![label,f,recorded,if extrasSide then base else dest,extraTypes,if extrasSide then otherExtras else extras])) := by
  apply inputs P right ![label,g,recorded,dest,extraTypes,otherExtras] _ hrc
  intro i
  fin_cases i
  · exact ⟨refl _⟩
  · exact hhead
  · exact ⟨refl _⟩
  · cases extrasSide
    · exact ⟨refl _⟩
    · exact hsibling
  · exact ⟨refl _⟩
  · cases extrasSide
    · exact hsibling
    · exact ⟨refl _⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixInputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.GenericSixInputProof
