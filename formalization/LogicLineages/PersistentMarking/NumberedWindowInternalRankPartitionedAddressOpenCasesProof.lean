module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalParameterizedAddressPositiveOpenProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenCasesProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedAddressPositive (addressAt zeroAddress)
open NumberedWindowInternalParameterizedAddressPositiveOpenProof
open NumberedWindowInternalRankPartitionedAddress
open NumberedWindowInternalRankPartitionedAddressOpenProof (exact_OpenRankPartitionZero)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem parsedTarget (cv tv : Program 1) (P : Program 5) (x w y c ty src dst : OTerm α)
    (held : Nonempty (Derivation B Γ (AddressAtReport cv tv P x w y c ty src dst))) :
    Nonempty (Derivation B Γ (unary rawLeast dst y)) := by
  obtain ⟨report⟩ := held
  let right := Derivation.conjunctionLeft (Derivation.conjunctionRight report)
  exact ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.conjunctionRight right))⟩

/-- Open the concrete zero branch of the physically partitioned address
checker. The exposed target equals the exact target whose zero-rank test
was used, by functionality of the actual original rawLeast selector. -/
theorem exact_OpenRankPartitionZeroCases (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (x w y k : OTerm α) (goal : Formula α)
    (field : Nonempty (Derivation B Γ (unary rawLeast k y)))
    (rank : Nonempty (Derivation B Γ (unary g z k)))
    (accepted : Nonempty (Derivation B Γ
      (programGraph (rankPartitionedAddress cv tv g raw L) (suc z) ![x,w,y])))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (c ty src dst : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (AddressAtReport cv tv (zeroPositive g raw L)
        (x.relabel j) (w.relabel j) (y.relabel j) c ty src dst)) →
      Nonempty (Derivation B Δ (eqn dst (k.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply exact_OpenAddressAtCases cv tv (zeroPositive g raw L) x w y goal
    ((exact_OpenRankPartitionZero cv tv g raw L x w y k field rank).mp accepted)
  intro β j Δ c ty src dst keep got
  have prior := renameInto field j Δ keep
  rw [unaryRename] at prior
  have actual := parsedTarget cv tv (zeroPositive g raw L) (x.relabel j) (w.relabel j) (y.relabel j) c ty src dst got
  exact next β j Δ c ty src dst keep got (valueUnique rawLeast dst (k.relabel j) ![y.relabel j] actual prior)

theorem exact_InstallOpenRankPartitionZero (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (x w y c ty src dst : OTerm α)
    (held : Nonempty (Derivation B Γ (AddressAtReport cv tv (zeroPositive g raw L) x w y c ty src dst)))
    (rank : Nonempty (Derivation B Γ (unary g z dst))) :
    Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv g raw L) (suc z) ![x,w,y])) :=
  (exact_OpenRankPartitionZero cv tv g raw L x w y dst (parsedTarget cv tv _ x w y c ty src dst held) rank).mpr
    (exact_OpenAddressAtIntro cv tv (zeroPositive g raw L) x w y c ty src dst held)

#print axioms exact_OpenRankPartitionZeroCases
#print axioms exact_InstallOpenRankPartitionZero
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenCasesProof
