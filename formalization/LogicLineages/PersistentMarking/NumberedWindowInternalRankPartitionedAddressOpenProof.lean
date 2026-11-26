module
public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddress
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro zeroBranchElim successorBranchIntro successorBranchElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelope (applyUnary)
open NumberedWindowInternalFreshProbeParsedEmitter (rawLeast)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalParameterizedAddressPositive (zeroAddress)
open NumberedWindowInternalRankPartitionedAddress

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPhysicalTargetRank (g : Program 1) (x w y k d : OTerm α)
    (field : Nonempty (Derivation B Γ (unary rawLeast k y)))
    (rank : Nonempty (Derivation B Γ (unary g d k))) :
    Nonempty (Derivation B Γ (programGraph (targetRank g) d ![x,w,y])) := by
  have onY : Nonempty (Derivation B Γ (unary (applyUnary g rawLeast) d y)) := by
    apply compositionValue g (fun _ : Fin 1 => rawLeast) d ![y] ![k] rank
    intro i
    obtain rfl := Fin.eq_zero i
    exact field
  apply compositionValue (applyUnary g rawLeast) (fun _ : Fin 1 => .projection (2 : Fin 3)) d ![x,w,y] ![y] onY
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue (2 : Fin 3) ![x,w,y]

theorem exact_OpenRankPartitionZero (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (x w y k : OTerm α)
    (field : Nonempty (Derivation B Γ (unary rawLeast k y)))
    (rank : Nonempty (Derivation B Γ (unary g z k))) :
    Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv g raw L) (suc z) ![x,w,y])) ↔
      Nonempty (Derivation B Γ (programGraph (zeroAddress cv tv g raw L) (suc z) ![x,w,y])) := by
  have tested := exact_OpenPhysicalTargetRank g x w y k z field rank
  exact ⟨zeroBranchElim (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) ![x,w,y] tested,
    zeroBranchIntro (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) ![x,w,y] tested⟩

theorem exact_OpenRankPartitionPositive (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (x w y k d : OTerm α)
    (field : Nonempty (Derivation B Γ (unary rawLeast k y)))
    (rank : Nonempty (Derivation B Γ (unary g (suc d) k))) :
    Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv g raw L) (suc z) ![x,w,y])) ↔
      Nonempty (Derivation B Γ (programGraph (addressPositive cv tv raw L) (suc z) ![x,w,y])) := by
  have tested := exact_OpenPhysicalTargetRank g x w y k (suc d) field rank
  exact ⟨successorBranchElim (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) d ![x,w,y] tested,
    successorBranchIntro (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) d ![x,w,y] tested⟩

#print axioms exact_OpenPhysicalTargetRank
#print axioms exact_OpenRankPartitionZero
#print axioms exact_OpenRankPartitionPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddressOpenProof
