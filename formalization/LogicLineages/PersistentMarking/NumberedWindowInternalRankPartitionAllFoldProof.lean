module

public import LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionedAddress
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankPositiveTransferProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAddressAtKnownFoldProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionAllFoldProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparsePositiveFold (positive)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalParameterizedPositiveFold (zeroPositive)
open NumberedWindowInternalParameterizedAddressPositive (addressAt zeroAddress exact_OriginalAddressAt)
open NumberedWindowInternalRankPartitionedAddress (targetRank rankPartitionedAddress)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalAddressAtKnownFoldProof (exact_OpenAddressAtKnownFold)
open NumberedWindowInternalSparseAddressPositiveOpenBindingProof (addressReportRename)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalZeroRankPositiveTransferProof (exact_OpenZeroRankPositiveImpliesOrdinary)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem threeRename {β : Type} (x cert y : OTerm α) (j : α → β) :
    (fun i : Fin 3 => (![x,cert,y] i).relabel j) = ![x.relabel j,cert.relabel j,y.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) i

/-- Read a successful physical rank-partitioned address as an ordinary
positive fold on its original two reports and unchanged certificate.
The object calculus splits the actual target-rank computation; no
externally supplied rank result or additional target field is required. -/
theorem exact_OpenRankPartitionOrdinaryFold (cv tv g : Program 1) (raw : Program 5) (L : Program 3)
    (x cert y c ty src dst : OTerm α)
    (left : Nonempty (Derivation B Γ (addressReport x c ty src)))
    (right : Nonempty (Derivation B Γ (addressReport y c ty dst)))
    (held : Nonempty (Derivation B Γ (programGraph (rankPartitionedAddress cv tv g raw L)
      (suc z) ![x,cert,y]))) :
    Nonempty (Derivation B Γ (programGraph (positive raw L) (suc z) ![c,ty,src,cert,dst])) := by
  apply optionGraphCases (targetRank g) ![x,cert,y] _
  · intro β j Δ keep zero
    simp only [programRename,loopArgsRename,sucRelabel,zRelabel]
    rw [threeRename] at zero
    have l := renameInto left j Δ keep
    have r := renameInto right j Δ keep
    simp only [addressReportRename] at l r
    have h := renameInto held j Δ keep
    simp only [programRename,threeRename,sucRelabel,zRelabel] at h
    have selected := zeroBranchElim (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) _ zero h
    have filtered := exact_OpenAddressAtKnownFold cv tv (zeroPositive g raw L)
      (x.relabel j) (cert.relabel j) (y.relabel j) (c.relabel j) (ty.relabel j)
      (src.relabel j) (dst.relabel j) l r selected
    exact exact_OpenZeroRankPositiveImpliesOrdinary g raw L (c.relabel j) (ty.relabel j)
      (src.relabel j) (cert.relabel j) (dst.relabel j) filtered
  · intro β j Δ k keep nonzero
    simp only [programRename,loopArgsRename,sucRelabel,zRelabel]
    rw [threeRename] at nonzero
    have l := renameInto left j Δ keep
    have r := renameInto right j Δ keep
    simp only [addressReportRename] at l r
    have h := renameInto held j Δ keep
    simp only [programRename,threeRename,sucRelabel,zRelabel] at h
    have selected := successorBranchElim (targetRank g) (zeroAddress cv tv g raw L)
      (addressPositive cv tv raw L) (suc z) k _ nonzero h
    have actual : Nonempty (Derivation B Δ (programGraph (addressAt cv tv (positive raw L))
        (suc z) ![x.relabel j,cert.relabel j,y.relabel j])) := by
      rw [exact_OriginalAddressAt]
      exact selected
    exact exact_OpenAddressAtKnownFold cv tv (positive raw L)
      (x.relabel j) (cert.relabel j) (y.relabel j) (c.relabel j) (ty.relabel j)
      (src.relabel j) (dst.relabel j) l r actual

#print axioms exact_OpenRankPartitionOrdinaryFold
end LogicLineages.PersistentMarking.NumberedWindowInternalRankPartitionAllFoldProof
