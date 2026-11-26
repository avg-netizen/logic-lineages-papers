module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCutProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalControlGraphSupportProof (projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalDirectBoundaryGuardsTargets (boundaryRaw)
open NumberedWindowInternalDirectSourcePartitionRawTargets (observePartition rawSourceCheck)
open NumberedWindowInternalDirectTargetPartitionRawTargets (rawTargetCheck)
open NumberedWindowInternalDirectInsertedScanTargets (scan)
open NumberedWindowInternalDirectCoreTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem routeCut {n : Nat} (p : Program n) (indices : Fin n → Fin 5)
    (xs : Fin 5 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (route p indices) (suc z) xs))) :
    Nonempty (Derivation B Γ (programGraph p (suc z) (fun i => xs (indices i)))) := by
  apply compositionRecover p (fun i => .projection (indices i)) (suc z) xs (fun i => xs (indices i)) h
  intro i
  exact projectionValue (indices i) xs

theorem exact_OpenCoreCut : ExactOpenCoreCut := by
  intro scalar positive count B α Γ s t k r a held
  let xs := coreTape s t k r a
  let right := conjunction (targetAt count) (scanAt positive)
  obtain ⟨whole⟩ := conjunctionRecover (boundaryAt scalar) (conjunction (sourceAt count) right) xs held
  obtain ⟨partitions⟩ := conjunctionRecover (sourceAt count) right xs ⟨Derivation.conjunctionRight whole⟩
  obtain ⟨tail⟩ := conjunctionRecover (targetAt count) (scanAt positive) xs ⟨Derivation.conjunctionRight partitions⟩
  have b := routeCut (boundaryRaw scalar) ![0,1,3] xs ⟨Derivation.conjunctionLeft whole⟩
  have f := routeCut (rawSourceCheck (observePartition count)) ![0,2,3] xs ⟨Derivation.conjunctionLeft partitions⟩
  have g := routeCut (rawTargetCheck count) ![1,2,4] xs ⟨Derivation.conjunctionLeft tail⟩
  have rscan := routeCut (scan positive) ![4,3] xs ⟨Derivation.conjunctionRight tail⟩
  have read3 (i j k : Fin 5) : (fun l : Fin 3 => xs (![i,j,k] l)) = ![xs i,xs j,xs k] := by
    funext l
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))) l
  have read2 (i j : Fin 5) : (fun l : Fin 2 => xs (![i,j] l)) = ![xs i,xs j] := by
    funext l
    exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) l
  rw [read3] at b f g
  rw [read2] at rscan
  exact ⟨b,f,g,rscan⟩

#print axioms exact_OpenCoreCut
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCutProof
