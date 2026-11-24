module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalDirectTargetPartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawTargets
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameUnit)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem liftAt (p : Program 1) (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p out (xs i)))) :
    Nonempty (Derivation B Γ (programGraph (.composition p ![.projection i]) out xs)) := by
  apply compositionValue p ![.projection i] out xs ![xs i] h
  intro k
  obtain rfl := Fin.eq_zero k
  exact projectionValue i xs

private theorem stripAt (p : Program 1) (i : Fin 3) (xs : Fin 3 → OTerm α) (out : OTerm α)
    (h : Nonempty (Derivation B Γ (unary p (suc out) (xs i)))) :
    Nonempty (Derivation B Γ
      (programGraph (.composition predecessor ![(.composition p ![.projection i])]) out xs)) := by
  apply compositionValue predecessor ![(.composition p ![.projection i])] out xs
    ![suc out] (predecessorSuccessor out)
  intro k
  obtain rfl := Fin.eq_zero k
  exact liftAt p i xs (suc out) h

theorem mappedCases (t k a : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (programGraph mapReady (suc z) (sourceTape t k a))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (projected : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (unary insertedTargets (suc projected) (a.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply optionGraphCases insertedTargets ![a] goal
  · intro β j Δ keep failed
    rw [inputsRename] at failed
    let xs := sourceTape (t.relabel j) (k.relabel j) (a.relabel j)
    have h0 : Nonempty (Derivation B Δ (programGraph mapAt z xs)) :=
      liftAt insertedTargets 2 xs z failed
    have lost := zeroBranchElim mapAt (constantZero 3) (constantOne 3) (suc z) xs
      h0 (renameUnit mapReady t k a held j Δ keep)
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc z) z xs lost (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ out keep present
    rw [inputsRename] at present
    exact next β j Δ out keep present

theorem recoverObserver (test : Program 2) (t k a dt dk projected : OTerm α)
    (ht : Nonempty (Derivation B Γ (unary parser (suc dt) t)))
    (hk : Nonempty (Derivation B Γ (unary parser (suc dk) k)))
    (ha : Nonempty (Derivation B Γ (unary insertedTargets (suc projected) a)))
    (h : Nonempty (Derivation B Γ (programGraph (decodeCall test) (suc z) (sourceTape t k a)))) :
    Nonempty (Derivation B Γ
      (programGraph (observePartition test) (suc z) (sourceTape dt dk projected))) := by
  let xs := sourceTape t k a
  apply compositionRecover (observePartition test) ![payloadAt 0,payloadAt 1,mapPayload]
    (suc z) xs (sourceTape dt dk projected) h
  exact fun i => Fin.cases (stripAt parser 0 xs dt ht)
    (Fin.cases (stripAt parser 1 xs dk hk)
      (Fin.cases (stripAt insertedTargets 2 xs projected ha) (fun j => Fin.elim0 j))) i

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawGraphProof
