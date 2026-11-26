module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawSourceIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetPartitionRawTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (insertedTargets)
open NumberedWindowInternalDirectSourcePartitionRawTargets (sourceTape parsedAt payloadAt observePartition appendKeptRemoved)
open NumberedWindowInternalDirectTargetPartitionRawTargets
open NumberedWindowInternalDirectRawSourceIntroProof (Report parsed payload)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem mapped (xs : Fin 3 → OTerm α) (p : OTerm α)
    (h : Report (B := B) (Γ := Γ) insertedTargets (suc p) ![xs 2]) :
    Report (B := B) (Γ := Γ) mapAt (suc p) xs := by
  apply compositionValue insertedTargets ![.projection 2] (suc p) xs ![xs 2] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 xs

private theorem observerDecoded (count : Program 2) (d k p joined : OTerm α)
    (a : Report (B := B) (Γ := Γ) append joined ![k,p])
    (o : Report (B := B) (Γ := Γ) count (suc z) ![d,joined]) :
    Report (B := B) (Γ := Γ) (observePartition count) (suc z) (sourceTape d k p) := by
  let xs := sourceTape d k p
  have joinedAt : Report (B := B) (Γ := Γ) appendKeptRemoved joined xs := by
    apply compositionValue append ![.projection 1,.projection 2] joined xs ![k,p] a
    intro i
    exact Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (fun j => Fin.elim0 j)) i
  apply compositionValue count ![.projection 0,appendKeptRemoved] (suc z) xs ![d,joined] o
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases joinedAt (fun j => Fin.elim0 j)) i

/-- Rebuild the actual raw target check from the exact target and kept
parser outputs, actual inserted row projection, ordered append, and
actual tested same-operand count graph. -/
theorem exact_OriginalRawTargetFromReports (count : Program 2)
    (t k a dt dk projected joined : OTerm α)
    (tapeTarget : Nonempty (Derivation B Γ (unary parser (suc dt) t)))
    (tapeKept : Nonempty (Derivation B Γ (unary parser (suc dk) k)))
    (mapRows : Nonempty (Derivation B Γ (unary insertedTargets (suc projected) a)))
    (app : Report (B := B) (Γ := Γ) append joined ![dk,projected])
    (cmp : Report (B := B) (Γ := Γ) count (suc z) ![dt,joined]) :
    Report (B := B) (Γ := Γ) (rawTargetCheck count) (suc z) (sourceTape t k a) := by
  let xs := sourceTape t k a
  have m := mapped xs projected mapRows
  have readyMap : Report (B := B) (Γ := Γ) mapReady (suc z) xs :=
    successorBranchIntro mapAt (constantZero 3) (constantOne 3) (suc z) projected xs m
      (oneConstantValue xs)
  have mapV : Report (B := B) (Γ := Γ) mapPayload projected xs := by
    apply compositionValue predecessor ![mapAt] projected xs ![suc projected]
      (predecessorSuccessor projected)
    intro i
    obtain rfl := Fin.eq_zero i
    exact m
  have dr : Report (B := B) (Γ := Γ) (decodeCall count) (suc z) xs := by
    apply compositionValue (observePartition count) ![payloadAt 0,payloadAt 1,mapPayload] (suc z) xs
      (sourceTape dt dk projected) (observerDecoded count dt dk projected joined app cmp)
    intro i
    exact Fin.cases (payload 0 xs dt tapeTarget)
      (Fin.cases (payload 1 xs dk tapeKept) (Fin.cases mapV (fun j => Fin.elim0 j))) i
  have all : Report (B := B) (Γ := Γ) allReady (suc z) xs :=
    conjunctionAccept (parsedAt 0) (conjunction (parsedAt 1) mapReady) xs (parsed 0 xs dt tapeTarget)
      (conjunctionAccept (parsedAt 1) mapReady xs (parsed 1 xs dk tapeKept) readyMap)
  exact conjunctionAccept allReady (decodeCall count) xs all dr

#print axioms exact_OriginalRawTargetFromReports
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectRawTargetIntroProof
