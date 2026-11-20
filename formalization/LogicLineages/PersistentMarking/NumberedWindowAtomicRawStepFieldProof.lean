module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserUnpackProof
public section

namespace LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
open NumberedWindowAtomicRawStep NumberedWindowAtomicRawStepTargets
open NumberedWindowFieldAlgorithm (pack unpack packNode unpackNode)
open NumberedWindowAnnotationAlgorithm (annotations termNext termParts)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparseFieldParserUnpackProof (casesUnpack)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (cellAt codeOfCell nodeOfCell noNode packOfUnpack)

theorem unpackPacked (xs : List Nat) : unpack (pack xs) = some xs := by
  induction xs with
  | nil => exact casesUnpack.1
  | cons x xs ih =>
    rw [pack,casesUnpack.2.2,ih]
    rfl

theorem nodePacked (tag : Nat) (xs : List Nat) : unpackNode (packNode tag xs) = some (tag,xs) := by
  rw [packNode,nodeOfCell (cellAt tag (pack xs)),unpackPacked]
  rfl

theorem codeOfNode {q tag : Nat} {xs : List Nat}
    (h : unpackNode q = some (tag,xs)) : q = packNode tag xs := by
  cases hc : chosenCell q with
  | none => rw [noNode hc] at h; cases h
  | some cell =>
    rcases cell with ⟨a,t⟩
    rw [nodeOfCell hc] at h
    cases ht : unpack t with
    | none => rw [ht] at h; cases h
    | some fs =>
      rw [ht] at h
      have same : (a,fs) = (tag,xs) := Option.some.inj h
      have htag : a = tag := congrArg Prod.fst same
      have hfields : fs = xs := congrArg Prod.snd same
      rw [codeOfCell hc,packOfUnpack t ht,htag,hfields,packNode]

theorem freeView (t n : Nat) : unpackNode (freeRaw t n) = some (0,[t,n]) := nodePacked 0 [t,n]
theorem bottomView (t : Nat) : unpackNode (bottomRaw t) = some (3,[t]) := nodePacked 3 [t]

theorem freeAnnotation (t n : Nat) : (annotations (freeRaw t n)).1 = t := by
  simp [annotations,termNext,freeView,termParts]
theorem bottomAnnotation (t : Nat) : (annotations (bottomRaw t)).1 = t := by
  simp [annotations,termNext,bottomView,termParts]

theorem atomicFields : ExactAtomicRawFields := by
  refine ⟨fun t n => ⟨freeView t n,freeAnnotation t n⟩,
    fun t => ⟨bottomView t,bottomAnnotation t⟩, ?_,nodePacked 7 []⟩
  intro t n u equality
  have h := congrArg unpackNode equality
  rw [freeView,bottomView] at h
  cases h

end LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
