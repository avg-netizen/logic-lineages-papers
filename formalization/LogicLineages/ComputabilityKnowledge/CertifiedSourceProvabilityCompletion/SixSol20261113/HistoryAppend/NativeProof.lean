module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.NativeProof
open GorbowPRProgram List.Vector

def newValue (n : Nat) (previous : List Nat) : Nat :=
  (Nat.pair (Nat.unpair n).1 ((previous[n-(Nat.unpair n).2]?).getD 0)).succ

def values (right : Nat) : Nat → List Nat
  | 0 => [right]
  | n+1 => newValue n (values right n) :: values right n

def result (right n : Nat) : Nat := ((values right n).head?).getD 0

theorem lookupList (index : Nat) (l : List Nat) :
    evaluate HistoryLookup.lookup (index ::ᵥ Encodable.encode l ::ᵥ nil) = Encodable.encode (l[index]?) := by
  change evaluate HistoryLookup.reference (evaluate HistoryLookup.drop (index ::ᵥ Encodable.encode l ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryLookup.NativeProof.evaluateDrop,HistoryLookup.NativeProof.referenceList,HistoryLookup.NativeProof.headDrop]

theorem referenceEval (n right : Nat) (previous : List Nat) :
    evaluate reference (n ::ᵥ Encodable.encode previous ::ᵥ right ::ᵥ nil) =
      Encodable.encode (previous[n-(Nat.unpair n).2]?) := by
  change evaluate HistoryLookup.lookup
    (evaluate HistoryCodec.difference
      (evaluate HistoryLookup.tail (n.succ ::ᵥ nil) ::ᵥ n ::ᵥ nil) ::ᵥ Encodable.encode previous ::ᵥ nil) = _
  rw [HistoryLookup.NativeProof.evaluateTail,Nat.pred_succ,HistoryCodec.NativeProof.evaluateDifference,lookupList]

theorem recursiveEval (n right : Nat) (previous : List Nat) :
    evaluate recursiveResult (n ::ᵥ Encodable.encode previous ::ᵥ right ::ᵥ nil) =
      (previous[n-(Nat.unpair n).2]?).getD 0 := by
  change evaluate HistoryCodec.predecessor
    (evaluate reference (n ::ᵥ Encodable.encode previous ::ᵥ right ::ᵥ nil) ::ᵥ nil) = _
  rw [referenceEval,HistoryCodec.NativeProof.evaluatePredecessor]
  cases h : previous[n-(Nat.unpair n).2]? <;> rfl

theorem valueEval (n right : Nat) (previous : List Nat) :
    evaluate value (n ::ᵥ Encodable.encode previous ::ᵥ right ::ᵥ nil) = newValue n previous := by
  change evaluate HistoryCodec.cons
    (evaluate HistoryLookup.head (n.succ ::ᵥ nil) ::ᵥ
      evaluate recursiveResult (n ::ᵥ Encodable.encode previous ::ᵥ right ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryCodec.NativeProof.nativeConsAllVectors,HistoryLookup.NativeProof.evaluateHead,Nat.pred_succ,recursiveEval]
  rfl

theorem tableEval (count right : Nat) :
    evaluate table (count ::ᵥ right ::ᵥ nil) = Encodable.encode (values right count) := by
  induction count with
  | zero =>
      change evaluate HistoryCodec.cons (right ::ᵥ 0 ::ᵥ nil) = _
      rw [HistoryCodec.NativeProof.nativeConsAllVectors]
      rfl
  | succ count ih =>
      change evaluate HistoryCodec.cons
        (evaluate value (count ::ᵥ evaluate table (count ::ᵥ right ::ᵥ nil) ::ᵥ right ::ᵥ nil) ::ᵥ
          evaluate table (count ::ᵥ right ::ᵥ nil) ::ᵥ nil) = _
      rw [ih,valueEval,HistoryCodec.NativeProof.nativeConsAllVectors]
      rfl

theorem appendEval (left right : Nat) :
    evaluate append (left ::ᵥ right ::ᵥ nil) = result right left := by
  change evaluate HistoryLookup.head (evaluate table (left ::ᵥ right ::ᵥ nil) ::ᵥ nil) = _
  rw [tableEval]
  cases left with
  | zero => exact HistoryLookup.NativeProof.headCons right []
  | succ n => exact HistoryLookup.NativeProof.headCons (newValue n (values right n)) (values right n)

theorem tableGet (right count index : Nat) (h : index ≤ count) :
    (values right count)[index]? = some (result right (count-index)) := by
  induction count generalizing index with
  | zero =>
      have hz : index = 0 := by omega
      subst index
      rfl
  | succ count ih => cases index with
    | zero => rfl
    | succ index =>
        simpa only [values,List.getElem?_cons_succ,Nat.succ_sub_succ_eq_sub] using ih index (by omega)

theorem resultCons (a left right : Nat) :
    result right (Nat.pair a left).succ = (Nat.pair a (result right left)).succ := by
  change newValue (Nat.pair a left) (values right (Nat.pair a left)) = _
  rw [newValue,Nat.unpair_pair]
  have hl := Nat.right_le_pair a left
  rw [tableGet right (Nat.pair a left) (Nat.pair a left-left) (Nat.sub_le _ _)]
  have he : Nat.pair a left - (Nat.pair a left-left) = left := by omega
  rw [he]
  rfl

theorem nativeHistoryAppend : Targets.NativeHistoryAppend := by
  intro left right
  rw [appendEval]
  induction left with
  | nil => rfl
  | cons a left ih =>
      rw [HistoryLookup.NativeProof.encodeCons,resultCons,ih]
      rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.NativeProof
