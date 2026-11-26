module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.NativeProof
open GorbowPRProgram List.Vector

theorem evaluateHead (code : Nat) :
    evaluate head (code ::ᵥ nil) = (Nat.unpair code.pred).1 := by
  change evaluate (HistoryDecoder.decoder false)
    (evaluate HistoryCodec.predecessor (code ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryCodec.NativeProof.evaluatePredecessor,HistoryDecoder.NativeProof.evaluateDecoder]
  rfl

theorem evaluateTail (code : Nat) :
    evaluate tail (code ::ᵥ nil) = (Nat.unpair code.pred).2 := by
  change evaluate (HistoryDecoder.decoder true)
    (evaluate HistoryCodec.predecessor (code ::ᵥ nil) ::ᵥ nil) = _
  rw [HistoryCodec.NativeProof.evaluatePredecessor,HistoryDecoder.NativeProof.evaluateDecoder]
  rfl

theorem encodeCons {α : Type} [Encodable α] (a : α) (l : List α) :
    Encodable.encode (a::l) = (Nat.pair (Encodable.encode a) (Encodable.encode l)).succ := rfl

theorem tailList {α : Type} [Encodable α] (l : List α) :
    evaluate tail (Encodable.encode l ::ᵥ nil) = Encodable.encode l.tail := by
  cases l with
  | nil => rw [evaluateTail]; rfl
  | cons a l => rw [encodeCons,evaluateTail,Nat.pred_succ,Nat.unpair_pair]; rfl

theorem headCons {α : Type} [Encodable α] (a : α) (l : List α) :
    evaluate head (Encodable.encode (a::l) ::ᵥ nil) = Encodable.encode a := by
  rw [encodeCons,evaluateHead,Nat.pred_succ,Nat.unpair_pair]

theorem tailDrop {α : Type} (n : Nat) (l : List α) : (l.drop n).tail = l.drop (n+1) := by
  induction n generalizing l with
  | zero => cases l <;> rfl
  | succ n ih => cases l with
    | nil => rfl
    | cons a l => exact ih l

theorem evaluateDrop {α : Type} [Encodable α] (index : Nat) (l : List α) :
    evaluate drop (index ::ᵥ Encodable.encode l ::ᵥ nil) = Encodable.encode (l.drop index) := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change evaluate tail (evaluate drop (index ::ᵥ Encodable.encode l ::ᵥ nil) ::ᵥ nil) = _
      rw [ih,tailList,tailDrop]

theorem referenceList {α : Type} [Encodable α] (l : List α) :
    evaluate reference (Encodable.encode l ::ᵥ nil) = Encodable.encode l.head? := by
  change evaluate HistoryCodec.select (Encodable.encode l ::ᵥ 0 ::ᵥ
    (evaluate head (Encodable.encode l ::ᵥ nil)).succ ::ᵥ nil) = _
  rw [HistoryCodec.NativeProof.evaluateSelect]
  cases l with
  | nil => rfl
  | cons a l => rw [headCons,encodeCons]; rfl

theorem headDrop {α : Type} (index : Nat) (l : List α) : (l.drop index).head? = l[index]? := by
  induction index generalizing l with
  | zero => cases l <;> rfl
  | succ index ih => cases l with
    | nil => rfl
    | cons a l => exact ih l

theorem nativeHistoryLookup : Targets.NativeHistoryLookup := by
  intro index history
  change evaluate reference (evaluate drop (index ::ᵥ Encodable.encode history ::ᵥ nil) ::ᵥ nil) = _
  rw [evaluateDrop,referenceList,headDrop]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLookup.NativeProof
