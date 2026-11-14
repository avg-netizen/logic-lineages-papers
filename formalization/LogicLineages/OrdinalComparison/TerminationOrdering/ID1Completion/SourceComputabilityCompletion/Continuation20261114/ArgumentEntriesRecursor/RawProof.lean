module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeSelectedRecursor.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.RawProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (numbersNumber)

theorem consChildren (raw : Nat) (h : tagValue raw = 7) :
    ArgumentEntriesFrontier.rawChildren raw = [firstValue raw,secondValue raw] := by
  simp [ArgumentEntriesFrontier.rawChildren,arityValue,h]

theorem tailDecrease (raw : Nat) (h : tagValue raw = 7) : secondValue raw < raw :=
  ArgumentEntriesFrontier.Proof.rawDecrease raw (secondValue raw) (by simp [consChildren raw h])

noncomputable def kernel (raw : Nat) (rec : ∀ child, child < raw → Nat) : Nat :=
  evaluate ArgumentEntriesLayer.step (List.Vector.ofFn ![raw,
    if h : tagValue raw = 7 then rec (secondValue raw) (tailDecrease raw h) else 0])
noncomputable def rawValue : Nat → Nat := Nat.lt_wfRel.wf.fix kernel

theorem rawValueEquation (raw : Nat) : rawValue raw =
    evaluate ArgumentEntriesLayer.step (List.Vector.ofFn ![raw,
      if tagValue raw = 7 then rawValue (secondValue raw) else 0]) := by
  rw [rawValue,WellFounded.fix_eq]
  unfold kernel
  split_ifs <;> rfl

def layerAt (raw : Nat) (answers : List Nat) (_param : Nat) : Option Nat :=
  some (evaluate ArgumentEntriesLayer.step (List.Vector.ofFn ![raw,answers.getD 1 0]))

theorem rankValue (raw param : Nat) : evaluate rank (List.Vector.ofFn ![raw,param]) = raw := rfl

theorem dependencyValue (raw param : Nat) :
    evaluate dependency (List.Vector.ofFn ![raw,param]) =
      numbersNumber (ArgumentEntriesFrontier.rawChildren raw) :=
  ArgumentEntriesFrontier.Proof.dependencyValue raw param

theorem layerValue (raw param : Nat) (answers : List Nat) :
    evaluate layer (List.Vector.ofFn ![raw,numbersNumber answers,param]) =
      Encodable.encode (layerAt raw answers param) := by
  change evaluate ArgumentEntriesLayer.recombine (List.Vector.ofFn ![raw,numbersNumber answers]) = _
  rw [ArgumentEntriesLayer.recombine,succOfEvaluation,binaryCompositionEvaluation]
  have ht : evaluate ArgumentEntriesLayer.tailAnswer (List.Vector.ofFn ![raw,numbersNumber answers]) =
      answers.getD 1 0 := by
    rw [ArgumentEntriesLayer.tailAnswer,binaryCompositionEvaluation,constantEvaluation]
    change evaluate InternalRawListRecursion.lookup (1 ::ᵥ numbersNumber answers ::ᵥ List.Vector.nil) = _
    exact ExchangeAnswerSlots.NativeProof.lookupEncoded 1 answers
  rw [ht]
  rfl

theorem stepIgnoresTail (raw a b : Nat) (h : tagValue raw ≠ 7) :
    evaluate ArgumentEntriesLayer.step (List.Vector.ofFn ![raw,a]) =
      evaluate ArgumentEntriesLayer.step (List.Vector.ofFn ![raw,b]) := by
  rw [ArgumentEntriesLayer.NativeProof.stepValue,ArgumentEntriesLayer.NativeProof.stepValue]
  change (if tagValue raw = 6 then _ else if tagValue raw = 7 then _ else _) = _
  by_cases h6 : tagValue raw = 6 <;> simp [tagValue] at h h6 ⊢ <;> simp_all

theorem layerCoherence (raw param : Nat) :
    layerAt raw ((ArgumentEntriesFrontier.rawChildren raw).map rawValue) param = some (rawValue raw) := by
  unfold layerAt
  congr 1
  rw [rawValueEquation]
  by_cases h : tagValue raw = 7
  · rw [consChildren raw h]
    simp only [List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero,if_pos h]
  · rw [if_neg h]
    exact stepIgnoresTail raw _ 0 h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.RawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesRecursor.RawProof
