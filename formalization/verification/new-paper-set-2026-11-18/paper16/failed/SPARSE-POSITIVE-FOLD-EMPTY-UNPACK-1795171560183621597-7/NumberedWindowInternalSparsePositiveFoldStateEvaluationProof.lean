module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalListCodec (consCode headCode tailCode)
open InternalListCodecEvaluationProof (consEvaluation headEvaluation tailEvaluation)
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualAdvanceCalibration encodeState packedOriginalAdvance)
open NumberedWindowInternalSparsePositiveFold
open NumberedWindowInternalSparsePositiveFoldTargets (encodeScratch)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseFieldCell (cellHead cellTail)

abbrev eval6 (p : Program 6) (counter old c ty start orig : Nat) : Nat :=
  evaluate p (counter ::ᵥ old ::ᵥ c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil)

theorem vectorFour (f : Fin 4 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m =>
    Fin.cases ?_ (fun n => Fin.elim0 n) m) l) k) i <;> simp <;> rfl

theorem vectorFive (f : Fin 5 → Nat) :
    List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ f 3 ::ᵥ f 4 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => Fin.cases ?_ (fun m =>
    Fin.cases ?_ (fun n => Fin.cases ?_ (fun u => Fin.elim0 u) n) m) l) k) i <;> simp <;> rfl

theorem scratchHead (cursor current : Nat) : run headCode (encodeScratch cursor current) = cursor := by
  unfold run
  rw [headEvaluation]
  simp [encodeScratch,Nat.add_comm 1]

theorem scratchTail (cursor current : Nat) : run tailCode (encodeScratch cursor current) = current := by
  unfold run
  rw [tailEvaluation]
  simp [encodeScratch,Nat.add_comm 1]

theorem initialValue (c ty start orig : Nat) :
    evaluate initial (c ::ᵥ ty ::ᵥ start ::ᵥ orig ::ᵥ nil) = encodeScratch orig start := by
  unfold initial
  rw [evaluate,vectorTwo]
  change evaluate consCode (orig ::ᵥ start ::ᵥ nil) = _
  rw [consEvaluation] <;> rfl

theorem cursorValue (k cursor current c ty start orig : Nat) :
    eval6 scratchCursor k (encodeScratch cursor current) c ty start orig = cursor := by
  unfold scratchCursor eval6
  rw [evaluate,vectorOne]
  exact scratchHead cursor current

theorem currentValue (k cursor current c ty start orig : Nat) :
    eval6 scratchCurrent k (encodeScratch cursor current) c ty start orig = current := by
  unfold scratchCurrent eval6
  rw [evaluate,vectorOne]
  exact scratchTail cursor current

theorem onCursorValue (p : Program 1) (k cursor current c ty start orig : Nat) :
    eval6 (onCursor p) k (encodeScratch cursor current) c ty start orig = run p cursor := by
  unfold onCursor eval6
  rw [evaluate,vectorOne]
  change run p (eval6 scratchCursor k (encodeScratch cursor current) c ty start orig) = _
  rw [cursorValue]

theorem deadValue (k old c ty start orig : Nat) :
    eval6 dead k old c ty start orig = encodeScratch 0 0 := by
  unfold dead eval6
  rw [evaluate,vectorTwo]
  change evaluate consCode ((0 : Nat) ::ᵥ 0 ::ᵥ nil) = _
  rw [consEvaluation] <;> rfl

theorem advanceValue (raw : Program 5) (least : Program 3) (k cursor current c ty start orig : Nat) :
    eval6 (advanceAtCell raw least) k (encodeScratch cursor current) c ty start orig =
      evaluate (advance raw least) (c ::ᵥ ty ::ᵥ current ::ᵥ run cellHead cursor ::ᵥ nil) := by
  unfold advanceAtCell eval6
  rw [evaluate,vectorFour]
  change evaluate (advance raw least) (c ::ᵥ ty ::ᵥ
    eval6 scratchCurrent k (encodeScratch cursor current) c ty start orig ::ᵥ
    eval6 (onCursor cellHead) k (encodeScratch cursor current) c ty start orig ::ᵥ nil) = _
  rw [currentValue,onCursorValue]

theorem updateValue (raw : Program 5) (least : Program 3) (k cursor current c ty start orig : Nat) :
    eval6 (updateCell raw least) k (encodeScratch cursor current) c ty start orig =
      encodeScratch (run cellTail cursor)
        (evaluate (advance raw least) (c ::ᵥ ty ::ᵥ current ::ᵥ run cellHead cursor ::ᵥ nil)) := by
  unfold updateCell eval6
  rw [evaluate,vectorTwo]
  change evaluate consCode (eval6 (onCursor cellTail) k (encodeScratch cursor current) c ty start orig ::ᵥ
    eval6 (advanceAtCell raw least) k (encodeScratch cursor current) c ty start orig ::ᵥ nil) = _
  rw [onCursorValue,advanceValue,consEvaluation] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldStateEvaluationProof
