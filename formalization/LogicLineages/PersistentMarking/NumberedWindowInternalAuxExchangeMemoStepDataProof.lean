module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof
  (vectorOne compositeTwo compositeThree literalEvaluation)
open NumberedWindowInternalSparseFieldCell (cellGood chosenCell)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
  (flagOfCell headTailOfCell noFlagOfNone)
open NumberedWindowInternalSparseRawFunctionFrame (frameGood frameSlot onRaw)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape atSlot)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (guardReports termFields)
open NumberedWindowAtomicRawStepFieldProof (nodePacked)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalAuxExchangeMemoTargets (auxFields guardedAuxChildren)
open NumberedWindowInternalAuxExchangeMemoStepTargets

abbrev args (i old : Nat) : List.Vector Nat 4 := i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil

theorem unaryValue (p : Program 1) (q : Program 4) (xs : List.Vector Nat 4) :
    evaluate (unaryAfter p q) xs = run p (evaluate q xs) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => evaluate q xs) = _
  rw [vectorOne] <;> rfl

theorem binaryValue (p : Program 2) (q r : Program 4) (xs : List.Vector Nat 4) :
    evaluate (binaryAfter p q r) xs = evaluate p (evaluate q xs ::ᵥ evaluate r xs ::ᵥ nil) :=
  compositeTwo p q r xs

theorem conjunctionOne {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs = 1 ↔ evaluate p xs = 1 ∧ evaluate q xs = 1 := by
  rw [actualConjunctionEvaluation]
  split <;> simp_all

theorem conjunctionBit {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (conjunction p q) xs = 0 ∨ evaluate (conjunction p q) xs = 1 := by
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem currentValue (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem packedValue (i old : Nat) : evaluate packedKey (args i old) = i+1+1 := by
  rw [packedKey,unaryValue,currentValue] <;> rfl

private theorem rawCell (i : Nat) : chosenCell (i+1+1) = decode (i+1) := allInput.2 (i+1)

theorem missingKey (i old : Nat) (missing : decode (i+1) = none) :
    evaluate goodKey (args i old) = 0 := by
  have flag := noFlagOfNone ((rawCell i).trans missing)
  rw [goodKey,actualConjunctionEvaluation,unaryValue,packedValue]
  simp [flag]

theorem foundKey (i old a b : Nat) (found : decode (i+1) = some (a,b)) :
    evaluate goodKey (args i old) = 1 ∧ evaluate rawSource (args i old) = a ∧
      evaluate rawTarget (args i old) = b := by
  have cell := (rawCell i).trans found
  have fields := headTailOfCell cell
  constructor
  · rw [goodKey,conjunctionOne,unaryValue,packedValue]
    exact ⟨flagOfCell cell,rfl⟩
  · constructor
    · rw [rawSource,unaryValue,packedValue]; exact fields.1
    · rw [rawTarget,unaryValue,packedValue]; exact fields.2

private theorem frameValue (i old a b : Nat) (p : Program 3)
    (left : evaluate rawSource (args i old) = a) (right : evaluate rawTarget (args i old) = b) :
    evaluate (atFrame p) (args i old) = evaluate p (tape a dummyWitnessCode b) := by
  rw [atFrame,compositeThree,literalEvaluation,left,right]

abbrev ActualAuxPair (a b f g : Nat) : Prop :=
  ∃ dom cod arg, unpackNode a = some (6,[dom,cod,f,arg]) ∧ unpackNode b = some (6,[dom,cod,g,arg])

private theorem fieldsRead {n dom cod fn arg : Nat} (found : auxFields n = some (dom,cod,fn,arg)) :
    unpackNode n = some (6,[dom,cod,fn,arg]) := by
  unfold auxFields at found
  split at found
  next d c f u read =>
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    rcases found with ⟨rfl,rfl,rfl,rfl⟩
    exact read
  next => cases found

theorem auxChoice (a b f g : Nat) : guardedAuxChildren a b = some (f,g) ↔
    (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true ∧ ActualAuxPair a b f g := by
  constructor
  · intro found
    cases left : auxFields a with
    | none => simp [guardedAuxChildren,left] at found
    | some ab =>
      rcases ab with ⟨dom,cod,fn,arg⟩
      cases right : auxFields b with
      | none => simp [guardedAuxChildren,left,right] at found
      | some bb =>
        rcases bb with ⟨dom',cod',fn',arg'⟩
        have chosen : (if dom = dom' ∧ cod = cod' ∧ arg = arg' ∧
            (syntaxBits a).1 = true ∧ (syntaxBits b).1 = true then some (fn,fn') else none) =
            some (f,g) := by
          simpa only [guardedAuxChildren,left,right,Option.bind_eq_bind,Option.bind_some] using found
        split at chosen
        next checked =>
          obtain ⟨rfl,rfl,rfl,validA,validB⟩ := checked
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj chosen)
          exact ⟨validA,validB,dom,cod,arg,fieldsRead left,fieldsRead right⟩
        next => cases chosen
  · rintro ⟨validA,validB,dom,cod,arg,left,right⟩
    simp [guardedAuxChildren,auxFields,left,right,validA,validB]

theorem frameOne (i old a b : Nat) (left : evaluate rawSource (args i old) = a)
    (right : evaluate rawTarget (args i old) = b) :
    evaluate (atFrame frameGood) (args i old) = 1 ↔ ∃ f g, ActualAuxPair a b f g := by
  rw [frameValue i old a b _ left right,guardReports]
  constructor
  · rintro ⟨f,_,g,d,c,u,_,ha,hb⟩
    exact ⟨f,g,d,c,u,ha,hb⟩
  · rintro ⟨f,g,d,c,u,ha,hb⟩
    exact ⟨f,0,g,d,c,u,nodePacked 5 [0],ha,hb⟩

private theorem childValue (i old a b f g : Nat) (left : evaluate rawSource (args i old) = a)
    (right : evaluate rawTarget (args i old) = b) (frame : ActualAuxPair a b f g) :
    evaluate childKey (args i old) = pair f g := by
  obtain ⟨d,c,u,ha,hb⟩ := frame
  have first : evaluate (atFrame (frameSlot 2 0)) (args i old) = f := by
    rw [frameValue i old a b _ left right]
    change evaluate (onRaw (NumberedWindowInternalSparsePathEnvelope.field 2) 0)
      (tape a dummyWitnessCode b) = f
    rw [atSlot]
    exact (termFields ha).2.2.1
  have second : evaluate (atFrame (frameSlot 2 2)) (args i old) = g := by
    rw [frameValue i old a b _ left right]
    change evaluate (onRaw (NumberedWindowInternalSparsePathEnvelope.field 2) 2)
      (tape a dummyWitnessCode b) = g
    rw [atSlot]
    exact (termFields hb).2.2.1
  rw [childKey,binaryValue,first,second]
  exact NumberedWindowInternalSparsePairEvaluationProof.pairValue f g

theorem childReports (i old a b f g : Nat) (left : evaluate rawSource (args i old) = a)
    (right : evaluate rawTarget (args i old) = b) (report : ActualAuxPair a b f g) :
    (evaluate childEarlier (args i old) = 1 ↔ pair f g < i+1) ∧
      evaluate childResult (args i old) = evaluate lookup ((i-pair f g) ::ᵥ old ::ᵥ nil) := by
  have atChild := childValue i old a b f g left right report
  constructor
  · rw [childEarlier,binaryValue,currentValue,atChild,exactLessThanEvaluation]
    split <;> simp_all
  · rw [childResult,binaryValue,childLag,binaryValue,atChild]
    change evaluate lookup
      (evaluate InternalEqualityTest.subtract (pair f g ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
    rw [exactSubtractionEvaluation]

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
