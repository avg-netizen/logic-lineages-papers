module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
open LogicLineages.ComputabilityKnowledge LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (Measure)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureMemoTargets
open NumberedWindowInternalAuxMeasureMemoChecks (exact_AuxMeasureCalibration)
open NumberedWindowInternalAuxMeasureStepTargets

theorem exact_CombineProgram : ExactCombineProgram := by
  let Input := List.Vector Nat 2
  have decodePrim : Primrec readMeasure := Primrec.option_getD.comp Primrec.decode (Primrec.const (0,0))
  have fn : Primrec (fun xs : Input => readMeasure xs.head) := decodePrim.comp Primrec.vector_head
  have arg : Primrec (fun xs : Input => readMeasure xs.tail.head) :=
    decodePrim.comp (Primrec.vector_head.comp Primrec.vector_tail)
  let nodes := Primrec.succ.comp (Primrec.nat_add.comp (Primrec.fst.comp fn) (Primrec.fst.comp arg))
  let maxNumeral := Primrec.nat_max.comp (Primrec.snd.comp fn) (Primrec.snd.comp arg)
  have value : Primrec (fun xs : Input => combine xs.head xs.tail.head) :=
    Primrec.encode.comp (nodes.pair maxNumeral)
  obtain ⟨P,actual⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 2 _ value
  exact ⟨P,fun f a => actual (f ::ᵥ a ::ᵥ nil)⟩

private theorem currentValue (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem shape (i old : Nat) : evaluate shapeCheck (args i old) = 1 ↔
    ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) := by
  rw [shapeCheck,unaryValue,currentValue,termOne]

private theorem childAtValue (slot i old f : Nat) (value : run (NumberedWindowInternalSparsePathEnvelope.field slot) (i+1) = f) :
    evaluate (childAt slot) (args i old) = f := by
  rw [childAt,unaryValue,currentValue]
  exact value

private theorem earlier (slot i old child : Nat) (report : evaluate (childAt slot) (args i old) = child)
    (bound : child < i+1) : evaluate (earlierAt slot) (args i old) = 1 := by
  rw [earlierAt,binaryValue,report,currentValue,exactLessThanEvaluation,if_pos bound]

private theorem actualMeasure (slot i old child : Nat) (report : evaluate (childAt slot) (args i old) = child) :
    evaluate (measureAt slot) (args i old) = evaluate lookup ((i-child) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,report]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (child ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

theorem exact_PhysicalAuxMeasureStep : ExactPhysicalAuxMeasureStep := by
  intro base P combiner i old
  change evaluate (measureUpdate base P) (args i old) = measureStepValue base i old
  rw [measureUpdate,evalBranch]
  by_cases aux : ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg])
  · obtain ⟨dom,cod,fn,arg,read⟩ := aux
    have checked := (shape i old).mpr ⟨dom,cod,fn,arg,read⟩
    have fields := termFields read
    have fnOut := childAtValue 2 i old fn fields.2.2.1
    have argOut := childAtValue 3 i old arg fields.2.2.2
    have fnSmall := (nodeBounds read).2 fn (by simp)
    have argSmall := (nodeBounds read).2 arg (by simp)
    have admitted : evaluate certain (args i old) = 1 := by
      simp only [certain,conjunctionOne]
      exact ⟨checked,earlier 2 i old fn fnOut fnSmall,earlier 3 i old arg argOut argSmall⟩
    rw [admitted,if_neg (by decide),binaryValue,actualMeasure 2 i old fn fnOut,actualMeasure 3 i old arg argOut]
    have smaller : fn < i+1 ∧ arg < i+1 := ⟨fnSmall,argSmall⟩
    rw [measureStepValue,read,if_pos smaller]
    exact combiner (evaluate lookup ((i-fn) ::ᵥ old ::ᵥ nil)) (evaluate lookup ((i-arg) ::ᵥ old ::ᵥ nil))
  · have missed : evaluate shapeCheck (args i old) ≠ 1 := fun h => aux ((shape i old).mp h)
    have rejected : evaluate certain (args i old) = 0 := by
      rw [certain,actualConjunctionEvaluation]
      simp [missed]
    rw [rejected,if_pos rfl,unaryValue,currentValue]
    unfold measureStepValue
    split
    next dom cod fn arg read => exact False.elim (aux ⟨dom,cod,fn,arg,read⟩)
    next => rfl

theorem exact_PhysicalAuxMeasure : ExactPhysicalAuxMeasure := by
  intro base P original combineCal
  exact exact_AuxMeasureCalibration base (measureUpdate base P) original
    (exact_PhysicalAuxMeasureStep base P combineCal)

#print axioms exact_CombineProgram
#print axioms exact_PhysicalAuxMeasureStep
#print axioms exact_PhysicalAuxMeasure

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepChecks
