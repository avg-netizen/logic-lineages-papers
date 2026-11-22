module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowAddressAlgorithm (typeBit)
open NumberedWindowSyntaxAlgorithm (syntaxBits termParts termNext table)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparsePathEnvelope (run field)
open NumberedWindowInternalAuxExchangeMemoStepTargets (TermSyntaxCalibrated currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalAuxMeasureStepTargets (certain shapeCheck childAt earlierAt measureAt offsetAt)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets

open NumberedWindowInternalCoverAuxSyntaxTargets

private theorem lengthSyntax (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlierSyntax {i n : Nat} (h : i < n) : (table n)[i]? = some (syntaxBits i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases before : i < n
    · simp only [table,List.getElem?_append_left (lengthSyntax n ▸ before)]
      exact ih before
    · have last : i = n := by omega
      subst i
      change (table n ++ [syntaxBits n])[n]? = some (syntaxBits n)
      simpa only [lengthSyntax] using
        (List.getElem?_concat_length (l := table n) (a := syntaxBits n))

private theorem readSyntax {i n : Nat} (h : i < n) :
    (table n).getD i (false,false) = syntaxBits i := by
  rw [List.getD_eq_getElem?_getD,earlierSyntax h]
  rfl

private theorem current (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

theorem exact_CoverAuxSyntaxSource : ExactCoverAuxSyntaxSource := by
  intro raw dom cod fn arg read
  have fnSmall := (nodeBounds read).2 fn (by simp)
  have argSmall := (nodeBounds read).2 arg (by simp)
  refine ⟨fnSmall,argSmall,?_⟩
  change termNext raw (table raw) = _
  simp only [termNext,read,Option.any_some,termParts,readSyntax fnSmall,readSyntax argSmall]

private theorem shape (i old : Nat) : evaluate shapeCheck (args i old) = 1 ↔
    ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) := by
  rw [shapeCheck,unaryValue,current,termOne]

private theorem selectField (j i old value : Nat)
    (found : run (field j) (i+1) = value) : evaluate (childAt j) (args i old) = value := by
  rw [childAt,unaryValue,current]
  exact found

private theorem lookupValue (slot i old q : Nat)
    (selected : evaluate (childAt slot) (args i old) = q) :
    evaluate (measureAt slot) (args i old) = evaluate lookup ((i-q) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,selected]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (q ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

private theorem earlier (slot i old v : Nat) (selected : evaluate (childAt slot) (args i old) = v)
    (small : v < i+1) : evaluate (earlierAt slot) (args i old) = 1 := by
  rw [earlierAt,binaryValue,selected,current,exactLessThanEvaluation,if_pos small]

theorem exact_CoverAuxSyntaxStepCalibration : ExactCoverAuxSyntaxStepCalibration := by
  intro V T cv ct i old previous
  change evaluate (auxSyntaxUpdate V T) (args i old) = (syntaxBits (i+1)).1.toNat
  rw [auxSyntaxUpdate,evalBranch]
  by_cases aux : ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg])
  · obtain ⟨dom,cod,fn,arg,read⟩ := aux
    obtain ⟨fnSmall,argSmall,actual⟩ := exact_CoverAuxSyntaxSource (i+1) dom cod fn arg read
    have fs := termFields read
    have d := selectField 0 i old dom fs.1
    have c := selectField 1 i old cod fs.2.1
    have f := selectField 2 i old fn fs.2.2.1
    have a := selectField 3 i old arg fs.2.2.2
    have guard : evaluate certain (args i old) = 1 := by
      simp only [certain,conjunctionOne]
      exact ⟨(shape i old).mpr ⟨dom,cod,fn,arg,read⟩,
        earlier 2 i old fn f fnSmall,earlier 3 i old arg a argSmall⟩
    rw [guard,if_neg (by decide),actual]
    simp only [auxAccept,actualConjunctionEvaluation,typeAt,unaryValue,d,c,ct dom,ct cod,
      lookupValue 2 i old fn f,lookupValue 3 i old arg a,previous fn fnSmall,previous arg argSmall]
    cases typeBit dom <;> cases typeBit cod <;> cases (syntaxBits fn).1 <;> cases (syntaxBits arg).1 <;> decide
  · have miss : evaluate shapeCheck (args i old) ≠ 1 := fun pass => aux ((shape i old).mp pass)
    have guard : evaluate certain (args i old) = 0 := by
      rw [certain,actualConjunctionEvaluation]
      simp [miss]
    rw [guard,if_pos rfl,unaryValue,current]
    exact cv (i+1)

private theorem selectedRow (V T : Program 1) (cv : TermSyntaxCalibrated V) (ct : TypeSyntaxCalibrated T)
    (n : Nat) :
    evaluate (scratchRow (constantZero 2) (auxSyntaxUpdate V T)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) =
      (syntaxBits n).1.toNat := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      apply exact_CoverAuxSyntaxStepCalibration V T cv ct
      intro child small
      rw [lookupAt (constantZero 2) (auxSyntaxUpdate V T) (0 ::ᵥ 0 ::ᵥ nil)
        i child (Nat.le_of_lt_succ small)]
      exact ih child small

theorem exact_CoverAuxSyntaxCalibration : ExactCoverAuxSyntaxCalibration := by
  intro V T cv ct n
  unfold auxSyntax run
  rw [selectedMeasure,compositeThree]
  exact selectedRow V T cv ct n

#print axioms exact_CoverAuxSyntaxSource
#print axioms exact_CoverAuxSyntaxStepCalibration
#print axioms exact_CoverAuxSyntaxCalibration

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxRowNumericProof
