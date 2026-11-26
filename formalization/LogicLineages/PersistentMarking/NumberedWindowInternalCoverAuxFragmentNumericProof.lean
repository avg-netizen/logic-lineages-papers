module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericRowProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalLessThan (constantOne)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax auxSyntaxUpdate)
open NumberedWindowInternalCoverAuxFragmentGuardTargets (fragmentLeaf fragmentGuard)
open NumberedWindowInternalCoverAuxFragmentNumericRowProof (exact_CoverAuxFragmentNumericRow)
open NumberedWindowInternalCoverAuxFragmentNumericTargets

private abbrev R : Program 4 := auxSyntaxUpdate fragmentLeaf (constantOne 1)
private abbrev tape (raw : Nat) : List.Vector Nat 3 := raw ::ᵥ 0 ::ᵥ 0 ::ᵥ nil
private abbrev row (raw : Nat) : Nat := evaluate (scratchRow (constantZero 2) R) (tape raw)
private abbrev old (i : Nat) : Nat := evaluate (scratchTable (constantZero 2) R) (tape i)

private theorem selectedRow (raw : Nat) : run fragmentGuard raw = row raw := by
  unfold fragmentGuard auxSyntax run
  rw [selectedMeasure,compositeThree] <;> rfl

private theorem seed : row 0 = 0 := by
  unfold row tape
  rw [rowZero] <;> rfl

private theorem step (i : Nat) : row (i+1) = fragmentRow i (old i) := by
  unfold row tape
  rw [rowSucc] <;> rfl

private theorem earlier (i child : Nat) (less : child < i+1) :
    sourceLookup i (old i) child = row child :=
  lookupAt (constantZero 2) R (0 ::ᵥ 0 ::ᵥ nil) i child (Nat.le_of_lt_succ less)

private theorem sourceCases {raw : Nat} (good : SourceFragment raw) :
    (0 < raw ∧ ¬ HasAuxPayload raw ∧ ¬ HasLambdaPayload raw) ∨
      ∃ dom cod fn arg, unpackNode raw = some (6,[dom,cod,fn,arg]) ∧
        SourceFragment fn ∧ SourceFragment arg :=
  match good with
  | .terminal prior noAux noLambda => .inl ⟨Nat.zero_lt_succ prior,noAux,noLambda⟩
  | .fork _ dom cod fn arg packing first second => .inr ⟨dom,cod,fn,arg,packing,first,second⟩

private theorem sourcePositive {raw : Nat} (good : SourceFragment raw) : 0 < raw := by
  rcases sourceCases good with ⟨positive,_,_⟩ | ⟨dom,cod,fn,arg,packing,_,_⟩
  · exact positive
  · exact Nat.zero_lt_of_lt ((nodeBounds packing).2 fn (by simp))

private theorem sourceFork {raw dom cod fn arg : Nat}
    (packing : unpackNode raw = some (6,[dom,cod,fn,arg])) :
    SourceFragment raw ↔ SourceFragment fn ∧ SourceFragment arg := by
  constructor
  · intro good
    rcases sourceCases good with ⟨_,noAux,_⟩ | ⟨d,c,actualFn,actualArg,actual,gfn,garg⟩
    · exact False.elim (noAux ⟨dom,cod,fn,arg,packing⟩)
    · have fields : [dom,cod,fn,arg] = [d,c,actualFn,actualArg] :=
        congrArg Prod.snd (Option.some.inj (packing.symm.trans actual))
      have sameFn : fn = actualFn := by
        have value := congrArg (fun xs : List Nat => xs.getD 2 0) fields
        change fn = actualFn at value
        exact value
      have sameArg : arg = actualArg := by
        have value := congrArg (fun xs : List Nat => xs.getD 3 0) fields
        change arg = actualArg at value
        exact value
      rw [sameFn,sameArg]
      exact ⟨gfn,garg⟩
  · rintro ⟨gfn,garg⟩
    exact .fork raw dom cod fn arg packing gfn garg

private theorem sourceTerminal (i : Nat) (miss : ¬ HasAuxPayload (i+1)) :
    SourceFragment (i+1) ↔ ¬ HasLambdaPayload (i+1) := by
  constructor
  · intro good
    rcases sourceCases good with ⟨_,_,noLambda⟩ | ⟨dom,cod,fn,arg,packed,_,_⟩
    · exact noLambda
    · exact False.elim (miss ⟨dom,cod,fn,arg,packed⟩)
  · intro noLambda
    exact .terminal i miss noLambda

private theorem exactRow (raw : Nat) : row raw = 1 ↔ SourceFragment raw := by
  induction raw using Nat.strongRecOn with
  | ind raw ih =>
    cases raw with
    | zero =>
      rw [seed]
      constructor
      · intro impossible
        omega
      · intro accepted
        have impossible := sourcePositive accepted
        omega
    | succ i =>
      rw [step]
      have h := exact_CoverAuxFragmentNumericRow i (old i)
      by_cases has : HasAuxPayload (i+1)
      · obtain ⟨dom,cod,fn,arg,packed⟩ := has
        have fnSmall := (nodeBounds packed).2 fn (by simp)
        have argSmall := (nodeBounds packed).2 arg (by simp)
        rw [h.1 dom cod fn arg packed,earlier i fn fnSmall,earlier i arg argSmall,
          ih fn fnSmall,ih arg argSmall,sourceFork packed]
      · rw [h.2.1 has,sourceTerminal i has]

theorem exact_CoverAuxFragmentNumericSource : ExactCoverAuxFragmentNumericSource := by
  refine ⟨(selectedRow 0).trans seed, ?_, ?_⟩
  · intro raw
    rw [selectedRow]
    cases raw with
    | zero => exact Or.inl seed
    | succ i =>
      rw [step]
      exact (exact_CoverAuxFragmentNumericRow i (old i)).2.2
  · intro raw
    rw [selectedRow]
    exact exactRow raw

#print axioms exact_CoverAuxFragmentNumericSource

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxFragmentNumericProof
