module

public import LogicLineages.PersistentMarking.NumberedWindowFunctionalOrderedSplitBoundaryProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectCoreCalibrationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountNumericChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFunctionalRawUnionNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitNumericProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open NumberedWindowFieldAlgorithm (unpack pack packNode unpackNode)
open NumberedWindowDirectAlgorithm (direct readWitness)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralCountNumericChecks (exact_OriginalLiteralCountFit)
open NumberedWindowInternalDirectCoreCalibrationProof (exact_OriginalDirectCoreNumeric)
open NumberedWindowFunctionalOrderedSplitBoundaryProof
  (allScalars noInsertions exact_ReorderedDeletionAccepted DeletionOrUnchanged exact_NoOrderedRecombination)
open NumberedWindowInternalFunctionalRawUnionNumericProof
  (exact_FunctionalUnionUnpackPack exact_FunctionalRawUnionNumeric)
open NumberedWindowInternalFunctionalRawUnion (functionalUnion)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (nodeOfCell cellAt)

def scalar : Program 1 := InternalLessThan.constantOne 1
def relation : Program 3 := InternalAcceptance.constantZero 3
def checker : Program 3 := dCore scalar relation permutation
def witness : Nat := packNode 5 [pack [1,0],pack [0],pack []]

private theorem actual (s w t : Nat) :
    evaluate checker (s ::ᵥ w ::ᵥ t ::ᵥ nil) = (direct allScalars noInsertions s w t).toNat :=
  exact_OriginalDirectCoreNumeric scalar relation permutation allScalars noInsertions
    (fun _ => rfl) (fun _ _ _ => rfl) exact_OriginalLiteralCountFit s w t

private theorem successfulWitness : readWitness witness = some ([1,0],[0],[]) := by
  have p : unpackNode witness = some (5,[pack [1,0],pack [0],pack []]) := by
    unfold witness packNode
    rw [nodeOfCell (cellAt 5 (pack [pack [1,0],pack [0],pack []])),
      exact_FunctionalUnionUnpackPack]
    rfl
  unfold readWitness
  rw [p]
  simp [Option.bind,exact_FunctionalUnionUnpackPack,NumberedWindowDirectAlgorithm.entries]

theorem exact_LiteralCheckerReorderedDeletion :
    evaluate checker (pack [0,0,1] ::ᵥ witness ::ᵥ pack [1,0] ::ᵥ nil) = 1 := by
  rw [actual,direct,exact_FunctionalUnionUnpackPack,exact_FunctionalUnionUnpackPack,successfulWitness]
  exact congrArg Bool.toNat exact_ReorderedDeletionAccepted

/-- An actual strict step, or unchanged equality, cannot introduce an occurrence
outside its source when the installed positive relation is constantly zero. -/
theorem exact_DecodedDeletionSide (src : List Nat) (t : Nat)
    (side : t = pack src ∨ ∃ w, evaluate checker (pack src ::ᵥ w ::ᵥ t ::ᵥ nil) = 1) :
    ∃ ys, unpack t = some ys ∧ DeletionOrUnchanged src ys := by
  rcases side with eq | ⟨w,edge⟩
  · exact ⟨src,eq ▸ exact_FunctionalUnionUnpackPack src,Or.inl rfl⟩
  · rw [actual,direct,exact_FunctionalUnionUnpackPack] at edge
    cases hw : readWitness w <;> cases ht : unpack t <;> rw [hw,ht] at edge <;> try contradiction
    rename_i wit ys
    have good : NumberedWindowDirectAlgorithm.directLists allScalars noInsertions src ys wit = true :=
      by cases e : NumberedWindowDirectAlgorithm.directLists allScalars noInsertions src ys wit <;>
        simp_all
    exact ⟨ys,rfl,Or.inr ⟨wit,good⟩⟩

/-- Exact numeric form of the split failure: even two merely nonincreasing
parts cannot produce the installed ordered union value. -/
theorem exact_LiteralCheckerNoOrderedSplit (a b : Nat)
    (left : a = pack [0,0] ∨ ∃ w, evaluate checker (pack [0,0] ::ᵥ w ::ᵥ a ::ᵥ nil) = 1)
    (right : b = pack [1] ∨ ∃ w, evaluate checker (pack [1] ::ᵥ w ::ᵥ b ::ᵥ nil) = 1) :
    evaluate functionalUnion (a ::ᵥ b ::ᵥ nil) ≠ pack [1,0] := by
  obtain ⟨xs,hx,dx⟩ := exact_DecodedDeletionSide [0,0] a left
  obtain ⟨ys,hy,dy⟩ := exact_DecodedDeletionSide [1] b right
  intro h
  rw [exact_FunctionalRawUnionNumeric a b xs ys hx hy] at h
  have e := congrArg unpack h
  rw [exact_FunctionalUnionUnpackPack,exact_FunctionalUnionUnpackPack] at e
  exact exact_NoOrderedRecombination xs ys dx dy (Option.some.inj e)

#print axioms exact_LiteralCheckerReorderedDeletion
#print axioms exact_DecodedDeletionSide
#print axioms exact_LiteralCheckerNoOrderedSplit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralOrderedSplitNumericProof
