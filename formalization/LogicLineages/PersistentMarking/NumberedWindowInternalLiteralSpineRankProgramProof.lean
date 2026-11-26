module
public import LogicLineages.PersistentMarking.NumberedWindowInternalTransparentAuxRankTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralExchangeSpineRankProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawGuardProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameNumericParseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoStepDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanEvaluationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSpineRankProgramProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch constantZero)
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open InternalEqualityTestEvaluationProof (exactSubtractionEvaluation)
open InternalLessThanEvaluationProof (exactLessThanEvaluation)
open InternalRawListRecursion (lookup)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowNeutralSpineRankAlgorithm (rawRank next row tableEarlier)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (nodePacked codeOfNode)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds)
open NumberedWindowInternalLiteralAtomicRawGuardProof (freeTest bottomTest freeCode bottomCode)
open NumberedWindowInternalSparsePathEnvelope (run nodeGood field)
open NumberedWindowInternalSparseRawFunctionFrameNumericParseProof (termOne termFields)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (literalEvaluation compositeThree)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey)
open NumberedWindowInternalAuxExchangeMemoStepDataProof (args unaryValue binaryValue conjunctionOne)
open NumberedWindowInternalAuxMeasureStepTargets (shapeCheck earlierAt measureAt childAt offsetAt)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalTransparentAuxRankTargets
open NumberedWindowInternalLiteralExchangeSpineRankProof (exact_RawRankAux)

def spineRankLeaf : Program 1 :=
  branch freeTest (branch bottomTest (constantZero 1) (literal 1 1)) (literal 1 2)

private theorem nodeBit (tag arity q : Nat) :
    run (nodeGood (literal 1 tag) arity) q = 0 ∨ run (nodeGood (literal 1 tag) arity) q = 1 := by
  unfold run nodeGood
  rw [actualConjunctionEvaluation]
  split <;> simp

private theorem zeroUnlessFree (q : Nat) (no : ¬∃ t n, q = freeRaw t n) : run freeTest q = 0 := by
  rcases nodeBit 0 2 q with h | h
  · exact h
  · exact False.elim (no ((freeCode q).mp h))

private theorem zeroUnlessBottom (q : Nat) (no : ¬∃ t, q = bottomRaw t) : run bottomTest q = 0 := by
  rcases nodeBit 3 1 q with h | h
  · exact h
  · exact False.elim (no ((bottomCode q).mp h))

private theorem two {xs : List Nat} (h : xs.length = 2) : ∃ a b, xs = [a,b] := by
  rcases xs with _ | ⟨a,_ | ⟨b,_ | ⟨c,cs⟩⟩⟩ <;> simp_all

private theorem one {xs : List Nat} (h : xs.length = 1) : ∃ a, xs = [a] := by
  rcases xs with _ | ⟨a,_ | ⟨b,bs⟩⟩ <;> simp_all

theorem exact_SpineRankLeaf (q : Nat)
    (notAux : ¬∃ dom cod fn arg, unpackNode q = some (6,[dom,cod,fn,arg])) :
    run spineRankLeaf q = rawRank q := by
  have reading : run spineRankLeaf q = (if run freeTest q = 0 then
      (if run bottomTest q = 0 then 0 else 1) else 2) := by
    unfold run spineRankLeaf
    rw [evalBranch,evalBranch,literalEvaluation,literalEvaluation]
    rfl
  rw [reading]
  by_cases isFree : ∃ t n, q = freeRaw t n
  · obtain ⟨t,n,rfl⟩ := isFree
    have checked := (freeCode (freeRaw t n)).mpr ⟨t,n,rfl⟩
    have read : unpackNode (freeRaw t n) = some (0,[t,n]) := nodePacked 0 [t,n]
    simp [checked,rawRank,next,read,row]
  · rw [zeroUnlessFree q isFree,if_pos rfl]
    by_cases isBottom : ∃ t, q = bottomRaw t
    · obtain ⟨t,rfl⟩ := isBottom
      have checked := (bottomCode (bottomRaw t)).mpr ⟨t,rfl⟩
      have read : unpackNode (bottomRaw t) = some (3,[t]) := nodePacked 3 [t]
      simp [checked,rawRank,next,read,row]
    · rw [zeroUnlessBottom q isBottom,if_pos rfl]
      unfold rawRank next
      cases code : unpackNode q with
      | none => rfl
      | some name =>
        obtain ⟨tag,fs⟩ := name
        simp only [Option.map_some,Option.getD_some,row]
        have a : ¬(tag = 0 ∧ fs.length = 2) := by
          rintro ⟨rfl,h⟩
          obtain ⟨t,n,rfl⟩ := two h
          exact isFree ⟨t,n,codeOfNode code⟩
        have b : ¬(tag = 3 ∧ fs.length = 1) := by
          rintro ⟨rfl,h⟩
          obtain ⟨t,rfl⟩ := one h
          exact isBottom ⟨t,codeOfNode code⟩
        have c : ¬(tag = 6 ∧ fs.length = 4) := by
          rintro ⟨rfl,h⟩
          rcases fs with _ | ⟨d,_ | ⟨c,_ | ⟨f,_ | ⟨u,_ | ⟨e,es⟩⟩⟩⟩⟩
            <;> simp_all
        rw [if_neg a,if_neg b,if_neg c]

private theorem currentValue (i old : Nat) : evaluate currentKey (args i old) = i+1 := by
  rw [currentKey,unaryValue] <;> rfl

private theorem shape (i old : Nat) : evaluate shapeCheck (args i old) = 1 ↔
    ∃ dom cod fn arg, unpackNode (i+1) = some (6,[dom,cod,fn,arg]) := by
  rw [shapeCheck,unaryValue,currentValue,termOne]

private theorem childValue (i old f : Nat) (value : run (field 2) (i+1) = f) :
    evaluate (childAt 2) (args i old) = f := by
  rw [childAt,unaryValue,currentValue]
  exact value

private theorem earlier (i old child : Nat) (report : evaluate (childAt 2) (args i old) = child)
    (bound : child < i+1) : evaluate (earlierAt 2) (args i old) = 1 := by
  rw [earlierAt,binaryValue,report,currentValue,exactLessThanEvaluation,if_pos bound]

private theorem stored (i old child : Nat) (report : evaluate (childAt 2) (args i old) = child) :
    evaluate (measureAt 2) (args i old) = evaluate lookup ((i-child) ::ᵥ old ::ᵥ nil) := by
  rw [measureAt,binaryValue,offsetAt,binaryValue,report]
  change evaluate lookup (evaluate InternalEqualityTest.subtract (child ::ᵥ i ::ᵥ nil) ::ᵥ old ::ᵥ nil) = _
  rw [exactSubtractionEvaluation]

private theorem rowFit (g : Program 1)
    (base : ∀ n, (¬∃ d c f u, unpackNode n = some (6,[d,c,f,u])) → run g n = rawRank n)
    (n : Nat) :
    evaluate (scratchRow (constantZero 2) (rankUpdate g)) (n ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = rawRank n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero => rw [rowZero]; rfl
    | succ i =>
      rw [rowSucc]
      let R := rankUpdate g
      let old := evaluate (NumberedWindowInternalSparseFieldParser.scratchTable (constantZero 2) R)
        (i ::ᵥ 0 ::ᵥ 0 ::ᵥ nil)
      change evaluate (rankUpdate g) (args i old) = rawRank (i+1)
      rw [rankUpdate,evalBranch]
      by_cases aux : ∃ d c f u, unpackNode (i+1) = some (6,[d,c,f,u])
      · obtain ⟨d,c,f,u,read⟩ := aux
        have small := (nodeBounds read).2 f (by simp)
        have code := childValue i old f (termFields read).2.2.1
        have pass : evaluate rankGuard (args i old) = 1 := by
          simp only [rankGuard,conjunctionOne]
          exact ⟨(shape i old).mpr ⟨d,c,f,u,read⟩,earlier i old f code small⟩
        have prev : evaluate (measureAt 2) (args i old) = rawRank f := by
          rw [stored i old f code]
          change evaluate lookup ((i-f) ::ᵥ evaluate
            (NumberedWindowInternalSparseFieldParser.scratchTable (constantZero 2) R)
              (i ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) ::ᵥ nil) = _
          rw [lookupAt (constantZero 2) R (0 ::ᵥ 0 ::ᵥ nil) i f (Nat.le_of_lt_succ small)]
          exact ih f small
        rw [pass,if_neg (by decide),rankAtFn,evalBranch,unaryValue,prev]
        change (if rawRank f = 0 then 0 else rawRank f+1) = _
        exact (exact_RawRankAux (i+1) d c f u read).symm
      · have missed : evaluate shapeCheck (args i old) ≠ 1 := fun h => aux ((shape i old).mp h)
        have nope : evaluate rankGuard (args i old) = 0 := by
          rw [rankGuard,actualConjunctionEvaluation]
          simp [missed]
        rw [nope,if_pos rfl,unaryValue,currentValue]
        exact base (i+1) aux

/-- A genuine structural rank callback at all raw inputs. The physical
success at a tag-six node uses its original strictly earlier child
row; only non-auxiliary shapes use the explicit atomic fallback. -/
theorem exact_LiteralSpineRankProgram : RankCalibrated (auxRank spineRankLeaf) := by
  intro n
  rw [auxRank,selectedMeasure,compositeThree]
  exact rowFit spineRankLeaf exact_SpineRankLeaf n

#print axioms exact_SpineRankLeaf
#print axioms exact_LiteralSpineRankProgram
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSpineRankProgramProof
