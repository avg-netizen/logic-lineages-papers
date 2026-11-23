module
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRawRankProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepFieldProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankCalibrationProof
open NumberedWindowFieldAlgorithm (unpack unpackNode packNode)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparsePathEnvelopeCellEvaluationProof (noNode nodeOfCell codeOfCell packOfUnpack)
open NumberedWindowNeutralSpineRankAlgorithm
open NumberedWindowNeutralSpineRawRankProof (NeutralSpineRank)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowAtomicRawStepFieldProof (freeView bottomView)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationTableProof (auxView)
open NumberedWindowRawExchangeVerticesCodecProof (exactBounds)

private theorem physical (q tag : Nat) (fields : List Nat) (read : unpackNode q = some (tag,fields)) :
    packNode tag fields = q := by
  cases hc : chosenCell q with
  | none => rw [noNode hc] at read; cases read
  | some pair =>
    rcases pair with ⟨a,t⟩
    rw [nodeOfCell hc] at read
    cases ht : unpack t with
    | none => rw [ht] at read; cases read
    | some fs =>
      rw [ht] at read
      have same : (a,fs) = (tag,fields) := Option.some.inj read
      obtain ⟨hat,hfs⟩ := Prod.mk.inj same
      rw [← hat,← hfs,packNode,← packOfUnpack t ht]
      exact (codeOfCell hc).symm

private theorem fieldEarlier (q tag : Nat) (fields : List Nat) (x : Nat)
    (read : unpackNode q = some (tag,fields)) (mem : x ∈ fields) : x < q :=
  (exactBounds.2.2.2 q tag fields read).2 x mem

private theorem auxRow (prior : List Nat) (dom cod fn arg : Nat) :
    row prior 6 [dom,cod,fn,arg] =
      if prior.getD fn 0 = 0 then 0 else prior.getD fn 0 + 1 := rfl

/-- Forward literal agreement at every real original neutral spine. -/
theorem exact_RawNeutralRankFromShape {q n : Nat} (pure : NeutralSpineRank q n) :
    rawRank q = n+1 := by
  induction pure with
  | free ty name => simp [rawRank,next,freeView,row]
  | bottom ty => simp [rawRank,next,bottomView,row]
  | @aux fn n dom cod arg more ih =>
    let q := auxRaw dom cod fn arg
    have b := fieldEarlier q 6 [dom,cod,fn,arg] fn (auxView dom cod fn arg) (by simp)
    have lookup := tableEarlier fn q b
    change rawRank q = n+1+1
    have seen : unpackNode q = some (6,[dom,cod,fn,arg]) := auxView dom cod fn arg
    rw [rawRank,next,seen,Option.map_some,Option.getD_some,auxRow,lookup,ih,
      if_neg (Nat.succ_ne_zero n)]

/-- A positive report must come from a literal original neutral spine.
No implicitly accepted shape or external interpretation is inserted. -/
theorem exact_RawNeutralShapeFromRank (q : Nat) : ∀ n, rawRank q = n+1 → NeutralSpineRank q n := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
    intro n h
    cases seen : unpackNode q with
    | none => simp [rawRank,next,seen] at h
    | some p =>
      obtain ⟨tag,fields⟩ := p
      have eq := physical q tag fields seen
      have hr : row (table q) tag fields = n+1 := by simpa only [rawRank,next,seen,Option.map_some,Option.getD_some] using h
      by_cases hf : tag = 0 ∧ fields.length = 2
      · obtain ⟨rfl,len⟩ := hf
        obtain ⟨a,b,form⟩ : ∃ a b, fields = [a,b] :=
          ⟨_,_,List.eq_getElem_of_length_eq_two fields len⟩
        have value : n = 1 := by simp [row,form] at hr; omega
        rw [← eq,form,value]
        exact .free a b
      by_cases hb : tag = 3 ∧ fields.length = 1
      · obtain ⟨rfl,len⟩ := hb
        obtain ⟨a,form⟩ := List.length_eq_one_iff.mp len
        have value : n = 0 := by simp [row,form] at hr; omega
        rw [← eq,form,value]
        exact .bottom a
      by_cases ha : tag = 6 ∧ fields.length = 4
      · obtain ⟨rfl,len⟩ := ha
        obtain ⟨dom,cod,fn,arg,form⟩ : ∃ a b c d, fields = [a,b,c,d] :=
          ⟨_,_,_,_,List.eq_getElem_of_length_eq_four fields len⟩
        have smaller := fieldEarlier q 6 fields fn seen (by simp [form])
        have v := tableEarlier fn q smaller
        rw [form,auxRow,v] at hr
        have hv := hr
        cases found : rawRank fn with
        | zero => simp [found] at hv
        | succ m =>
          have value : n = m+1 := by simp [found] at hv; omega
          rw [← eq,form,value]
          exact .aux dom cod arg (ih fn smaller m found)
      · simp [row,hf,hb,ha] at hr

theorem exact_OriginalRawNeutralRankIff (q n : Nat) : rawRank q = n+1 ↔ NeutralSpineRank q n :=
  ⟨exact_RawNeutralShapeFromRank q n,exact_RawNeutralRankFromShape⟩

#print axioms exact_RawNeutralRankFromShape
#print axioms exact_RawNeutralShapeFromRank
#print axioms exact_OriginalRawNeutralRankIff
end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankCalibrationProof
