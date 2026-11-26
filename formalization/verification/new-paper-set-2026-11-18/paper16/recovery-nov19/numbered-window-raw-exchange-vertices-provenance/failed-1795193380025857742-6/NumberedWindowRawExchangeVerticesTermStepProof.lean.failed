module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesExchangeTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgumentsProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTermStepProof
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (declaration)
open NumberedWindowExchangeAtoms (HeadPairs allowed bag)
open NumberedWindowExchangeAlgorithm (table termNext row parts)
open NumberedWindowCoverBoundsAlgorithm (bounds termMeasure)
open NumberedWindowRawExchangeVerticesCodecProof (getFieldLt)
open NumberedWindowRawExchangeVerticesBoundsTableProof (previous termBounds)
open NumberedWindowRawExchangeVerticesArgumentsProof (bagBounds)
open NumberedWindowRawExchangeVerticesExchangeTableProof
  (EarlierAgreement successfulView earlierTerm earlierArgs)

private theorem measureFromParts (hp : HeadPairs) (a b tag : Nat) (xs ys : List Nat)
    (readA : unpackNode a = some (tag,xs)) (readB : unpackNode b = some (tag,ys))
    (inductionAt : EarlierAgreement hp a b)
    (reported : parts hp (table hp (pair a b)) tag tag xs ys = true) :
    (bounds a).1 = (bounds b).1 := by
  let x := fun i => xs.getD i 0
  let y := fun i => ys.getD i 0
  let earlier := fun i => (table hp (pair a b)).getD (pair (x i) (y i)) (false,false)
  have rawA (i : Nat) : (NumberedWindowCoverBoundsAlgorithm.table a).getD (x i) default = bounds (x i) :=
    previous (getFieldLt readA i)
  have rawB (i : Nat) : (NumberedWindowCoverBoundsAlgorithm.table b).getD (y i) default = bounds (y i) :=
    previous (getFieldLt readB i)
  have term (i : Nat) (ok : (earlier i).1 = true) : (bounds (x i)).1 = (bounds (y i)).1 :=
    earlierTerm hp inductionAt (getFieldLt readA i) (getFieldLt readB i) ok
  have args (i : Nat) (ok : (earlier i).2 = true) : (bounds (x i)).2 = (bounds (y i)).2 :=
    earlierArgs hp inductionAt (getFieldLt readA i) (getFieldLt readB i) ok
  rw [termBounds readA,termBounds readB]
  rcases tag with _ | _ | _ | _ | _ | _ | _ | other
  · simp [parts] at reported
  · simp [parts] at reported
  · have ok : x 0 = y 0 ∧ (earlier 1).1 = true := by
      simpa [parts,x,y,earlier,Bool.and_eq_true,beq_iff_eq] using reported
    have child : (bounds (x 1)).1 = (bounds (y 1)).1 := term 1 ok.2
    simp only [termMeasure,rawA 1,rawB 1,child]
  · simp [parts] at reported
  · have ok :
        (allowed hp (x 0) (y 0) = true ∧
          (declaration (x 0)).1 = (declaration (y 0)).1 ∧ bag (x 1) (y 1) = true) ∨
        (x 0 = y 0 ∧ (earlier 1).2 = true) := by
      simpa [parts,x,y,earlier,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using reported
    have child : (bounds (x 1)).2 = (bounds (y 1)).2 := by
      rcases ok with head | step
      · exact bagBounds head.2.2
      · exact args 1 step.2
    simp only [termMeasure,rawA 1,rawB 1,child]
  · have ok : x 1 = y 1 ∧ x 2 = y 2 ∧
        ((allowed hp (x 0) (y 0) = true ∧ bag (x 3) (y 3) = true ∧ x 4 = y 4) ∨
        (x 0 = y 0 ∧ (((earlier 3).2 = true ∧ x 4 = y 4) ∨ (x 3 = y 3 ∧ (earlier 4).2 = true)))) := by
      simpa [parts,x,y,earlier,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using reported
    have same : (bounds (x 3)).2 = (bounds (y 3)).2 ∧ (bounds (x 4)).2 = (bounds (y 4)).2 := by
      rcases ok.2.2 with ⟨_,bagged,unchanged⟩ | ⟨_,moved⟩
      · exact ⟨bagBounds bagged,congrArg (fun n => (bounds n).2) unchanged⟩
      · rcases moved with ⟨first,unchanged⟩ | ⟨unchanged,second⟩
        · exact ⟨args 3 first,congrArg (fun n => (bounds n).2) unchanged⟩
        · exact ⟨congrArg (fun n => (bounds n).2) unchanged,args 4 second⟩
    have mark : xs.getD 2 0 = ys.getD 2 0 := ok.2.1
    simp only [termMeasure,rawA 3,rawA 4,rawB 3,rawB 4,same.1,same.2,mark]
  · have ok : x 0 = y 0 ∧ x 1 = y 1 ∧
        (((earlier 2).1 = true ∧ x 3 = y 3) ∨ (x 2 = y 2 ∧ (earlier 3).1 = true)) := by
      simpa [parts,x,y,earlier,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,and_assoc] using reported
    have both : (bounds (x 2)).1 = (bounds (y 2)).1 ∧ (bounds (x 3)).1 = (bounds (y 3)).1 := by
      rcases ok.2.2 with ⟨first,unchanged⟩ | ⟨unchanged,second⟩
      · exact ⟨term 2 first,congrArg (fun n => (bounds n).1) unchanged⟩
      · exact ⟨congrArg (fun n => (bounds n).1) unchanged,term 3 second⟩
    simp only [termMeasure,rawA 2,rawA 3,rawB 2,rawB 3,both.1,both.2]
  · simp [parts] at reported

theorem termStep (hp : HeadPairs) (a b : Nat) (inductionAt : EarlierAgreement hp a b)
    (h : (row hp a b).1 = true) : (bounds a).1 = (bounds b).1 := by
  rw [successfulView hp a b (Or.inl h)] at h
  unfold termNext at h
  cases ha : unpackNode a with
  | none => simp [ha] at h
  | some asNode =>
    rcases asNode with ⟨i,xs⟩
    cases hb : unpackNode b with
    | none => simp [ha,hb] at h
    | some bsNode =>
      rcases bsNode with ⟨j,ys⟩
      have checked : parts hp (table hp (pair a b)) i j xs ys = true := by
        simpa [ha,hb] using h
      have same : i = j := by
        by_cases same : i = j
        · exact same
        · simp [parts,same] at checked
      subst j
      exact measureFromParts hp a b i xs ys ha hb inductionAt checked

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTermStepProof
