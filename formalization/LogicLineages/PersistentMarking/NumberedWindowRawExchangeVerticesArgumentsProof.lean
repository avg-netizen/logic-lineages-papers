module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgumentsProof
open NumberedWindowPairAlgorithm (decode)
open NumberedWindowFieldAlgorithm (step steps finish unpack)
open NumberedWindowCoverBoundsAlgorithm (Measure bounds table argsNext)
open NumberedWindowExchangeAtoms (bag)
open NumberedWindowRawExchangeVerticesTargets
open NumberedWindowRawExchangeVerticesCodecProof (decoded failedSteps)
open NumberedWindowRawExchangeVerticesBoundsTableProof (previous)

private def merge (a b : Measure) : Measure := (a.1+b.1,max a.2 b.2)
private def cell (q : Nat) : Measure := ((bounds q).1.1 + 1,(bounds q).1.2)

private theorem mergeZero (m : Measure) : merge m (0,0) = m := by
  cases m
  simp [merge]

private theorem zeroMerge (m : Measure) : merge (0,0) m = m := by
  cases m
  simp [merge]

private theorem mergeAssoc (a b c : Measure) : merge (merge a b) c = merge a (merge b c) := by
  simp only [merge,Nat.add_assoc,Nat.max_assoc]

private theorem foldAppend (xs ys : List Nat) :
    argsFold (xs ++ ys) = merge (argsFold xs) (argsFold ys) := by
  induction xs with
  | nil => exact (zeroMerge (argsFold ys)).symm
  | cons x xs ih =>
    change merge (cell x) (argsFold (xs++ys)) = merge (merge (cell x) (argsFold xs)) (argsFold ys)
    rw [ih,mergeAssoc]

private theorem foldPermutation {xs ys : List Nat} (h : xs.Perm ys) :
    argsFold xs = argsFold ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    change merge (cell x) _ = merge (cell x) _
    rw [ih]
  | swap a b tail =>
    apply Prod.ext
    · simp only [argsFold]
      omega
    · simp only [argsFold,Nat.max_left_comm]
  | trans _ _ ha hb => exact ha.trans hb

theorem argsCell {n head tail : Nat} (parsed : decode n = some (head,tail)) :
    (bounds (n+1)).2 = ((bounds head).1.1+1+(bounds tail).2.1,max (bounds head).1.2 (bounds tail).2.2) := by
  have headLt : head < n+1 := Nat.lt_succ_of_le (decoded parsed).2.1
  have tailLt : tail < n+1 := Nat.lt_succ_of_le (decoded parsed).2.2
  change argsNext (n+1) (table (n+1)) = _
  rw [argsNext,parsed]
  change (((table (n+1)).getD head default).1.1+1+((table (n+1)).getD tail default).2.1,
    max ((table (n+1)).getD head default).1.2 ((table (n+1)).getD tail default).2.2) = _
  rw [previous headLt,previous tailLt]

private theorem foldSteps (fuel rest : Nat) (acc xs : List Nat)
    (h : finish (steps fuel (some (rest,acc))) = some xs) :
    merge (argsFold acc.reverse) (bounds rest).2 = argsFold xs := by
  induction fuel generalizing rest acc with
  | zero =>
    cases rest with
    | zero =>
      have same : acc.reverse = xs := by simpa [steps,finish] using h
      rw [← same]
      exact mergeZero _
    | succ n => simp [steps,finish] at h
  | succ fuel ih =>
    cases rest with
    | zero => exact ih 0 acc (by simpa only [steps,step] using h)
    | succ n =>
      cases found : decode n with
      | none => simp [steps,step,found,failedSteps,finish] at h
      | some p =>
        rcases p with ⟨head,tail⟩
        have actual : finish (steps fuel (some (tail,head::acc))) = some xs := by
          simpa [steps,step,found] using h
        have row := ih tail (head::acc) actual
        rw [List.reverse_cons,foldAppend,mergeAssoc] at row
        have single : argsFold [head] = cell head := mergeZero (cell head)
        have fields : (bounds (n+1)).2 = merge (cell head) (bounds tail).2 := argsCell found
        rw [single,← fields] at row
        exact row

theorem actualFold {n : Nat} {xs : List Nat} (h : unpack n = some xs) :
    (bounds n).2 = argsFold xs := by
  have row := foldSteps n n [] xs h
  change merge (0,0) (bounds n).2 = argsFold xs at row
  simpa only [zeroMerge] using row

theorem bagBounds {a b : Nat} (h : bag a b = true) :
    (bounds a).2 = (bounds b).2 := by
  unfold bag at h
  cases ha : unpack a with
  | none => simp [ha] at h
  | some xs =>
    cases hb : unpack b with
    | none => simp [ha,hb] at h
    | some ys =>
      have perm : xs.Perm ys := by simpa [ha,hb] using h
      rw [actualFold ha,actualFold hb]
      exact foldPermutation perm

theorem exactArguments : ExactOriginalRawArgsBounds :=
  ⟨fun _ _ => actualFold,fun _ _ => bagBounds⟩

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesArgumentsProof
