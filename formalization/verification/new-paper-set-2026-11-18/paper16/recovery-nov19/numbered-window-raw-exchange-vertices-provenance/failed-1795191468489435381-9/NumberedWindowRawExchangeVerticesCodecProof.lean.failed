module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (step steps finish unpack unpackNode)
open NumberedWindowRawExchangeVerticesTargets

private theorem components (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  let s := a+b
  have atMost : s ≤ s*s := by
    by_cases hz : s = 0
    · rw [hz]; exact Nat.le_refl 0
    · have one : 1 ≤ s := by omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s one
  have hb : b ≤ s := by dsimp [s]; omega
  change a ≤ s*s+a ∧ b ≤ s*s+a
  constructor <;> omega

theorem decoded {n a b : Nat} (ok : decode n = some (a,b)) :
    pair a b = n ∧ a ≤ n ∧ b ≤ n := by
  have same : pair a b = n := by
    unfold decode at ok
    exact of_decide_eq_true
      (List.find?_some (p := fun p : Nat × Nat => decide (pair p.1 p.2 = n)) ok)
  have h := components a b
  rw [same] at h
  exact ⟨same,h⟩

private theorem squareGap {s t : Nat} (h : s < t) : s*s+s < t*t := by
  have before : s+1 ≤ t := Nat.succ_le_of_lt h
  have sq := Nat.mul_le_mul before before
  have expanded : (s+1)*(s+1) = s*s+s+s+1 := by
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
    omega
  rw [expanded] at sq
  omega

theorem samePair {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  let s := a+b
  let t := c+d
  have raw : s*s+a = t*t+c := h
  have hs : a ≤ s := by dsimp [s]; omega
  have ht : c ≤ t := by dsimp [t]; omega
  have same : s = t := by
    rcases Nat.lt_trichotomy s t with lt | eq | gt
    · have gap := squareGap lt
      omega
    · exact eq
    · have gap := squareGap gt
      omega
  rw [same] at raw
  have ha : a = c := Nat.add_left_cancel raw
  have hb : b = d := by dsimp [s,t] at same; omega
  exact ⟨ha,hb⟩

theorem childKeyLt {x y a b : Nat} (hx : x < a) (hy : y ≤ b) :
    pair x y < pair a b := by
  have sumLe : x+y ≤ a+b := Nat.add_le_add (Nat.le_of_lt hx) hy
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul sumLe sumLe) hx

theorem failedSteps (fuel : Nat) : steps fuel none = none := by
  induction fuel with
  | zero => rfl
  | succ n ih => exact ih

private theorem boundedSteps (fuel limit rest : Nat) (acc out : List Nat)
    (hrest : rest ≤ limit) (hacc : ∀ x ∈ acc, x < limit)
    (ok : finish (steps fuel (some (rest,acc))) = some out) :
    ∀ x ∈ out, x < limit := by
  induction fuel generalizing rest acc with
  | zero =>
    cases rest with
    | zero =>
      have same : acc.reverse = out := by simpa [steps,finish] using ok
      intro x hx
      rw [← same] at hx
      exact hacc x (List.mem_reverse.mp hx)
    | succ n => simp [steps,finish] at ok
  | succ fuel ih =>
    cases rest with
    | zero =>
      exact ih 0 acc hrest hacc (by simpa only [steps,step] using ok)
    | succ n =>
      cases found : decode n with
      | none => simp [steps,step,found,failedSteps,finish] at ok
      | some p =>
        rcases p with ⟨h,t⟩
        have actual : finish (steps fuel (some (t,h::acc))) = some out := by
          simpa [steps,step,found] using ok
        obtain ⟨_,hh,ht⟩ := decoded found
        have small : t ≤ limit := Nat.le_trans ht (Nat.le_trans (Nat.le_succ n) hrest)
        have first : h < limit := Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hh) hrest
        apply ih t (h::acc) small _ actual
        intro x hx
        rcases List.mem_cons.mp hx with same | prior
        · exact same.symm ▸ first
        · exact hacc x prior

theorem unpacked {n : Nat} {xs : List Nat} (h : unpack n = some xs) :
    ∀ x ∈ xs, x < n :=
  boundedSteps n n n [] xs (Nat.le_refl _) (by simp) h

theorem nodeBounds {n tag : Nat} {xs : List Nat} (h : unpackNode n = some (tag,xs)) :
    0 < n ∧ ∀ x ∈ xs, x < n := by
  cases n with
  | zero => simp [unpackNode] at h
  | succ n =>
    cases found : decode n with
    | none => simp [unpackNode,found] at h
    | some p =>
      rcases p with ⟨rawTag,body⟩
      cases fields : unpack body with
      | none => simp [unpackNode,found,fields] at h
      | some row =>
        have same : (rawTag,row) = (tag,xs) := by simpa [unpackNode,found,fields] using h
        have eqFields : row = xs := congrArg Prod.snd same
        subst xs
        refine ⟨Nat.zero_lt_succ n,?_⟩
        intro x hx
        have below := unpacked fields x hx
        exact Nat.lt_trans below (Nat.lt_succ_of_le (decoded found).2.2)

theorem getFieldLt {n tag : Nat} {xs : List Nat} (h : unpackNode n = some (tag,xs)) (k : Nat) :
    xs.getD k 0 < n := by
  rw [List.getD_eq_getElem?_getD]
  cases got : xs[k]? with
  | none => exact (nodeBounds h).1
  | some x => exact (nodeBounds h).2 x (List.mem_of_getElem? got)

theorem exactBounds : ExactOriginalRawFieldBounds :=
  ⟨fun _ _ _ => decoded,fun _ _ _ _ => samePair,fun _ _ => unpacked,fun _ _ _ => nodeBounds⟩

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
