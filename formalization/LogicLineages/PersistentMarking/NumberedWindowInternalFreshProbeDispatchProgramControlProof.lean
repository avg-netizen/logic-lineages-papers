module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramTargets
public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
open NumberedWindowInternalFreshProbeDispatchProgram
open NumberedWindowInternalFreshProbeDispatchProgramTargets
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector

theorem vectorOne (f : Fin 1 → Nat) : List.Vector.ofFn f = f 0 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  obtain rfl := Fin.eq_zero i
  simp

theorem vectorTwo (f : Fin 2 → Nat) : List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp <;> rfl
  · obtain rfl := Fin.eq_zero j
    simp <;> rfl

theorem vectorThree (f : Fin 3 → Nat) : List.Vector.ofFn f = f 0 ::ᵥ f 1 ::ᵥ f 2 ::ᵥ nil := by
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
  · simp <;> rfl
  · simp <;> rfl
  · obtain rfl := Fin.eq_zero k
    simp <;> rfl

theorem compositeOne {n : Nat} (p : Program 1) (a : Program n) (xs : List.Vector Nat n) :
    evaluate (.composition p (Fin.cons a Fin.elim0)) xs =
      evaluate p (evaluate a xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 1 =>
    evaluate ((Fin.cons a Fin.elim0 : Fin 1 → Program n) i) xs) = _
  rw [vectorOne] <;> rfl

theorem compositeTwo {n : Nat} (p : Program 2) (a b : Program n) (xs : List.Vector Nat n) :
    evaluate (.composition p (Fin.cons a (Fin.cons b Fin.elim0))) xs =
      evaluate p (evaluate a xs ::ᵥ evaluate b xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 2 =>
    evaluate ((Fin.cons a (Fin.cons b Fin.elim0) : Fin 2 → Program n) i) xs) = _
  rw [vectorTwo] <;> rfl

theorem compositeThree {n : Nat} (p : Program 3) (a b c : Program n) (xs : List.Vector Nat n) :
    evaluate (.composition p (Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0)))) xs =
      evaluate p (evaluate a xs ::ᵥ evaluate b xs ::ᵥ evaluate c xs ::ᵥ nil) := by
  change evaluate p (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((Fin.cons a (Fin.cons b (Fin.cons c Fin.elim0)) : Fin 3 → Program n) i) xs) = _
  rw [vectorThree] <;> rfl

theorem zeroEvaluation {n : Nat} (xs : List.Vector Nat n) : evaluate (zeroAt n) xs = 0 := rfl

theorem literalEvaluation (n k : Nat) (xs : List.Vector Nat n) : evaluate (literal n k) xs = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.succ (evaluate (literal n k) xs) = Nat.succ k
    rw [ih]

theorem predEvaluation (x : Nat) : evaluate predOne (x ::ᵥ nil) = x.pred := by
  cases x <;> rfl

private theorem subEvaluation (x y : Nat) : evaluate truncatedSubtraction (x ::ᵥ y ::ᵥ nil) = y-x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    change evaluate predOne (List.Vector.ofFn fun _ : Fin 1 =>
      evaluate truncatedSubtraction (x ::ᵥ y ::ᵥ nil)) = y-(x+1)
    rw [vectorOne,predEvaluation,ih,Nat.pred_eq_sub_one]
    omega

private theorem zeroTestEvaluation (x : Nat) :
    evaluate GorbowPRInternalControl.zeroTest (x ::ᵥ nil) = if x = 0 then 1 else 0 := by
  cases x with
  | zero => simp [GorbowPRInternalControl.zeroTest,GorbowPRInternalControl.one,evaluate]
  | succ x => simp [GorbowPRInternalControl.zeroTest,GorbowPRInternalControl.zeroStep,evaluate]

private theorem conditionalEvaluation (x a b : Nat) :
    evaluate GorbowPRInternalControl.conditional (x ::ᵥ a ::ᵥ b ::ᵥ nil) = if x = 0 then a else b := by
  cases x <;> rfl

private theorem reverseSubEvaluation (x y : Nat) :
    evaluate reversedSubtraction (x ::ᵥ y ::ᵥ nil) = x-y := by
  rw [reversedSubtraction,compositeTwo]
  exact subEvaluation y x

private theorem reverseZeroEvaluation (x y : Nat) :
    evaluate reversedZeroTest (x ::ᵥ y ::ᵥ nil) = if x-y = 0 then 1 else 0 := by
  change evaluate GorbowPRInternalControl.zeroTest (List.Vector.ofFn fun _ : Fin 1 =>
    evaluate reversedSubtraction (x ::ᵥ y ::ᵥ nil)) = _
  rw [vectorOne,zeroTestEvaluation,reverseSubEvaluation]

theorem compareEvaluation (x y : Nat) :
    evaluate compareNumbers (x ::ᵥ y ::ᵥ nil) = if x = y then 1 else 0 := by
  rw [compareNumbers,compositeThree,conditionalEvaluation,subEvaluation,reverseZeroEvaluation,zeroEvaluation]
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases hyx : y ≤ x
    · have hx : y < x := lt_of_le_of_ne hyx (Ne.symm hxy)
      simp [hxy,Nat.sub_eq_zero_of_le hyx,show x-y ≠ 0 by omega]
    · simp [hxy,show y-x ≠ 0 by omega]

private theorem equalsOneEvaluation (x : Nat) :
    evaluate GorbowVerifierNormalization.equalsOne (x ::ᵥ nil) = if x = 1 then 1 else 0 := by
  cases x with
  | zero => rfl
  | succ x =>
    change evaluate GorbowPRInternalControl.zeroTest (List.Vector.ofFn fun _ : Fin 1 => x) = _
    rw [vectorOne,zeroTestEvaluation]
    simp

private theorem normalizeEvaluation {n : Nat} (p : Program n) (xs : List.Vector Nat n) :
    evaluate (GorbowVerifierNormalization.normalize p) xs = if evaluate p xs = 1 then 1 else 0 := by
  change evaluate GorbowVerifierNormalization.equalsOne (List.Vector.ofFn fun _ : Fin 1 => evaluate p xs) = _
  rw [vectorOne,equalsOneEvaluation]

theorem branchEvaluation {n : Nat} (p a b : Program n) (xs : List.Vector Nat n) :
    evaluate (chooseBranch p a b) xs = if evaluate p xs = 0 then evaluate a xs else evaluate b xs := by
  rw [chooseBranch,compositeThree,conditionalEvaluation]

theorem bothEvaluation {n : Nat} (p q : Program n) (xs : List.Vector Nat n) :
    evaluate (bothOne p q) xs = if evaluate p xs = 1 ∧ evaluate q xs = 1 then 1 else 0 := by
  rw [bothOne,branchEvaluation,normalizeEvaluation,normalizeEvaluation,zeroEvaluation]
  by_cases hp : evaluate p xs = 1 <;> by_cases hq : evaluate q xs = 1 <;> simp [hp,hq]

theorem exact_DispatchControlEvaluation : ExactDispatchControlEvaluation :=
  ⟨literalEvaluation,predEvaluation,compareEvaluation,fun _ => branchEvaluation,
    fun _ => bothEvaluation⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
