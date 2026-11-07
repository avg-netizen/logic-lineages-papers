module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowPRInternalControl GorbowVerifierNormalization
open InternalAcceptance List.Vector

/-- These are only natural-number AST calculations, not proof-tree reflection. -/
theorem evalZeroTest : ∀ x : Nat,
    evaluate zeroTest (x ::ᵥ List.Vector.nil) = if x = 0 then 1 else 0
  | 0 => by
    have hv : (List.Vector.ofFn fun _ : Fin 1 => (0 : Nat)) = 0 ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      rw [List.Vector.get_ofFn]
      obtain rfl := Fin.eq_zero i
      rfl
    change Nat.succ (List.Vector.ofFn fun _ : Fin 1 => (0 : Nat)).head = 1
    rw [hv]
    rfl
  | x + 1 => by simp [zeroTest,zeroStep,evaluate]

theorem evalEqualsOne : ∀ x : Nat,
    evaluate equalsOne (x ::ᵥ List.Vector.nil) = if x = 1 then 1 else 0
  | 0 => rfl
  | x + 1 => by
    have hv : (List.Vector.ofFn fun _ : Fin 1 => x) = x ::ᵥ List.Vector.nil := by
      apply List.Vector.ext
      intro i
      rw [List.Vector.get_ofFn]
      obtain rfl := Fin.eq_zero i
      rfl
    change evaluate zeroTest (List.Vector.ofFn fun _ : Fin 1 => x) = _
    rw [hv,evalZeroTest]
    simp

theorem evalNormalize {n : Nat} (p : Program n) (xs : List.Vector Nat n) :
    evaluate (normalize p) xs = if evaluate p xs = 1 then 1 else 0 := by
  have hv : (List.Vector.ofFn fun _ : Fin 1 => evaluate p xs) =
      evaluate p xs ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    obtain rfl := Fin.eq_zero i
    rfl
  change evaluate equalsOne (List.Vector.ofFn fun _ : Fin 1 => evaluate p xs) = _
  rw [hv,evalEqualsOne]

theorem evalConditional : ∀ x a b : Nat,
    evaluate conditional (x ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) = if x = 0 then a else b
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem evalBranch {n : Nat} (control a b : Program n) (xs : List.Vector Nat n) :
    evaluate (branch control a b) xs =
      if evaluate control xs = 0 then evaluate a xs else evaluate b xs := by
  have hv : (List.Vector.ofFn fun i : Fin 3 =>
      evaluate ((Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0)) : Fin 3 → Program n) i) xs) =
      evaluate control xs ::ᵥ evaluate a xs ::ᵥ evaluate b xs ::ᵥ List.Vector.nil := by
    apply List.Vector.ext
    intro i
    rw [List.Vector.get_ofFn]
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        rfl
  change evaluate conditional (List.Vector.ofFn fun i : Fin 3 =>
    evaluate ((Fin.cons control (Fin.cons a (Fin.cons b Fin.elim0)) : Fin 3 → Program n) i) xs) = _
  rw [hv,evalConditional]

theorem actualConjunctionEvaluation : InternalAcceptanceTargets.ActualConjunctionEvaluation := by
  intro n p q xs
  unfold conjunction
  rw [evalBranch,evalNormalize,evalNormalize]
  change (if (if evaluate p xs = 1 then 1 else 0) = 0 then 0 else
    (if evaluate q xs = 1 then 1 else 0)) = _
  by_cases hp : evaluate p xs = 1 <;> by_cases hq : evaluate q xs = 1 <;> simp [hp,hq]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
