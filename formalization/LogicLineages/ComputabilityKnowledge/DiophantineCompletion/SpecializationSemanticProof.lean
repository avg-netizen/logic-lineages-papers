module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationTargets
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationSemanticProof
open PolynomialCircuit PolynomialDomainShift DiophantinePolynomialBridge Specialization SpecializationTargets

private theorem factorIdentity (vs : List Nat) (x : Nat) (ρ : Nat → Int) :
    (x : Int) ^ vs.count 0 * MvPolynomial.eval ρ (variableProduct (dropParameter vs)) =
      MvPolynomial.eval (fun i => Nat.casesOn i (x : Int) ρ) (variableProduct vs) := by
  induction vs with
  | nil => simp [dropParameter,variableProduct]
  | cons i vs ih =>
      cases i with
      | zero =>
          simpa [dropParameter,variableProduct,pow_succ,mul_assoc,mul_comm,mul_left_comm] using
            congrArg (fun t : Int => (x : Int) * t) ih
      | succ i =>
          simpa [dropParameter,variableProduct,mul_assoc,mul_comm,mul_left_comm] using
            congrArg (fun t : Int => ρ i * t) ih

private theorem termsIdentity (ms : Monomials) (x : Nat) (ρ : Nat → Int) :
    MvPolynomial.eval ρ (interpretTerms (ms.map (term x))) =
      MvPolynomial.eval (fun i => Nat.casesOn i (x : Int) ρ) (interpretTerms ms) := by
  induction ms with
  | nil => simp [interpretTerms]
  | cons m ms ih =>
      rcases m with ⟨z,vs⟩
      simp only [List.map_cons,term,interpretTerms,map_add,map_mul,MvPolynomial.eval_C,ih]
      rw [← factorIdentity vs x ρ]
      ring

theorem substitutionIdentity : SubstitutionIdentity := by
  intro p x ρ
  exact termsIdentity p.monomials x ρ

private theorem droppedMem (vs : List Nat) (i : Nat) :
    i ∈ dropParameter vs → i + 1 ∈ vs := by
  induction vs with
  | nil => simp [dropParameter]
  | cons a vs ih =>
      cases a with
      | zero =>
          intro h
          exact List.mem_cons_of_mem 0 (ih h)
      | succ a =>
          intro h
          change i ∈ a :: dropParameter vs at h
          rcases List.mem_cons.mp h with h | h
          · subst i
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih h)

theorem substitutionWellFormed : SubstitutionWellFormed := by
  intro p x hp m hm i hi
  obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hm
  have hvar := hp old hold (i + 1) (droppedMem old.2 i hi)
  change i < p.inputCount - 1
  omega

theorem substitutionRootCorrespondence : SubstitutionRootCorrespondence := by
  intro p m x hp
  change (∃ w : Fin (p.inputCount - 1) → Nat, MvPolynomial.eval
    (fun i => (finiteNat w i : Int)) (interpret (specialize x p)) = 0) ↔ _
  rw [hp]
  apply exists_congr
  intro w
  rw [substitutionIdentity]
  have hρ : (fun i => Nat.casesOn i (x : Int) (fun j => (finiteNat w j : Int))) =
      (fun i => (joinedNat (fun _ : Fin 1 => x) w i : Int)) := by
    funext i
    cases i with
    | zero => simp [joinedNat]
    | succ i => simp [joinedNat,finiteNat]
  rw [hρ]
  rfl

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.SpecializationSemanticProof
