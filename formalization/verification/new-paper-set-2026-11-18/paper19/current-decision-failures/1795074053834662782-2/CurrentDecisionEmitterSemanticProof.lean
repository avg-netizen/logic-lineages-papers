module
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitterDefinitions
public import LogicLineages.ControlSensitivityCurrent.SourceASTObservationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence ExistentialPlan PrimitiveLowering
open InputNormalization (sourceValue)
open CurrentAttainment (repeatAdd)

private theorem repeat_eval (p : AdmissibleSum.Policy) (f : Nat → Nat) (n : Nat) {Γ}
    (x a : Variable Γ .ground)
    (k : ∀ {Δ}, Renaming Γ Δ → Variable Δ .ground → InputNormalization.Input Δ 0)
    (ρ : Variable Γ .ground → Nat) (P : Prop)
    (hk : ∀ (Δ : List Ty) (r : Renaming Γ Δ) (z : Variable Δ .ground)
      (ν : Variable Δ .ground → Nat), (∀ y, ν (r y) = ρ y) →
      ν z = ρ a + n * ρ x → ((k r z).eval p f ν Fin.elim0 ↔ P)) :
    (repeatAdd x a n k).eval p f ρ Fin.elim0 ↔ P := by
  induction n generalizing Γ with
  | zero =>
    exact hk Γ (fun x => x) a ρ (fun _ => rfl) (by simp)
  | succ n ih =>
    change (repeatAdd (.there x) .here n (fun r z => k (fun y => r (.there y)) z)).eval p f
      (extend ρ (ρ a + ρ x)) Fin.elim0 ↔ P
    apply ih
    intro Δ r z ν hr hz
    apply hk Δ (fun y => r (.there y)) z ν (fun y => hr (.there y))
    change ν z = ρ a + ρ x + n * ρ x at hz
    rw [hz, Nat.succ_mul]
    omega

theorem observe_iff (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (a b : Input Γ .ground) (x y v : Variable Γ .ground) (factor anchor : Nat)
    (k : ∀ {Δ}, Renaming Γ Δ → Ports Δ → InputNormalization.Input Δ 0)
    (ρ : Variable Γ .ground → Nat) (P : Prop)
    (hk : ∀ (Δ : List Ty) (r : Renaming Γ Δ) (z : Ports Δ)
      (ν : Variable Δ .ground → Nat), (∀ y, ν (r y) = ρ y) →
      ν z.1 = sourceValue p f ρ a →
      ν z.2.1 = sourceValue p f ρ b →
      ν z.2.2.1 = ρ x + factor * ρ v →
      ν z.2.2.2 = factor * anchor + ρ y →
      ((k r z).eval p f ν Fin.elim0 ↔ P)) :
    (observe a b x y v factor anchor k).eval p f ρ Fin.elim0 ↔ P := by
  unfold observe
  simp only [InputNormalization.Input.eval]
  have hb := SourceAST.sourceValue_rename p f (Renaming.weaken Γ .ground) ρ
    (extend ρ (sourceValue p f ρ a)) (fun _ => rfl) b
  rw [hb]
  apply repeat_eval
  intro Δ r sum ν hkeep hsum
  simp only [InputNormalization.Input.eval]
  let ν' := extend ν (factor*anchor)
  let ν'' := extend ν' (factor*anchor + ν (r (.there (.there (.there y)))))
  let r' : Renaming Γ (.ground :: .ground :: Δ) :=
    fun z => .there (.there (r (.there (.there (.there z)))))
  let out : Ports (.ground :: .ground :: Δ) :=
    (.there (.there (r (.there (.there .here)))),
     .there (.there (r (.there .here))),
     .there (.there sum), .here)
  change (k r' out).eval p f ν'' Fin.elim0 ↔ P
  apply hk _ r' out ν''
  · intro i
    exact hkeep (.there (.there (.there i)))
  · exact hkeep (.there (.there .here))
  · exact hkeep (.there .here)
  · change ν sum = ρ x + factor * ρ v
    exact hsum
  · change factor*anchor + ν (r (.there (.there (.there y)))) = factor*anchor + ρ y
    rw [hkeep]
    rfl

theorem final_iff (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (strict : Bool) (a b : Ports Γ) (v w : Variable Γ .ground)
    (ρ : Variable Γ .ground → Nat) :
    (finalRows strict a b v w).eval p f ρ Fin.elim0 ↔
      (ρ a.1 = ρ a.2.1 ∧ ρ a.2.2.1 = ρ a.2.2.2) ∧
      (ρ b.1 = ρ b.2.1 ∧ ρ b.2.2.1 = ρ b.2.2.2) ∧
      (if strict then ρ w ≤ ρ v else ρ w < ρ v) := by
  cases strict
  · change (((decide (ρ b.2.2.1 = ρ b.2.2.2) && decide (ρ b.1 = ρ b.2.1)) &&
      (decide (ρ a.2.2.1 = ρ a.2.2.2) && decide (ρ a.1 = ρ a.2.1))) &&
      decide (ρ w < ρ v)) = true ↔ _
    simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq]
    tauto
  · change (((decide (ρ b.2.2.1 = ρ b.2.2.2) && decide (ρ b.1 = ρ b.2.1)) &&
      (decide (ρ a.2.2.1 = ρ a.2.2.2) && decide (ρ a.1 = ρ a.2.1))) &&
      decide (ρ w ≤ ρ v)) = true ↔ _
    simp only [if_true, Bool.and_eq_true, decide_eq_true_eq]
    tauto

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionEmitter
