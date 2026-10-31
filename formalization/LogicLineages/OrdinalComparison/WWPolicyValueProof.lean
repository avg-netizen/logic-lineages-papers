module
public import LogicLineages.OrdinalComparison.WWPolicyValueTargets
public import Mathlib.SetTheory.Ordinal.Principal

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem omega_coeff_lt (a e : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 a e < Ordinal.omega0 := by
  by_cases he : e ∈ (Ordinal.CNF Ordinal.omega0 a).map Prod.fst
  · obtain ⟨⟨e, c⟩, hm, rfl⟩ := List.mem_map.mp he
    rw [Ordinal.CNF.coeff_of_mem_CNF hm]
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hm
  · rw [Ordinal.CNF.coeff_of_notMem_CNF he]
    exact Ordinal.omega0_pos

private theorem naturalSum_coeff (a b : Ordinal) :
    Ordinal.CNF.coeff Ordinal.omega0 (ordinalNaturalSum a b) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b := by
  apply Ordinal.CNF.coeff_eval Ordinal.one_lt_omega0
  intro e
  exact Ordinal.isPrincipal_add_omega0 (omega_coeff_lt a e) (omega_coeff_lt b e)

private theorem naturalSum_assoc (a b c : Ordinal) :
    ordinalNaturalSum (ordinalNaturalSum a b) c =
      ordinalNaturalSum a (ordinalNaturalSum b c) := by
  unfold ordinalNaturalSum
  rw [show Ordinal.CNF.coeff Ordinal.omega0
      (Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b)) =
      Ordinal.CNF.coeff Ordinal.omega0 a + Ordinal.CNF.coeff Ordinal.omega0 b from
        naturalSum_coeff a b]
  rw [show Ordinal.CNF.coeff Ordinal.omega0
      (Ordinal.CNF.eval Ordinal.omega0
        (Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 c)) =
      Ordinal.CNF.coeff Ordinal.omega0 b + Ordinal.CNF.coeff Ordinal.omega0 c from
        naturalSum_coeff b c]
  rw [add_assoc]

private theorem free_input_values {Γ : List Ty} {σ : Ty} (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (v : OrdinalPartialVector Γ σ) (hv : policyPartial .left i t = some v) :
    ∃ w, policyPartial .right i t = some w ∧
      ∀ (j : Fin (σ.level + 2)) (ρ : OrdinalComponent Γ → Ordinal),
        denote ρ (v j) = denote ρ (w j) := by
  rw [policyPartial.eq_def, hf] at hv
  have hv' : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  refine ⟨ordinalFreePartialVector i t, ?_, fun _ _ => rfl⟩
  rw [policyPartial.eq_def, hf]
  rfl

theorem actualPolicyFixedInputValue : Targets.ActualPolicyFixedInputValue := by
  intro Γ σ i t
  induction t generalizing i with
  | zero => intro v hv; exact free_input_values i .zero rfl v hv
  | one => intro v hv; exact free_input_values i .one rfl v hv
  | omega => intro v hv; exact free_input_values i .omega rfl v hv
  | var c =>
    intro v hv
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_input_values i (.var c) hf v hv
    · refine ⟨v, ?_, fun _ _ => rfl⟩
      simpa only [policyPartial] using hv
  | add f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_input_values i (.add f g) hf v hv
    · rw [policyPartial, Bool.eq_false_iff.mpr hf] at hv
      have hex : ∃ pf : OrdinalPartialVector Γ σ,
          policyPartial .left i f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
          policyPartial .left i g = some pg ∧
          (fun j => sum3 .left (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
      subst v
      obtain ⟨qf, hqf, eqf⟩ := ihf i pf hpf
      obtain ⟨qg, hqg, eqg⟩ := ihg i pg hpg
      refine ⟨fun j => sum3 .right (qf j) (qg j) .one, ?_, ?_⟩
      · rw [policyPartial, Bool.eq_false_iff.mpr hf, hqf, hqg]
        rfl
      · intro j ρ
        simp only [sum3, denote, eqf j ρ, eqg j ρ]
        exact naturalSum_assoc _ _ _
  | emul f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_input_values i (.emul f g) hf v hv
    · rw [policyPartial, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            policyPartial .left (i + 1) f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            policyPartial .left i g = some pg ∧
            (fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        obtain ⟨qf, hqf, eqf⟩ := ihf (i + 1) pf hpf
        obtain ⟨qg, hqg, eqg⟩ := ihg i pg hpg
        refine ⟨fun j => .add (.add (.add (qf j) (qf j)) (qg j)) .one, ?_, ?_⟩
        · rw [policyPartial, Bool.eq_false_iff.mpr hf, if_pos hi, hqf, hqg]
          rfl
        · intro j ρ
          simp only [denote, eqf j ρ, eqg j ρ]
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_input_values i (.collapse f g) hf v hv
    · rw [policyPartial, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            policyPartial .left 1 f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            policyPartial .left 0 g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
              else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        obtain ⟨qf, hqf, eqf⟩ := ihf 1 pf hpf
        obtain ⟨qg, hqg, eqg⟩ := ihg 0 pg hpg
        refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (qg 0)
          else .add (qf j) (qg j), ?_, ?_⟩
        · rw [policyPartial, Bool.eq_false_iff.mpr hf, if_pos hi, hqf, hqg]
          rfl
        · intro j ρ
          by_cases hj : j.val = 0
          · simp only [if_pos hj, denote, eqg 0 ρ]
          · simp only [if_neg hj, denote, eqf j ρ, eqg j ρ]
      · simp [hi] at hv

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
