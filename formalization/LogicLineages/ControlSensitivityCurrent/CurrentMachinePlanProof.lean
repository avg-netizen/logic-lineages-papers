module
public import LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanShapeProof
public import LogicLineages.ControlSensitivityCurrent.ActualMachineProof
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanProof
public import LogicLineages.OrdinalComparison.SourceMachineConjunctionPlanProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan ParametricExistentialPlan PrimitiveLowering
open CurrentMachinePlanTargets (SuccessorEquations)

theorem gamma_growth (b : Nat) : FullAddition.Targets.SourceGrowth (SourceMachineControlNonperiodicity.gamma b) := by
  have h := ActualMachine.actualMachineGrowth b
  exact ⟨fun n => (h.2.2.2.2.1 n).1,h.2.2.2.2.2.1⟩

theorem graph_policy (b : Nat) (p : AdmissibleSum.Policy) {Γ : List Ty}
    (ρ : Variable Γ .ground → Nat) (x y : Variable Γ .ground) :
    PolicyAddition.Equation p (SourceMachineControlNonperiodicity.gamma b) (inputs ρ)
        (SourceSortCompletion.successorProbe x) (.var y) ↔
      ParametricSourceAddition.Equation (SourceMachineControlNonperiodicity.gamma b) (inputs ρ)
        (SourceSortCompletion.successorProbe x) (.var y) := by
  have hg := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  have hp := PolicyLowering.equation_iff p _ hg.1 hg.2.1 (inputs ρ)
    (.successor (.var x)) (.port (.var y))
  have he := SourceMachineConjunctionPlan.Proof.successor_equation _ hg.1 hg.2.1 (inputs ρ) x y
  change PolicyAddition.Equation p _ (inputs ρ) (SourceSortCompletion.successorProbe x) (.var y) ↔
    SourceMachineControlNonperiodicity.gamma b (ρ x+4) = ρ y at hp
  exact hp.trans ((eq_comm : SourceMachineControlNonperiodicity.gamma b (ρ x+4) = ρ y ↔
    ρ y = SourceMachineControlNonperiodicity.gamma b (ρ x+4)).trans he.symm)

theorem eval_agreement (b : Nat) (p : AdmissibleSum.Policy) {Γ : List Ty} (q : Plan Γ)
    (hq : SuccessorEquations q) (ρ : Variable Γ .ground → Nat) :
    PolicyPlan.Eval p (SourceMachineControlNonperiodicity.gamma b) ρ q ↔
      EvalWith (SourceMachineControlNonperiodicity.gamma b) ρ q := by
  induction q with
  | done => rfl
  | equation a c q ih =>
      obtain ⟨⟨x,y,hx,hy⟩,hn⟩ := hq
      simp only [PolicyPlan.Eval,EvalWith,hx,hy,graph_policy,ih hn ρ]
  | gate g q ih => exact and_congr Iff.rfl (ih hq ρ)
  | existsGround q ih => exact exists_congr (fun n => ih hq (ExistentialPlan.extend ρ n))

theorem pointwise_plan : CurrentMachinePlanTargets.PointwisePlan := by
  intro b e p ρ
  exact (eval_agreement b p _ (original_plan b e) ρ).trans
    (SourceMachineConjunctionPlan.Proof.exactConjunction b e ρ)

theorem compiled_halting : CurrentMachinePlanTargets.CompiledHalting := by
  intro b e p
  let q := SourceMachineConjunctionPlan.plan b e
  let f := SourceMachineControlNonperiodicity.gamma b
  have hnew := PolicyPlan.compilation f (gamma_growth b) p _ q
  have hold := ParametricExistentialPlan.Proof.actualGammaCompilation b _ q
    (SourceMachineConjunctionPlan.Proof.supportedSyntax b e)
  have hbridge : (∃ ν, PolicyPlan.ResultHolds p f (compile q) ν) ↔ ∃ ν, HoldsWith f (compile q) ν := by
    constructor
    · rintro ⟨ν,hν⟩
      let ρ := fun x => ν ((compile q).embedding x)
      have h := (hnew ρ).mpr ⟨ν,fun _ => rfl,hν⟩
      obtain ⟨ν',_,hν'⟩ := (hold ρ).mp ((eval_agreement b p q (original_plan b e) ρ).mp h)
      exact ⟨ν',hν'⟩
    · rintro ⟨ν,hν⟩
      let ρ := fun x => ν ((compile q).embedding x)
      have h := (hold ρ).mpr ⟨ν,fun _ => rfl,hν⟩
      obtain ⟨ν',_,hν'⟩ := (hnew ρ).mp ((eval_agreement b p q (original_plan b e) ρ).mpr h)
      exact ⟨ν',hν'⟩
  exact hbridge.trans (SourceMachineConjunctionPlan.Proof.exactCompiledHalting.2 b e)

end LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan
