module
public import LogicLineages.ControlSensitivityCurrent.CurrentMachinePlanTargets
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
public import LogicLineages.OrdinalComparison.ParametricScalingPlanDefinitions
public import LogicLineages.OrdinalComparison.SourcePrimitiveLoweringGraphProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan

open LogicLineages.OrdinalComparison.Source
open ExistentialPlan BinaryPlan PrimitiveLowering GroundEquivalence
open CurrentMachinePlanTargets (SuccessorEquations)

theorem successor_rename {Γ Δ : List Ty} (r : Renaming Γ Δ) (x : Variable Γ .ground) :
    (successorProbe x).rename r = successorProbe (r x) :=
  rfl

theorem rename_shape {Γ : List Ty} (q : Plan Γ) (hq : SuccessorEquations q)
    {Δ : List Ty} (r : Renaming Γ Δ) :
    SuccessorEquations (renamePlan r q) := by
  induction q generalizing Δ with
  | done => trivial
  | equation a b q ih =>
      obtain ⟨⟨x,y,hx,hy⟩,hq'⟩ := hq
      refine ⟨⟨r x,r y,?_,?_⟩, ih hq' r⟩
      · rw [(ScopedDAG.Proof.«renaming» _ _ _ r a).1, hx, successor_rename]
      · rw [(ScopedDAG.Proof.«renaming» _ _ _ r b).1, hy]
        rfl
  | gate g q ih => exact ih hq r
  | existsGround q ih => exact ih hq (Renaming.lift r)

theorem binary_shape {Γ : List Ty} (d : SourceAdditionCompletion.BinaryDAG)
    (out : Port Γ) (q : Plan Γ) (hq : SuccessorEquations q) :
    SuccessorEquations (binaryPlan d out q) := by
  induction d generalizing Γ with
  | zero => exact hq
  | one => exact hq
  | double d ih =>
      exact ih _ _ (rename_shape q hq (Renaming.weaken Γ .ground))
  | doubleOne d ih =>
      exact ih _ _ (rename_shape q hq (shift 3))

theorem scale_shape {Γ : List Ty} (e : Nat) (a out : Port Γ) (q : Plan Γ)
    (hq : SuccessorEquations q) : SuccessorEquations (ParametricScalingPlan.scalePlan e a out q) := by
  induction e generalizing Γ with
  | zero => exact hq
  | succ e ih => exact ih _ _ _ (rename_shape q hq (Renaming.weaken Γ .ground))

private theorem constant_shape {Γ : List Ty} (k : Nat) (q : Plan (.ground :: Γ))
    (hq : SuccessorEquations q) : SuccessorEquations (constantPlan k q) :=
  binary_shape _ _ q hq

theorem original_plan : CurrentMachinePlanTargets.OriginalPlan := by
  intro b e
  unfold SourceMachineConjunctionPlan.plan
  apply constant_shape
  apply constant_shape
  apply constant_shape
  simp only [SuccessorEquations, SourceMachineConjunctionPlan.tail]
  apply scale_shape
  simp only [SuccessorEquations, and_true]
  exact ⟨SourceMachineConjunctionPlan.wire 10,SourceMachineConjunctionPlan.wire 11,rfl,rfl⟩

end LogicLineages.ControlSensitivityCurrent.CurrentMachinePlan
