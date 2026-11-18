module
public import LogicLineages.ControlSensitivityCurrent.PolicyPlanTargets
public import LogicLineages.ControlSensitivityCurrent.PolicyLoweringProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyPlan
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan GroundEquivalence PrimitiveLowering

theorem equationNaturality : PolicyPlanTargets.EquationNaturality := by
  intro p f Γ Δ r ρ ν h a b
  have hc : ∀ (τ : Ty) (x : Variable Γ τ) (j : Fin (τ.level+1)),
      inputs ν ⟨τ,r x,j⟩ = inputs ρ ⟨τ,x,j⟩ := by
    intro τ x j
    cases τ with
    | ground => exact h x
    | arrow a b => rfl
  rw [PolicyObservation.equationCalibration,PolicyObservation.equationCalibration,
    PolicyObservation.sourceNaturality p f Γ Δ r (inputs ρ) (inputs ν) hc a,
    PolicyObservation.sourceNaturality p f Γ Δ r (inputs ρ) (inputs ν) hc b]
theorem equation_dag_rename (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ Δ} (r : Renaming Γ Δ) (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (a b : Input Γ .ground) :
    PolicyAddition.Equation p f (inputs ν) (ScopedDAG.renameInput r a).term (ScopedDAG.renameInput r b).term ↔
      PolicyAddition.Equation p f (inputs ρ) a.term b.term := by
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r a).1,(ScopedDAG.Proof.«renaming» Γ Δ .ground r b).1]
  exact equationNaturality p f Γ Δ r ρ ν h a.term b.term
theorem port_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (a : Port Γ) :
    (portRename r a).value (inputs ν)=a.value (inputs ρ) := by
  cases a with
  | zero => rfl
  | var x => exact h x

theorem gate_rename {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x, ν (r x)=ρ x) (g : Gate Γ) :
    (gateRename r g).Holds (inputs ν) ↔ g.Holds (inputs ρ) := by
  cases g <;> simp only [gateRename,Gate.Holds,port_rename r ρ ν h]

def block {Γ} (ρ : Variable Γ .ground → Nat) :
    (n : Nat) → (Fin n → Nat) → Variable (List.replicate n Ty.ground++Γ) .ground → Nat
  | 0, _ => ρ
  | n+1, z => ExistentialPlan.extend (block ρ n (fun i => z i.succ)) (z 0)

theorem inputs_block {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat) :
    inputs (block ρ n z)=PrimitiveLowering.extend (inputs ρ) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext c
    rcases c with ⟨σ,x,j⟩
    cases x with
    | here => rfl
    | there x =>
      have hh := congrFun (ih (fun i => z i.succ)) ⟨σ,x,j⟩
      cases σ <;> exact hh

theorem block_shift {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat)
    (x : Variable Γ .ground) : block ρ n z (shift n x)=ρ x := by
  have hh := PrimitiveLowering.Proof.extend_shift (inputs ρ) n z x 0
  rw [← inputs_block] at hh
  exact hh

theorem block_fresh {Γ} (ρ : Variable Γ .ground → Nat) (n : Nat) (z : Fin n → Nat)
    (i : Fin n) : block ρ n z (fresh i)=z i := by
  have hh := PrimitiveLowering.Proof.extend_fresh (inputs ρ) n z i
  rw [← inputs_block] at hh
  exact hh

theorem block_decompose {Γ} (n : Nat) (ν : Variable (List.replicate n Ty.ground++Γ) .ground → Nat) :
    block (fun x => ν (shift n x)) n (fun i => ν (fresh i))=ν := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext x
    cases x with
    | here => rfl
    | there x => exact congrFun (ih (fun x => ν (.there x))) x

end LogicLineages.ControlSensitivityCurrent.PolicyPlan
