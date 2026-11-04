module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFiniteTargets
public import LogicLineages.OrdinalComparison.ParametricPlanFiniteProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Proof
open ExistentialPlan BinaryPlan PrimitiveLowering ParametricPlanFinite ParametricScalingPlan

theorem forwardRenaming : Targets.ForwardRenaming := by
  intro G Γ Δ r q
  induction q generalizing Δ with
  | done => exact fun _ => trivial
  | @equation Γ a b q ih =>
    rintro ⟨hl,hq⟩
    refine ⟨?_,ih Δ r hq⟩
    intro ν
    let ρ : Variable Γ .ground → Nat := fun x => ν (r x)
    obtain ⟨x,y,hx,hy⟩ := hl ρ
    exact ⟨x,y,
      (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G Γ Δ r ρ ν (fun _ => rfl) a x).mpr hx,
      (ParametricPrimitiveFinite.Proof.groundInputDAGRenaming G Γ Δ r ρ ν (fun _ => rfl) b y).mpr hy⟩
  | gate g q ih => exact ih Δ r
  | existsGround q ih => exact ih (.ground::Δ) (Renaming.lift r)

theorem binary_finite (G : Nat → Nat) (d : SourceAdditionCompletion.BinaryDAG) :
    ∀ (Γ : List Ty) (out : Port Γ) (q : Plan Γ),
    UniformFinite G q → UniformFinite G (binaryPlan d out q) := by
  induction d with
  | zero => intros; assumption
  | one => intros; assumption
  | double d ih =>
    intro Γ out q h
    apply ih
    exact forwardRenaming G _ _ _ q h
  | doubleOne d ih =>
    intro Γ out q h
    apply ih
    exact forwardRenaming G _ _ _ q h

theorem scale_finite (G : Nat → Nat) (e : Nat) :
    ∀ (Γ : List Ty) (a out : Port Γ) (q : Plan Γ),
    UniformFinite G q → UniformFinite G (scalePlan e a out q) := by
  induction e with
  | zero => intros; assumption
  | succ e ih =>
    intro Γ a out q h
    apply ih
    exact forwardRenaming G _ _ _ q h

theorem constructorPreservation : Targets.ConstructorPreservation := by
  refine ⟨fun G Γ d out q => binary_finite G d Γ out q,?_,fun G Γ e a out q => scale_finite G e Γ a out q⟩
  intro G Γ k q h
  exact binary_finite G (SourceAdditionCompletion.binaryDAG k) _ _ q h
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFinite.Proof
