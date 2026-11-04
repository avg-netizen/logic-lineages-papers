module
public import LogicLineages.OrdinalComparison.SourceMachinePlanFragmentTargets
public import LogicLineages.OrdinalComparison.SourceGroundBinderFragmentProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
open ExistentialPlan BinaryPlan PrimitiveLowering ParametricScalingPlan SourceGroundBinderFragment

theorem dag_rename {Γ Δ} (r : Renaming Γ Δ) (a : GroundEquivalence.Input Γ .ground)
    (h : Fragment a.term) : Fragment (ScopedDAG.renameInput r a).term := by
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r a).1]
  exact (SourceGroundBinderFragment.Proof.exactRenaming Γ Δ .ground r a.term).mpr h

theorem renamePreservation : Targets.RenamePreservation := by
  intro Γ Δ r q
  induction q generalizing Δ with
  | done => exact fun _ => trivial
  | equation a b q ih =>
    rintro ⟨ha,hb,hq⟩
    exact ⟨dag_rename r a ha,dag_rename r b hb,ih Δ r hq⟩
  | gate g q ih => exact ih Δ r
  | existsGround q ih => exact ih _ (Renaming.lift r)

theorem binary_fragment (d : SourceAdditionCompletion.BinaryDAG) :
    ∀ (Γ : List Ty) (out : Port Γ) (q : Plan Γ),
    PlanFragment q → PlanFragment (binaryPlan d out q) := by
  induction d with
  | zero => intros; assumption
  | one => intros; assumption
  | double d ih =>
    intro Γ out q h
    apply ih
    exact renamePreservation _ _ _ q h
  | doubleOne d ih =>
    intro Γ out q h
    apply ih
    exact renamePreservation _ _ _ q h

theorem scale_fragment (e : Nat) : ∀ (Γ : List Ty) (a out : Port Γ) (q : Plan Γ),
    PlanFragment q → PlanFragment (scalePlan e a out q) := by
  induction e with
  | zero => intros; assumption
  | succ e ih =>
    intro Γ a out q h
    apply ih
    exact renamePreservation _ _ _ q h

theorem constructorPreservation : Targets.ConstructorPreservation := by
  refine ⟨fun Γ d out q => binary_fragment d Γ out q,?_,fun Γ e a out q => scale_fragment e Γ a out q⟩
  intro Γ k q h
  exact binary_fragment (SourceAdditionCompletion.binaryDAG k) _ _ q h
end LogicLineages.OrdinalComparison.Source.SourceMachinePlanFragment.Proof
