module
public import LogicLineages.OrdinalComparison.ParametricPrimitiveFiniteTargets
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof
open ParametricSourceEraser ParametricSourceSuccessor

theorem denote_rename_full (G : Nat → Nat) {Γ Δ} (r : Renaming Γ Δ)
    (ρ : OrdinalComponent Γ → Nat) (ν : OrdinalComponent Δ → Nat)
    (h : ∀ c,ν (ordinalComponentRename r c)=ρ c) (t : OrdinalExpression Γ) :
    denoteWith G (positive ν) (ordinalExpressionRename r t)=denoteWith G (positive ρ) t := by
  rw [ordinalExpressionRename,ParametricSourceSuccessor.Proof.exactSubstitution]
  congr 1
  funext c
  exact congrArg (fun n : Nat => ((n+1 : Nat) : Ordinal)) (h c)

theorem fullComponentRenaming : Targets.FullComponentRenaming := by
  intro G Γ Δ r ρ ν h t n
  obtain ⟨v,hv,_⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ t
  have hr : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (t.rename r)=
      some (SourceRenaming.renameVector r v) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ .ground r OrdinalSyntax.defaultPolicy t,hv]
    rfl
  have hd := denote_rename_full G r ρ ν h (v 0)
  constructor
  · rintro ⟨w,hw,he⟩
    cases Option.some.inj (hr.symm.trans hw)
    exact ⟨v,hv,hd.symm.trans he⟩
  · rintro ⟨w,hw,he⟩
    cases Option.some.inj (hv.symm.trans hw)
    exact ⟨_,hr,hd.trans he⟩

theorem groundInputDAGRenaming : Targets.GroundInputDAGRenaming := by
  intro G Γ Δ r ρ ν h t n
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r t).1]
  apply fullComponentRenaming G Γ Δ r (ExistentialPlan.inputs ρ) (ExistentialPlan.inputs ν)
  intro c
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground => exact h x
  | arrow a b => rfl
end LogicLineages.OrdinalComparison.Source.ParametricPrimitiveFinite.Proof
