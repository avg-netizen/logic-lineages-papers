module
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanTargets
public import LogicLineages.OrdinalComparison.ParametricPrimitiveLoweringProof
public import LogicLineages.OrdinalComparison.SourceExistentialPlanSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Proof
open ExistentialPlan GroundEquivalence PrimitiveLowering ParametricSourceSuccessor

theorem denote_rename (G : Nat → Nat) {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x,ν (r x)=ρ x) (t : OrdinalExpression Γ) :
    denoteWith G (fun c => ((inputs ν c+1 : Nat) : Ordinal)) (ordinalExpressionRename r t) =
      denoteWith G (fun c => ((inputs ρ c+1 : Nat) : Ordinal)) t := by
  rw [ordinalExpressionRename,ParametricSourceSuccessor.Proof.exactSubstitution]
  congr 1
  funext c
  rcases c with ⟨σ,x,j⟩
  cases σ with
  | ground => exact congrArg (fun n : Nat => ((n+1 : Nat) : Ordinal)) (h x)
  | arrow a b => rfl

theorem equation_of_assignments (G : Nat → Nat) {Γ} (ρ : OrdinalComponent Γ → Nat)
    (a b : OriginalTerm Γ .ground) (va vb : OrdinalVector Γ 0)
    (ha : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a=some va)
    (hb : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy b=some vb) :
    ParametricSourceAddition.Equation G ρ a b ↔
      denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (va 0)=
        denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal)) (vb 0) := by
  constructor
  · rintro ⟨wa,wb,hwa,hwb,he⟩
    cases Option.some.inj (ha.symm.trans hwa)
    cases Option.some.inj (hb.symm.trans hwb)
    exact he
  · intro he
    exact ⟨va,vb,ha,hb,he⟩

theorem exactEquationRenaming : Targets.ExactEquationRenaming := by
  intro G Γ Δ r ρ ν h a b
  obtain ⟨va,ha,_⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ a
  obtain ⟨vb,hb,_⟩ := SourceCollisionCompletion.Proof.actualScalarTotal Γ b
  have hra : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (a.rename r)=
      some (SourceRenaming.renameVector r va) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ .ground r OrdinalSyntax.defaultPolicy a,ha]
    rfl
  have hrb : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (b.rename r)=
      some (SourceRenaming.renameVector r vb) := by
    rw [SourceRenaming.Proof.assignmentNaturality Γ Δ .ground r OrdinalSyntax.defaultPolicy b,hb]
    rfl
  rw [equation_of_assignments G (inputs ν) _ _ _ _ hra hrb,
    equation_of_assignments G (inputs ρ) _ _ _ _ ha hb]
  change (denoteWith G _ (ordinalExpressionRename r (va 0)) =
    denoteWith G _ (ordinalExpressionRename r (vb 0))) ↔ _
  rw [denote_rename G r ρ ν h,denote_rename G r ρ ν h]

theorem equation_dag_rename (G : Nat → Nat) {Γ Δ} (r : Renaming Γ Δ)
    (ρ : Variable Γ .ground → Nat) (ν : Variable Δ .ground → Nat)
    (h : ∀ x,ν (r x)=ρ x) (a b : Input Γ .ground) :
    ParametricSourceAddition.Equation G (inputs ν) (ScopedDAG.renameInput r a).term (ScopedDAG.renameInput r b).term ↔
      ParametricSourceAddition.Equation G (inputs ρ) a.term b.term := by
  rw [(ScopedDAG.Proof.«renaming» Γ Δ .ground r a).1,(ScopedDAG.Proof.«renaming» Γ Δ .ground r b).1]
  exact exactEquationRenaming G Γ Δ r ρ ν h a.term b.term

theorem supported_rename {Γ Δ} (r : Renaming Γ Δ) (g : Gate Γ)
    (h : ParametricPrimitiveLowering.Supported g) :
    ParametricPrimitiveLowering.Supported (gateRename r g) := by
  cases g <;> exact h
end LogicLineages.OrdinalComparison.Source.ParametricExistentialPlan.Proof
