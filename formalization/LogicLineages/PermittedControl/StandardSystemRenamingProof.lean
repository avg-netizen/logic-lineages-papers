module
public import LogicLineages.PermittedControl.StandardSystemMaskTargets
public import LogicLineages.PermittedControl.StandardAggregationWeakProof
public import LogicLineages.PermittedControl.StandardPairCompilerProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardSystemMask.Proof
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector
open Source.AdmissibleSum
open SelectedHardness (value1)
open StandardFunctionalDetector.Proof
open SelectedSystemReduction
open StandardCombinatorCoordinates.Proof (padVector pad_assignment pad_head pad_scalar)
open Source.FunctionalDetector (unary shiftTwo pad alignedLeft alignedRight)

 theorem expression_preserves {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ)
    (h : Preserves ctrl r ρ σ) (t : OrdinalExpression Γ) :
    expressionValue ctrl σ (ordinalExpressionRename r t)=expressionValue ctrl ρ t := by
  rw [expressionValue,ordinalExpressionRename,ParametricSourceSuccessor.Proof.exactSubstitution]
  apply congrArg (fun ν => ParametricSourceSuccessor.denoteWith ctrl ν t)
  funext c
  rcases c with ⟨τ,x,j⟩
  exact congrArg (closedValue ctrl) (h τ x j)

 theorem ground_preserves {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ)
    (h : Preserves ctrl r ρ σ) (policy : Policy) (t : OriginalTerm Γ .ground) :
    groundValue ctrl policy σ (t.rename r)=groundValue ctrl policy ρ t := by
  unfold groundValue
  rw [SourceRenaming.Proof.assignmentNaturality]
  cases ht : AdmissibleAssignment.assignment policy t with
  | none => rfl
  | some v =>
    change finiteValue (expressionValue ctrl σ (ordinalExpressionRename r (v 0)))=
      finiteValue (expressionValue ctrl ρ (v 0))
    rw [expression_preserves ctrl r ρ σ h]

 theorem head_preserves {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ)
    (h : Preserves ctrl r ρ σ) (policy : Policy) (t : OriginalTerm Γ unary) :
    value1 ctrl policy σ (t.rename r)=value1 ctrl policy ρ t := by
  unfold value1
  rw [SourceRenaming.Proof.assignmentNaturality]
  cases ht : AdmissibleAssignment.assignment policy t with
  | none => rfl
  | some v => exact expression_preserves ctrl r ρ σ h (v 1)

 theorem allEqual_preserves {Γ Δ : List Ty} (ctrl : Nat → Nat) (r : Renaming Γ Δ)
    (ρ : AdmissibleSubstitution ctrl Γ) (σ : AdmissibleSubstitution ctrl Δ)
    (h : Preserves ctrl r ρ σ) (policy : Policy)
    (ps : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)) :
    SelectedAggregation.AllEqual ctrl policy σ
      (ps.map fun p => (p.1.rename r,p.2.rename r)) ↔ SelectedAggregation.AllEqual ctrl policy ρ ps := by
  constructor
  · intro hp p hm
    have he := hp (p.1.rename r,p.2.rename r) (List.mem_map.mpr ⟨p,hm,rfl⟩)
    simpa only [ground_preserves ctrl r ρ σ h] using he
  · intro hp p hm
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
    change groundValue _ _ _ (q.1.rename r)=groundValue _ _ _ (q.2.rename r)
    rw [ground_preserves ctrl r ρ σ h,ground_preserves ctrl r ρ σ h]
    exact hp q hq

 theorem actualRenaming : StandardSystemMask.ActualRenaming := by
  intro Γ Δ r ρ σ h
  exact ⟨expression_preserves Phi r ρ σ h,ground_preserves Phi r ρ σ h⟩
end LogicLineages.PermittedControl.StandardSystemMask.Proof
