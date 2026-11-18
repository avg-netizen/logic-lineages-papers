module
public import LogicLineages.PermittedControl.SelectedBoundedDeltaTargets
public import LogicLineages.PermittedControl.SelectedGradedPositivityProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedNormSumsProof
open OrdinalComparison Source SelectedSourceDomain Source.AdmissibleSum Source.AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

 theorem scalar_finite (ctrl : Nat → Nat) (Γ : List Ty) (t : OrdinalExpression Γ)
    (ht : AmbientGrade ctrl Γ 0 t) (ρ : AdmissibleSubstitution ctrl Γ) :
    ∃ n : Nat, expressionValue ctrl ρ t = (n : Ordinal.{0}) :=
  SourceScalarCalibrationProof.ambient_scalar_finite ctrl ht ρ rfl

 theorem finite_calibration (n : Nat) : finiteValue (n : Ordinal.{0}) = n :=
  (SourceScalarCalibrationProof.natural_calibration n).1

 theorem scalar_positive (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (Γ : List Ty) (t : OrdinalExpression Γ) (ht : AmbientGrade ctrl Γ 0 t)
    (ρ : AdmissibleSubstitution ctrl Γ) : 0 < finiteValue (expressionValue ctrl ρ t) := by
  obtain ⟨n,hn,hv,hc,hN⟩ := (SelectedGradedPositivityProof.positiveScalars ctrl K hc).2 Γ t ht ρ
  rw [hc]
  exact hn

private theorem castAdd_eq_castLE {n m : Nat} (i : Fin n) :
    Fin.castAdd m i = Fin.castLE (Nat.le_add_right n m) i := Fin.ext rfl

 theorem shapeNorm (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (n : Nat) (s : Shape n) (xs : Fin n → OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ctrl ρ (expand s xs)) =
      ((List.ofFn xs).map (fun t => actualOrdinalNorm (expressionValue ctrl ρ t))).sum := by
  induction s with
  | leaf => simp [expand,List.ofFn_succ,List.ofFn_zero]
  | @join n m a b iha ihb =>
    change actualOrdinalNorm (ordinalNaturalSum
      (expressionValue ctrl ρ (expand a (fun i => xs (Fin.castAdd m i))))
      (expressionValue ctrl ρ (expand b (fun i => xs (Fin.natAdd n i))))) = _
    rw [Source.OriginalDomain.actualNaturalSumNormAdditivity _ _
      (SelectedValueClosureProof.ambient_below ctrl ρ _)
      (SelectedValueClosureProof.ambient_below ctrl ρ _)]
    rw [iha,ihb,List.ofFn_add,List.map_append,List.sum_append]
    simp only [castAdd_eq_castLE]

 theorem repeatNorm (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (p : Policy) (site : MacroSite) (k : Nat) (t : OrdinalExpression Γ) (hk : 0 < k) :
    actualOrdinalNorm (expressionValue ctrl ρ (repeated p site k t)) =
      k * actualOrdinalNorm (expressionValue ctrl ρ t) := by
  cases k with
  | zero => omega
  | succ k =>
    change actualOrdinalNorm (expressionValue ctrl ρ (expand (p.shape site k) (fun _ => t))) = _
    rw [shapeNorm]
    simp [List.ofFn_const,List.sum_replicate,Nat.add_mul,Nat.add_comm]

 theorem scalarNorm (ctrl : Nat → Nat) (Γ : List Ty) (ρ : AdmissibleSubstitution ctrl Γ)
    (t : OrdinalExpression Γ) (ht : AmbientGrade ctrl Γ 0 t) :
    actualOrdinalNorm (expressionValue ctrl ρ t) = finiteValue (expressionValue ctrl ρ t) := by
  obtain ⟨n,hn⟩ := scalar_finite ctrl Γ t ht ρ
  rw [hn,finite_calibration]
  exact (finiteNorm n).2

end LogicLineages.PermittedControl.SelectedNormSumsProof
