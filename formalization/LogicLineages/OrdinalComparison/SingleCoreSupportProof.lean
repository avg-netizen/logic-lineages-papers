module
public import LogicLineages.OrdinalComparison.SingleCoreSupportProgramProof
public import LogicLineages.OrdinalComparison.OneVariableComparisonDomainsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SingleCoreSupport

theorem bounds : Targets.ActualSingleCoreSupportBounds := by
  intro d E hv
  induction E with
  | constant c => intro i hi; cases hi
  | input j =>
    intro i hi
    have heq : i=j := List.mem_singleton.mp hi
    subst i
    exact ⟨hv,by change j≤4*j+1; omega⟩
  | add E F ihE ihF =>
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have hh := ihE hv.1 i hi
      refine ⟨hh.1,hh.2.trans ?_⟩
      change multivariatePositiveEncode E≤4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2
      have hp := Nat.left_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
      omega
    · have hh := ihF hv.2 i hi
      refine ⟨hh.1,hh.2.trans ?_⟩
      change multivariatePositiveEncode F≤4*Nat.pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)+2
      have hp := Nat.right_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
      omega
  | head rho E ih =>
    intro i hi
    have hh := ih hv.2.2 i hi
    refine ⟨hh.1,hh.2.trans ?_⟩
    change multivariatePositiveEncode E≤4*Nat.pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)+3
    have hp := Nat.right_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
    omega

theorem agreement : Targets.ActualSingleCoreSupportAgreement := by
  intro E ρ σ h
  induction E with
  | constant c => rfl
  | input i => exact h i List.mem_cons_self
  | add E F ihE ihF =>
    exact congrArg₂ (·+·) (ihE (fun i hi => h i (List.mem_append_left _ hi)))
      (ihF (fun i hi => h i (List.mem_append_right _ hi)))
  | head rho E ih => exact congrArg (actualProfileHead rho) (ih h)

theorem dominance : Targets.ActualSingleCoreSupportDominance := by
  intro d E hv ρ i hi
  induction E with
  | constant c => cases hi
  | input j =>
    have heq : i=j := List.mem_singleton.mp hi
    subst i
    exact le_rfl
  | add E F ihE ihF =>
    rcases List.mem_append.mp hi with hi | hi
    · exact (ihE hv.1 hi).trans (Nat.le_add_right _ _)
    · exact (ihF hv.2 hi).trans (Nat.le_add_left _ _)
  | head rho E ih =>
    exact (ih hv.2.2 hi).trans ((actualFixedLimitProfileHeads rho hv.1).2 _).le

theorem full : Targets.FullActualSingleCoreSupport := ⟨program,bounds,agreement,dominance⟩

end LogicLineages.OrdinalComparison.SingleCoreSupport
