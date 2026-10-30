module
public import LogicLineages.OrdinalComparison.ProfileCompilerTargets
public import LogicLineages.OrdinalComparison.ProfileHeadProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem actualFixedLimitProfileMonotone : Targets.ActualFixedLimitProfileMonotone := by
  intro L E
  induction E with
  | constant n => intro _ x y _; exact le_rfl
  | input => intro _ x y h; exact h
  | add E F ihE ihF =>
    intro hv x y hxy
    exact Nat.add_le_add (ihE hv.1 hxy) (ihF hv.2 hxy)
  | head rho E ih =>
    intro hv
    exact (actualFixedLimitProfileHeads rho hv.1).1.monotone.comp (ih hv.2.2)

theorem actualProfileWordValueAppend (v w : List NONote) (x : Nat) :
    actualProfileWordValue (v ++ w) x = actualProfileWordValue w (actualProfileWordValue v x) := by
  induction v generalizing x with
  | nil => rfl
  | cons rho v ih => exact ih (actualProfileHead rho x)

private theorem omega_profile_valid (L : Ordinal) (hL : Ordinal.omega0 < L) :
    Order.IsSuccLimit profileOmegaNote.1.repr ∧ profileOmegaNote.1.repr < L := by
  rw [actualOmegaProfileHead.1]
  exact ⟨Ordinal.isSuccLimit_omega0, hL⟩

private theorem profile_internal_valid (L : Ordinal) (hL : Ordinal.omega0 < L)
    (E : FixedLimitPositiveExpr) (hv : fixedLimitProfileBelow L E) :
    ∀ rho ∈ profileBoundWordInternal E, Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < L := by
  induction E with
  | constant n => simp [profileBoundWordInternal]
  | input => simp [profileBoundWordInternal]
  | add E F ihE ihF =>
    intro rho hr
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp hr with hr | hr
      · exact ihE hv.1 rho hr
      · exact ihF hv.2 rho hr
    · have hr' := List.mem_singleton.mp hr
      subst rho
      exact omega_profile_valid L hL
  | head rho E ih =>
    intro sigma hs
    rcases List.mem_append.mp hs with hs | hs
    · exact ih hv.2.2 sigma hs
    · have hs' := List.mem_singleton.mp hs
      subst sigma
      exact ⟨hv.1, hv.2.1⟩

private theorem profile_internal_bound (L : Ordinal) (E : FixedLimitPositiveExpr)
    (hv : fixedLimitProfileBelow L E) (x : Nat) (hx : fixedLimitProfileThreshold E ≤ x) :
    x ≤ actualProfileWordValue (profileBoundWordInternal E) x ∧
      actualFixedLimitProfileEval E x ≤ actualProfileWordValue (profileBoundWordInternal E) x := by
  induction E generalizing x with
  | constant n =>
    exact ⟨le_rfl, (Nat.le_max_right 4 n).trans hx⟩
  | input => exact ⟨le_rfl, le_rfl⟩
  | add E F ihE ihF =>
    have hxE : fixedLimitProfileThreshold E ≤ x := (Nat.le_max_left _ _).trans hx
    have hxF : fixedLimitProfileThreshold F ≤ x := (Nat.le_max_right _ _).trans hx
    let u := actualProfileWordValue (profileBoundWordInternal E) x
    let v := actualProfileWordValue (profileBoundWordInternal F) u
    have hE := ihE hv.1 x hxE
    have hF := ihF hv.2 u (hxF.trans hE.1)
    have hFx := actualFixedLimitProfileMonotone L F hv.2 hE.1
    have hdouble := actualOmegaProfileHead.2 v
    simp only [profileBoundWordInternal, actualProfileWordValueAppend, actualProfileWordValue, actualFixedLimitProfileEval]
    change x ≤ actualProfileHead profileOmegaNote v ∧
      actualFixedLimitProfileEval E x + actualFixedLimitProfileEval F x ≤ actualProfileHead profileOmegaNote v
    constructor
    · have hvx : x ≤ v := hE.1.trans hF.1
      omega
    · have hleft : actualFixedLimitProfileEval E x ≤ v := hE.2.trans hF.1
      have hright : actualFixedLimitProfileEval F x ≤ v := hFx.trans hF.2
      omega
  | head rho E ih =>
    have hE := ih hv.2.2 x hx
    have hhead := actualFixedLimitProfileHeads rho hv.1
    simp only [profileBoundWordInternal, actualProfileWordValueAppend, actualProfileWordValue, actualFixedLimitProfileEval]
    exact ⟨hE.1.trans (hhead.2 _).le, hhead.1.monotone hE.2⟩

theorem actualProfileBoundCompiler : Targets.ActualProfileBoundCompiler := by
  intro L hL E hv
  refine ⟨by simp [profileBoundWord], ?_, ?_⟩
  · intro rho hr
    rcases List.mem_append.mp hr with hr | hr
    · exact profile_internal_valid L hL E hv rho hr
    · have hr' := List.mem_singleton.mp hr
      subst rho
      exact omega_profile_valid L hL
  · intro x hx
    have hb := profile_internal_bound L E hv x hx
    have hhead := (actualFixedLimitProfileHeads profileOmegaNote (omega_profile_valid L hL).1).2
      (actualProfileWordValue (profileBoundWordInternal E) x)
    simp only [profileBoundWord, actualProfileWordValueAppend, actualProfileWordValue]
    exact ⟨hb.2.trans_lt hhead, hb.1.trans_lt hhead⟩

end LogicLineages.OrdinalComparison
