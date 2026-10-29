module

public import LogicLineages.Ultrafilters.DomainDerivationTargets
public import LogicLineages.Ultrafilters.DomainSubfield
public import LogicLineages.Ultrafilters.DerivativeWellDefined

@[expose] public section
namespace LogicLineages.Ultrafilters

theorem domain_derivation : Targets.DomainDerivation := by
  classical
  intro p hp
  obtain ⟨K, hK, hc⟩ := domain_subfield p hp
  have reps (a : K) : ∃ f : ℝ → ℝ,
      classOf p f = (a : RealUltrapower p) ∧ {x | DifferentiableAt ℝ f x} ∈ p := by
    have ha := a.property
    change (a : RealUltrapower p) ∈ (K : Set (RealUltrapower p)) at ha
    rw [hK] at ha
    exact ha
  choose rep hrep using reps
  let d : K → RealUltrapower p := fun a => classOf p (deriv (rep a))
  have spec (a : K) (f : ℝ → ℝ) (he : classOf p f = (a : RealUltrapower p))
      (hf : {x | DifferentiableAt ℝ f x} ∈ p) : d a = classOf p (deriv f) := by
    exact derivative_well_defined p hp (rep a) f ((hrep a).1.trans he.symm)
      (hrep a).2 hf
  have hadd (a b : K) : d (a + b) = d a + d b := by
    have hf : {x | DifferentiableAt ℝ (fun y => rep a y + rep b y) x} ∈ p := by
      apply Filter.mem_of_superset (Filter.inter_mem (hrep a).2 (hrep b).2)
      intro x hx
      exact hx.1.add hx.2
    rw [spec (a + b) (fun x => rep a x + rep b x)
      (by change classOf p (rep a) + classOf p (rep b) = _; rw [(hrep a).1, (hrep b).1]; rfl) hf]
    apply Filter.Germ.coe_eq.mpr
    apply Filter.mem_of_superset (Filter.inter_mem (hrep a).2 (hrep b).2)
    intro x hx
    exact deriv_add hx.1 hx.2
  have hzero : d 0 = 0 := by
    have h := hadd 0 0
    simpa using (add_left_cancel (show d 0 + 0 = d 0 + d 0 by simpa using h)).symm
  let F : K →+ RealUltrapower p :=
    { toFun := d, map_zero' := hzero, map_add' := hadd }
  have hmul (a b : K) : F (a * b) = a • F b + b • F a := by
    have hf : {x | DifferentiableAt ℝ (fun y => rep a y * rep b y) x} ∈ p := by
      apply Filter.mem_of_superset (Filter.inter_mem (hrep a).2 (hrep b).2)
      intro x hx
      exact hx.1.mul hx.2
    change d (a * b) = (a : RealUltrapower p) * d b + (b : RealUltrapower p) * d a
    rw [spec (a * b) (fun x => rep a x * rep b x)
      (by change classOf p (rep a) * classOf p (rep b) = _; rw [(hrep a).1, (hrep b).1]; rfl) hf,
      ← (hrep a).1, ← (hrep b).1]
    apply Filter.Germ.coe_eq.mpr
    apply Filter.mem_of_superset (Filter.inter_mem (hrep a).2 (hrep b).2)
    intro x hx
    change deriv (rep a * rep b) x =
      rep a x * deriv (rep b) x + rep b x * deriv (rep a) x
    rw [deriv_mul hx.1 hx.2]
    ring
  let D : Derivation ℤ K (RealUltrapower p) := Derivation.mk' F.toIntLinearMap hmul
  refine ⟨K, hK, hc, D, ?_⟩
  intro f hf hk
  exact spec ⟨classOf p f, hk⟩ f rfl hf

end LogicLineages.Ultrafilters
