module

public import LogicLineages.Ultrafilters.DomainSubfieldTargets
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section
namespace LogicLineages.Ultrafilters

theorem constant_mem_domain (p : Ultrafilter ℝ) (r : ℝ) :
    constantClass p r ∈ differentiationDomain p := by
  exact ⟨fun _ => r, rfl, Filter.Eventually.of_forall (fun _ => differentiableAt_const r)⟩

theorem domain_subfield : Targets.DomainSubfield := by
  intro p hp
  let K : Subfield (RealUltrapower p) :=
    { carrier := differentiationDomain p
      zero_mem' := constant_mem_domain p 0
      one_mem' := constant_mem_domain p 1
      add_mem' := by
        rintro a b ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
        refine ⟨fun x => f x + g x, rfl, ?_⟩
        apply Filter.mem_of_superset (Filter.inter_mem hf hg)
        intro x hx
        exact hx.1.add hx.2
      neg_mem' := by
        rintro a ⟨f, rfl, hf⟩
        refine ⟨fun x => -f x, rfl, ?_⟩
        apply Filter.mem_of_superset hf
        intro x hx
        exact hx.neg
      mul_mem' := by
        rintro a b ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩
        refine ⟨fun x => f x * g x, rfl, ?_⟩
        apply Filter.mem_of_superset (Filter.inter_mem hf hg)
        intro x hx
        exact hx.1.mul hx.2
      inv_mem' := by
        intro a ha
        by_cases hz : a = 0
        · rw [hz, inv_zero]
          exact constant_mem_domain p 0
        rcases ha with ⟨f, rfl, hf⟩
        have hn : {x | f x ≠ 0} ∈ p := by
          apply Ultrafilter.compl_mem_iff_notMem.mpr
          intro he
          apply hz
          exact Filter.Germ.coe_eq.mpr he
        refine ⟨fun x => (f x)⁻¹, rfl, ?_⟩
        apply Filter.mem_of_superset (Filter.inter_mem hf hn)
        intro x hx
        exact hx.1.inv hx.2 }
  exact ⟨K, rfl, constant_mem_domain p⟩

end LogicLineages.Ultrafilters
