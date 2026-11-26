import LogicLineages.PersistentMarking.HereditaryLatticeInductionProof
namespace LogicLineages.PersistentMarking.HereditaryLatticeCompleteProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode

theorem nonempty : HereditaryDomainTargets.CarrierNonempty := by
  intro E σ Γ hw
  exact ⟨(descriptor E σ).join Γ [],(HereditaryLatticeInductionProof.join E σ Γ [] hw (by simp)).1⟩

/- Classical predicate selection is confined to the mathematical arbitrary
subset existence theorem. The descriptor/enumerator/operations stay executable. -/
theorem complete : HereditaryDomainTargets.Complete := by
  classical
  intro E σ Γ hw P
  let xs := ((descriptor E σ).carriers Γ).filter (fun c => decide (P c))
  have hm : ∀ c, c ∈ xs ↔ c ∈ (descriptor E σ).carriers Γ ∧ P c := by
    intro c; simp only [xs,List.mem_filter,decide_eq_true_eq]
  have hc : ∀ c, c ∈ xs → c ∈ (descriptor E σ).carriers Γ := fun c h => ((hm c).mp h).1
  have hj := HereditaryLatticeInductionProof.join E σ Γ xs hw hc
  have hi := HereditaryLatticeInductionProof.meet E σ Γ xs hw hc
  refine ⟨(descriptor E σ).join Γ xs,(descriptor E σ).meet Γ xs,hj.1,hi.1,?_,?_,?_⟩
  · intro c hc hp
    exact ⟨hj.2.1 c ((hm c).mpr ⟨hc,hp⟩),hi.2.1 c ((hm c).mpr ⟨hc,hp⟩)⟩
  · intro b hb h
    apply hj.2.2 b hb
    intro c hx
    exact h c ((hm c).mp hx).1 ((hm c).mp hx).2
  · intro b hb h
    apply hi.2.2 b hb
    intro c hx
    exact h c ((hm c).mp hx).1 ((hm c).mp hx).2
end LogicLineages.PersistentMarking.HereditaryLatticeCompleteProof
