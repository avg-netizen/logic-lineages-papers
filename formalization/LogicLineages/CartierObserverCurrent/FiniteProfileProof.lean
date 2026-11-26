module
public import LogicLineages.CartierObserverCurrent.FiniteProfileTargets
public import LogicLineages.CartierObserverCurrent.GeometricStateProof
public import LogicLineages.CartierObserverCurrent.ProfileDescentProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FiniteProfile
open SplittingRoots

theorem actualFiniteProfile : Targets.ActualFiniteProfile := by
  intro d
  letI : Finite (Root d) := (finiteFieldAndRoots d).2
  unfold Profile
  infer_instance

theorem actualGeometricBijection : Targets.ActualGeometricBijection := by
  intro d
  classical
  let hs (g : State d) : ProfileDescent.baseState d g.val :=
    (GeometricState.actualBaseEquivalence d g.val).mpr g.property
  let F : State d → Profile d := fun g =>
    ⟨Classical.choose (ProfileDescent.baseToProfile d g.val (hs g)),
      (Classical.choose_spec (ProfileDescent.baseToProfile d g.val (hs g))).1.1⟩
  have hF (g : State d) : RationalCoverage.reconstruct d (F g).val = ProfileDescent.extend d g.val :=
    (Classical.choose_spec (ProfileDescent.baseToProfile d g.val (hs g))).1.2
  have hi : Function.Injective F := by
    intro a b h
    apply Subtype.ext
    apply (ProfileDescent.extend d).injective
    have hh := congrArg (fun p : Profile d => RationalCoverage.reconstruct d p.val) h
    rw [hF a, hF b] at hh
    exact hh
  have hu : Function.Surjective F := by
    intro b
    obtain ⟨g, ⟨hg, he⟩, _⟩ := (ProfileDescent.profileToBase d b.val).mp b.property
    let a : State d := ⟨g, (GeometricState.actualBaseEquivalence d g).mp hg⟩
    refine ⟨a, Subtype.ext ?_⟩
    exact RationalCoverage.reconstructionInjective d ((hF a).trans he)
  exact ⟨Equiv.ofBijective F ⟨hi, hu⟩, fun g => (hF g).symm⟩

theorem actualFiniteState : Targets.ActualFiniteState := by
  intro d
  letI : Finite (Profile d) := actualFiniteProfile d
  obtain ⟨e, _⟩ := actualGeometricBijection d
  exact Finite.of_injective e e.injective

#audit_namespace LogicLineages.CartierObserverCurrent.FiniteProfile
end LogicLineages.CartierObserverCurrent.FiniteProfile
