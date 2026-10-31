module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerRealizationTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerEnumerationProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalProof
public import LogicLineages.ModelsAlgebra.PGroups.WalkerSubtreeDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem option_transport {I V K : Type} (o : Option I) (e : I → V) (y : V → K) (z : K) :
    (o.map e).elim z y = o.elim z (fun i => y (e i)) := by cases o <;> rfl

/-- Internal comparison of two proved presentation universal properties.
Both properties are paid by concrete quotient/direct-limit theorems below. -/
private theorem identify_presentation (I V X : Type) [AddCommGroup X] (p : ℕ)
    (P : I → Option I) (Q : V → Option V) (e : I ≃ V) (gen : I → X)
    (hP : ∀ i, Q (e i) = (P i).map e)
    (hrel : ∀ i, p • gen i = (P i).elim 0 gen)
    (hu : ∀ (K : Type) [AddCommGroup K] (y : I → K),
      (∀ i, p • y i = (P i).elim 0 y) → ∃! f : X →+ K, ∀ i, f (gen i) = y i) :
    ∃ E : WalkerPresentedGroup p Q ≃+ X,
      ∀ i, E (walkerPresentedGenerator p Q (e i)) = gen i := by
  have hy : ∀ v, p • gen (e.symm v) = (Q v).elim 0 (fun v => gen (e.symm v)) := by
    intro v
    obtain ⟨i, rfl⟩ := e.surjective v
    rw [hP i, option_transport]
    simpa only [e.symm_apply_apply] using hrel i
  obtain ⟨f, hf, _⟩ := walker_presented_universal V p Q X (fun v => gen (e.symm v)) hy
  have hz : ∀ i, p • walkerPresentedGenerator p Q (e i) =
      (P i).elim 0 (fun i => walkerPresentedGenerator p Q (e i)) := by
    intro i
    rw [walker_presented_relations V p Q (e i), hP i, option_transport]
  obtain ⟨g, hg, _⟩ := hu (WalkerPresentedGroup p Q) (fun i => walkerPresentedGenerator p Q (e i)) hz
  have hgf : g.comp f = AddMonoidHom.id _ := by
    apply walker_presented_hom_ext V p Q (WalkerPresentedGroup p Q)
    intro v
    obtain ⟨i, rfl⟩ := e.surjective v
    change g (f (walkerPresentedGenerator p Q (e i))) = walkerPresentedGenerator p Q (e i)
    rw [hf, e.symm_apply_apply, hg]
  obtain ⟨u, _, huniq⟩ := hu X gen hrel
  have hfg : f.comp g = AddMonoidHom.id _ := by
    apply Eq.trans (huniq (f.comp g) ?_) (huniq (AddMonoidHom.id _) (fun _ => rfl)).symm
    intro i
    change f (g (gen i)) = gen i
    rw [hg, hf, e.symm_apply_apply]
  let E : WalkerPresentedGroup p Q ≃+ X :=
    { toFun := f
      invFun := g
      left_inv := fun x => congrArg (fun k => k x) hgf
      right_inv := fun x => congrArg (fun k => k x) hfg
      map_add' := f.map_add }
  refine ⟨E, ?_⟩
  intro i
  exact (hf (e i)).trans (congrArg gen (e.symm_apply_apply i))

theorem walker_source_realization : Targets.walkerSourceRealization := by
  classical
  intro p hp ξ _
  rcases walker_ordinal_enumeration ξ with ⟨n, e, _, he⟩ | ⟨e, _, he⟩
  · let parent := walkerFiniteOrdinalParent ξ n e he
    let P := walkerParentNode parent n
    have hP (i : Fin n) : walkerOrdinalParent ξ (e i) = (P i).map e := by
      simp only [P, walkerParentNode, parent, walkerFiniteOrdinalParent, dif_pos i.isLt]
      split <;> simp_all
    have hrel (i : Fin n) : p • (walkerFinitePresentation p parent n).generator i =
        (P i).elim 0 (walkerFinitePresentation p parent n).generator := by
      simpa only [P, walkerParentNode, option_transport] using walker_finite_tree_relations p parent n i
    have hu (K : Type) [AddCommGroup K] (y : Fin n → K)
        (hy : ∀ i, p • y i = (P i).elim 0 y) :
        ∃! f : (walkerFinitePresentation p parent n).Carrier →+ K,
          ∀ i, f ((walkerFinitePresentation p parent n).generator i) = y i := by
      apply walker_finite_universal p hp parent n K y
      intro i
      simpa only [P, walkerParentNode, option_transport] using hy i
    obtain ⟨E, hE⟩ := identify_presentation (Fin n) (WalkerOrdinalNode ξ)
      (walkerFinitePresentation p parent n).Carrier p P (walkerOrdinalParent ξ) e
      (walkerFinitePresentation p parent n).generator hP hrel hu
    exact Or.inl ⟨n, e, he, E, hE⟩
  · let parent := walkerInfiniteOrdinalParent ξ e he
    let P : ℕ → Option ℕ := fun i => (parent i).map Fin.val
    have hP (i : ℕ) : walkerOrdinalParent ξ (e i) = (P i).map e := by
      simp only [P, parent, walkerInfiniteOrdinalParent]
      split <;> simp_all
    have hrel (i : ℕ) : p • walkerSequentialGenerator p parent i =
        (P i).elim 0 (walkerSequentialGenerator p parent) := by
      simpa only [P, option_transport] using walker_limit_relations p parent i
    have hu (K : Type) [AddCommGroup K] (y : ℕ → K)
        (hy : ∀ i, p • y i = (P i).elim 0 y) :
        ∃! f : WalkerSequentialGroup p parent →+ K,
          ∀ i, f (walkerSequentialGenerator p parent i) = y i := by
      apply walker_limit_universal p hp parent K y
      intro i
      simpa only [P, option_transport] using hy i
    obtain ⟨E, hE⟩ := identify_presentation ℕ (WalkerOrdinalNode ξ)
      (WalkerSequentialGroup p parent) p P (walkerOrdinalParent ξ) e
      (walkerSequentialGenerator p parent) hP hrel hu
    exact Or.inr ⟨e, he, E, hE⟩

end LogicLineages.ModelsAlgebra.PGroups
