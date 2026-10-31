module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponentsTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.Proof

theorem fiberReachability : Targets.FiberReachability := by
  intro V I G c hc v w
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hc.noCross _ _ h).trans ih
  · intro he
    let v' : {x : V // c x = c v} := ⟨v, rfl⟩
    let w' : {x : V // c x = c v} := ⟨w, he.symm⟩
    exact ((hc.connected (c v)) v' w').map (SimpleGraph.Embedding.induce {x | c x = c v}).toHom

theorem fiberIsoRecovery : Targets.FiberIsoRecovery := by
  classical
  intro V W I J G H c d hc hd f
  let rep : I → V := fun i => Classical.choose (hc.onto i)
  have hrep : ∀ i, c (rep i) = i := fun i => Classical.choose_spec (hc.onto i)
  let p : I → J := fun i => d (f (rep i))
  have halign : ∀ v, d (f v) = p (c v) := by
    intro v
    have hr : G.Reachable (rep (c v)) v :=
      (fiberReachability V I G c hc _ _).mpr (hrep (c v))
    exact ((fiberReachability W J H d hd _ _).mp (hr.map f.toHom)).symm
  have hinj : Function.Injective p := by
    intro i j hij
    have hr : H.Reachable (f (rep i)) (f (rep j)) :=
      (fiberReachability W J H d hd _ _).mpr hij
    have hg : G.Reachable (rep i) (rep j) := f.reachable_iff.mp hr
    have he := (fiberReachability V I G c hc _ _).mp hg
    simpa only [hrep] using he
  have hsurj : Function.Surjective p := by
    intro j
    obtain ⟨w, hw⟩ := hd.onto j
    refine ⟨c (f.symm w), ?_⟩
    rw [← halign]
    simpa only [f.apply_symm_apply] using hw
  let e : I ≃ J := Equiv.ofBijective p ⟨hinj, hsurj⟩
  refine ⟨e, halign, ?_⟩
  intro i
  have hb : Set.BijOn f {v | c v = i} {w | d w = e i} := by
    refine ⟨?_, f.injective.injOn, ?_⟩
    · intro v hv
      change d (f v) = e i
      rw [halign, hv]
      rfl
    · intro w hw
      change d w = p i at hw
      refine ⟨f.symm w, ?_, f.apply_symm_apply w⟩
      change c (f.symm w) = i
      apply e.injective
      change p (c (f.symm w)) = p i
      rw [← halign]
      simpa only [f.apply_symm_apply] using hw
  exact ⟨f.induce hb⟩

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationComponents.Proof
