module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUniversalTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem root_extension_map {H K : Type} [AddCommGroup H] [AddCommGroup K]
    (p : ℕ) (a : H) (f : H →+ K) (b : K) (hb : p • b = f a) :
    ∃ g : WalkerAdjunction p a →+ K,
      (∀ h, g (walkerAdjunctionClass p a h 0) = f h) ∧
      g (walkerAdjunctionClass p a 0 1) = b := by
  let φ : H × ℤ →+ K :=
    { toFun := fun x => f x.1 + x.2 • b
      map_zero' := by simp
      map_add' := by intro x y; simp [map_add, add_zsmul, add_assoc, add_left_comm, add_comm] }
  have hk : walkerAdjunctionRelations p a ≤ φ.ker := by
    intro x hx
    obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    change φ (m • (-a, (p : ℤ))) = 0
    rw [map_zsmul]
    have hzero : φ (-a, (p : ℤ)) = 0 := by simp [φ, hb]
    rw [hzero]
    exact zsmul_zero m
  refine ⟨QuotientAddGroup.lift (walkerAdjunctionRelations p a) φ hk, ?_, ?_⟩
  · intro h
    change f h + (0 : ℤ) • b = f h
    simp
  · change f 0 + (1 : ℤ) • b = b
    simp

private theorem finite_map_exists (p : ℕ) (parent : WalkerParentSequence) (n : ℕ)
    (K : Type) [AddCommGroup K] (y : Fin n → K)
    (hy : WalkerAssignmentRelations p parent n y) :
    ∃ f : (walkerFinitePresentation p parent n).Carrier →+ K,
      ∀ i, f ((walkerFinitePresentation p parent n).generator i) = y i := by
  induction n with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hy0 : WalkerAssignmentRelations p parent n (fun j => y j.castSucc) := by
      intro j
      exact hy j.castSucc
    obtain ⟨f, hf⟩ := ih (fun j => y j.castSucc) hy0
    let a := (parent n).elim 0 (walkerFinitePresentation p parent n).generator
    have ha : f a = (parent n).elim 0 (fun j => y j.castSucc) := by
      have ho (o : Option (Fin n)) :
          f (o.elim 0 (walkerFinitePresentation p parent n).generator) =
            o.elim 0 (fun j => y j.castSucc) := by
        cases o with
        | none => exact map_zero f
        | some j => exact hf j
      exact ho (parent n)
    have hb : p • y (Fin.last n) = f a := by
      rw [ha]
      exact hy (Fin.last n)
    obtain ⟨g, hg, hlast⟩ := root_extension_map p a f (y (Fin.last n)) hb
    refine ⟨g, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [walkerFinitePresentation, walkerFiniteExtension, Fin.lastCases_last]
      exact hlast
    · simp only [walkerFinitePresentation, walkerFiniteExtension, Fin.lastCases_castSucc]
      exact (hg _).trans (hf j)

theorem walker_finite_universal : Targets.walkerFiniteUniversal := by
  intro p hp parent n K _ y hy
  obtain ⟨f, hf⟩ := finite_map_exists p parent n K y hy
  refine ⟨f, hf, ?_⟩
  intro g hg
  apply AddMonoidHom.ext
  intro x
  obtain ⟨d, rfl⟩ := (walker_finite_tree_unique_digits p hp parent n).2 x
  simp only [walkerFiniteDigitSum, map_sum, map_nsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hg i, hf i]

end LogicLineages.ModelsAlgebra.PGroups
