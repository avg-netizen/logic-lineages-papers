module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerFiniteTreeTargets
public import LogicLineages.ModelsAlgebra.PGroups.WalkerAdjunctionProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

private theorem digit_sum_step (p : ℕ) (parent : WalkerParentSequence) (n : ℕ)
    (d : Fin (n+1) → Fin p) :
    walkerFiniteDigitSum p parent (n+1) d =
      walkerAdjunctionClass p ((parent n).elim 0 (walkerFinitePresentation p parent n).generator)
        (walkerFiniteDigitSum p parent n (fun i => d i.castSucc)) (d (Fin.last n)).val := by
  let S := walkerFinitePresentation p parent n
  let a := (parent n).elim 0 S.generator
  let q := QuotientAddGroup.mk' (walkerAdjunctionRelations p a)
  change (∑ i, (d i).val • (walkerFiniteExtension p S (parent n)).generator i) = _
  rw [Fin.sum_univ_castSucc]
  simp only [walkerFiniteExtension, Fin.lastCases_castSucc, Fin.lastCases_last]
  change (∑ i : Fin n, (d i.castSucc).val • q (S.generator i, 0)) +
    (d (Fin.last n)).val • q (0,1) = q (∑ i, (d i.castSucc).val • S.generator i,
      ((d (Fin.last n)).val : ℤ))
  simp only [← map_nsmul, ← map_sum, ← map_add]
  congr 1
  ext <;> simp
  · exact map_sum (AddMonoidHom.fst S.Carrier ℤ) _ _
  · change (AddMonoidHom.snd S.Carrier ℤ) (∑ i : Fin n,
      ((d i.castSucc).val • S.generator i, (0 : ℤ))) = 0
    rw [map_sum]
    simp

private theorem digit_pair_injective {H : Type} [AddCommGroup H] (p : ℕ) (hp : 0 < p)
    (a : H) {h k : H} {r s : Fin p}
    (he : walkerAdjunctionClass p a h r.val = walkerAdjunctionClass p a k s.val) :
    h = k ∧ r = s := by
  obtain ⟨d, hd, hu⟩ := walker_adjunction_unique_digits H p hp a
    (walkerAdjunctionClass p a k s.val)
  have hr := hu (h, (r.val : ℤ)) ⟨by omega, by dsimp; exact_mod_cast r.isLt, he⟩
  have hs := hu (k, (s.val : ℤ)) ⟨by omega, by dsimp; exact_mod_cast s.isLt, rfl⟩
  have heq := hr.trans hs.symm
  constructor
  · exact congrArg Prod.fst heq
  · apply Fin.ext
    have hh := congrArg Prod.snd heq
    dsimp at hh
    exact_mod_cast hh

theorem walker_finite_tree_unique_digits : Targets.walkerFiniteTreeUniqueDigits := by
  intro p hp parent n
  induction n with
  | zero =>
    constructor
    · intro d e _
      funext i
      exact Fin.elim0 i
    · intro x
      refine ⟨Fin.elim0, ?_⟩
      change (PUnit.unit : PUnit) = x
      exact Subsingleton.elim _ _
  | succ n ih =>
    constructor
    · intro d e he
      rw [digit_sum_step, digit_sum_step] at he
      obtain ⟨hprev, hlast⟩ := digit_pair_injective p hp _ he
      have hds := ih.1 hprev
      funext i
      exact Fin.lastCases hlast (fun j => congrFun hds j) i
    · intro x
      obtain ⟨⟨h,r⟩, hr, _⟩ := walker_adjunction_unique_digits
        (walkerFinitePresentation p parent n).Carrier p hp
        ((parent n).elim 0 (walkerFinitePresentation p parent n).generator) x
      obtain ⟨d, hd⟩ := ih.2 h
      let s : Fin p := ⟨r.toNat, by omega⟩
      refine ⟨Fin.lastCases s d, ?_⟩
      rw [digit_sum_step]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
      rw [hd]
      change walkerAdjunctionClass p _ h (r.toNat : ℤ) = x
      rw [Int.toNat_of_nonneg hr.1]
      exact hr.2.2

theorem walker_finite_tree_relations : Targets.walkerFiniteTreeRelations := by
  intro p parent n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [walkerFinitePresentation, walkerFiniteExtension, Fin.lastCases_last, Fin.val_last]
      erw [walker_adjunction_root_relation]
      let a := (parent n).elim 0 (walkerFinitePresentation p parent n).generator
      change walkerAdjunctionClass p a a 0 = (parent n).elim 0 (fun j =>
        Fin.lastCases (walkerAdjunctionClass p a 0 1)
          (fun k => walkerAdjunctionClass p a
            ((walkerFinitePresentation p parent n).generator k) 0) j.castSucc)
      simp only [Fin.lastCases_castSucc]
      have ho (o : Option (Fin n)) :
          walkerAdjunctionClass p a (o.elim 0 (walkerFinitePresentation p parent n).generator) 0 =
            o.elim 0 (fun j => walkerAdjunctionClass p a
              ((walkerFinitePresentation p parent n).generator j) 0) := by
        cases o <;> rfl
      exact ho (parent n)
    · have hj := ih j
      let a := (parent n).elim 0 (walkerFinitePresentation p parent n).generator
      let f : (walkerFinitePresentation p parent n).Carrier →+
          (walkerFinitePresentation p parent (n+1)).Carrier :=
        { toFun := fun x => walkerAdjunctionClass p a x 0
          map_zero' := rfl
          map_add' := fun _ _ => rfl }
      have hh := congrArg f hj
      rw [map_nsmul] at hh
      change p • walkerAdjunctionClass p a ((walkerFinitePresentation p parent n).generator j) 0 =
        walkerAdjunctionClass p a ((parent j.val).elim 0 (fun k =>
          (walkerFinitePresentation p parent n).generator ⟨k.val, lt_trans k.isLt j.isLt⟩)) 0 at hh
      cases h : parent j.val with
      | none =>
        simp only [h, Option.elim_none] at hh
        have hz : walkerAdjunctionClass p a 0 0 = 0 := rfl
        rw [hz] at hh
        simp only [walkerFinitePresentation, walkerFiniteExtension, Fin.lastCases_castSucc,
          Fin.val_castSucc, h, Option.elim_none]
        exact hh
      | some k =>
        have hk : (⟨k.val, lt_trans k.isLt j.isLt⟩ : Fin n).castSucc =
            (⟨k.val, lt_trans k.isLt j.castSucc.isLt⟩ : Fin (n+1)) := rfl
        simp only [h, Option.elim_some] at hh
        simp only [walkerFinitePresentation, walkerFiniteExtension, Fin.lastCases_castSucc,
          Fin.val_castSucc, h, Option.elim_some]
        rw [← hk, Fin.lastCases_castSucc]
        exact hh

end LogicLineages.ModelsAlgebra.PGroups
